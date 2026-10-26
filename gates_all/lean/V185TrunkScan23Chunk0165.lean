import V185TrunkScan23Chunk0164

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_976131 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 4]
def baseStart_976131 : Nat := 118140960795 + 976131 * 2 ^ 59
def prefixEnd_976131 : Nat := 4983230072969 + 3 ^ 40 * 976131 * 2
def baseEnd_976131 : Nat := 501224384754025616673361

theorem tailTrace_976131 : CollatzResearch.WordTrace tailWord_976131 prefixEnd_976131 501224384754025616673361 := by
  unfold tailWord_976131
  simp only [CollatzResearch.WordTrace]
  refine ⟨35602422426651571747456247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23734948284434381164970831 35602422426651571747456247)
  ·
    refine ⟨53403633639977357621184371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35602422426651571747456247 53403633639977357621184371)
    ·
      refine ⟨80105450459966036431776557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53403633639977357621184371 80105450459966036431776557)
      ·
        refine ⟨30039543922487263661916209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80105450459966036431776557 30039543922487263661916209)
        ·
          refine ⟨22529657941865447746437157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30039543922487263661916209 22529657941865447746437157)
          ·
            refine ⟨4224310864099771452456967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22529657941865447746437157 4224310864099771452456967)
            ·
              refine ⟨6336466296149657178685451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4224310864099771452456967 6336466296149657178685451)
              ·
                refine ⟨9504699444224485768028177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6336466296149657178685451 9504699444224485768028177)
                ·
                  refine ⟨7128524583168364326021133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9504699444224485768028177 7128524583168364326021133)
                  ·
                    refine ⟨2673196718688136622257925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7128524583168364326021133 2673196718688136622257925)
                    ·
                      refine ⟨501224384754025616673361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2673196718688136622257925 501224384754025616673361)
                      ·
                        rfl

theorem cell23_976131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_976131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976131 prefixEnd_976131 := by exact prefixLift 976131
  have htrace : WordTrace (prefixWord ++ tailWord_976131) baseStart_976131 baseEnd_976131 := by
    simpa [prefixWord, tailWord_976131, baseEnd_976131] using wordTrace_append hprefix tailTrace_976131
  have hstable : (prefixWord ++ tailWord_976131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976131).length < 2 ^ (prefixWord ++ tailWord_976131).sum := by decide
  have hdescent : baseEnd_976131 < baseStart_976131 := by decide
  rcases family_descends (prefixWord ++ tailWord_976131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976161 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_976161 : Nat := 118140960795 + 976161 * 2 ^ 59
def prefixEnd_976161 : Nat := 4983230072969 + 3 ^ 40 * 976161 * 2
def baseEnd_976161 : Nat := 501239789173660499298223

theorem tailTrace_976161 : CollatzResearch.WordTrace tailWord_976161 prefixEnd_976161 501239789173660499298223 := by
  unfold tailWord_976161
  simp only [CollatzResearch.WordTrace]
  refine ⟨35603516616542886871048337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23735677744361924580698891 35603516616542886871048337)
  ·
    refine ⟨26702637462407165153286253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35603516616542886871048337 26702637462407165153286253)
    ·
      refine ⟨10013489048402686932482345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26702637462407165153286253 10013489048402686932482345)
      ·
        refine ⟨7510116786302015199361759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10013489048402686932482345 7510116786302015199361759)
        ·
          refine ⟨11265175179453022799042639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7510116786302015199361759 11265175179453022799042639)
          ·
            refine ⟨16897762769179534198563959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11265175179453022799042639 16897762769179534198563959)
            ·
              refine ⟨25346644153769301297845939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16897762769179534198563959 25346644153769301297845939)
              ·
                refine ⟨38019966230653951946768909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25346644153769301297845939 38019966230653951946768909)
                ·
                  refine ⟨14257487336495231980038341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38019966230653951946768909 14257487336495231980038341)
                  ·
                    refine ⟨2673278875592855996257189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14257487336495231980038341 2673278875592855996257189)
                    ·
                      refine ⟨501239789173660499298223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2673278875592855996257189 501239789173660499298223)
                      ·
                        rfl

theorem cell23_976161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_976161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976161 prefixEnd_976161 := by exact prefixLift 976161
  have htrace : WordTrace (prefixWord ++ tailWord_976161) baseStart_976161 baseEnd_976161 := by
    simpa [prefixWord, tailWord_976161, baseEnd_976161] using wordTrace_append hprefix tailTrace_976161
  have hstable : (prefixWord ++ tailWord_976161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976161).length < 2 ^ (prefixWord ++ tailWord_976161).sum := by decide
  have hdescent : baseEnd_976161 < baseStart_976161 := by decide
  rcases family_descends (prefixWord ++ tailWord_976161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976165 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 1, 4, 2]
def baseStart_976165 : Nat := 118140960795 + 976165 * 2 ^ 59
def prefixEnd_976165 : Nat := 4983230072969 + 3 ^ 40 * 976165 * 2
def baseEnd_976165 : Nat := 501241843096278483648205

theorem tailTrace_976165 : CollatzResearch.WordTrace tailWord_976165 prefixEnd_976165 501241843096278483648205 := by
  unfold tailWord_976165
  simp only [CollatzResearch.WordTrace]
  refine ⟨35603662508528395554193949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23735775005685597036129299 35603662508528395554193949)
  ·
    refine ⟨13351373440698148332822731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35603662508528395554193949 13351373440698148332822731)
    ·
      refine ⟨20027060161047222499234097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13351373440698148332822731 20027060161047222499234097)
      ·
        refine ⟨15020295120785416874425573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20027060161047222499234097 15020295120785416874425573)
        ·
          refine ⟨2816305335147265663954795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15020295120785416874425573 2816305335147265663954795)
          ·
            refine ⟨4224458002720898495932193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816305335147265663954795 4224458002720898495932193)
            ·
              refine ⟨3168343502040673871949145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4224458002720898495932193 3168343502040673871949145)
              ·
                refine ⟨2376257626530505403961859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3168343502040673871949145 2376257626530505403961859)
                ·
                  refine ⟨3564386439795758105942789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376257626530505403961859 3564386439795758105942789)
                  ·
                    refine ⟨668322457461704644864273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3564386439795758105942789 668322457461704644864273)
                    ·
                      refine ⟨501241843096278483648205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668322457461704644864273 501241843096278483648205)
                      ·
                        rfl

theorem cell23_976165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_976165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976165 prefixEnd_976165 := by exact prefixLift 976165
  have htrace : WordTrace (prefixWord ++ tailWord_976165) baseStart_976165 baseEnd_976165 := by
    simpa [prefixWord, tailWord_976165, baseEnd_976165] using wordTrace_append hprefix tailTrace_976165
  have hstable : (prefixWord ++ tailWord_976165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976165).length < 2 ^ (prefixWord ++ tailWord_976165).sum := by decide
  have hdescent : baseEnd_976165 < baseStart_976165 := by decide
  rcases family_descends (prefixWord ++ tailWord_976165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976178 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_976178 : Nat := 118140960795 + 976178 * 2 ^ 59
def prefixEnd_976178 : Nat := 4983230072969 + 3 ^ 40 * 976178 * 2
def baseEnd_976178 : Nat := 501248518344786932785645

theorem tailTrace_976178 : CollatzResearch.WordTrace tailWord_976178 prefixEnd_976178 501248518344786932785645 := by
  unfold tailWord_976178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8901034164370324693604297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23736091104987532516278125 8901034164370324693604297)
  ·
    refine ⟨6675775623277743520203223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8901034164370324693604297 6675775623277743520203223)
    ·
      refine ⟨10013663434916615280304835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6675775623277743520203223 10013663434916615280304835)
      ·
        refine ⟨15020495152374922920457253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10013663434916615280304835 15020495152374922920457253)
        ·
          refine ⟨2816342841070298047585735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15020495152374922920457253 2816342841070298047585735)
          ·
            refine ⟨4224514261605447071378603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816342841070298047585735 4224514261605447071378603)
            ·
              refine ⟨6336771392408170607067905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4224514261605447071378603 6336771392408170607067905)
              ·
                refine ⟨4752578544306127955300929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6336771392408170607067905 4752578544306127955300929)
                ·
                  refine ⟨3564433908229595966475697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4752578544306127955300929 3564433908229595966475697)
                  ·
                    refine ⟨2673325431172196974856773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3564433908229595966475697 2673325431172196974856773)
                    ·
                      refine ⟨501248518344786932785645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2673325431172196974856773 501248518344786932785645)
                      ·
                        rfl

theorem cell23_976178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_976178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976178 prefixEnd_976178 := by exact prefixLift 976178
  have htrace : WordTrace (prefixWord ++ tailWord_976178) baseStart_976178 baseEnd_976178 := by
    simpa [prefixWord, tailWord_976178, baseEnd_976178] using wordTrace_append hprefix tailTrace_976178
  have hstable : (prefixWord ++ tailWord_976178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976178).length < 2 ^ (prefixWord ++ tailWord_976178).sum := by decide
  have hdescent : baseEnd_976178 < baseStart_976178 := by decide
  rcases family_descends (prefixWord ++ tailWord_976178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976188 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 7]
def baseStart_976188 : Nat := 118140960795 + 976188 * 2 ^ 59
def prefixEnd_976188 : Nat := 4983230072969 + 3 ^ 40 * 976188 * 2
def baseEnd_976188 : Nat := 55694850350147988184511

theorem tailTrace_976188 : CollatzResearch.WordTrace tailWord_976188 prefixEnd_976188 55694850350147988184511 := by
  unfold tailWord_976188
  simp only [CollatzResearch.WordTrace]
  refine ⟨17802250693722535241140609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23736334258296713654854145 17802250693722535241140609)
  ·
    refine ⟨13351688020291901430855457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17802250693722535241140609 13351688020291901430855457)
    ·
      refine ⟨10013766015218926073141593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13351688020291901430855457 10013766015218926073141593)
      ·
        refine ⟨7510324511414194554856195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10013766015218926073141593 7510324511414194554856195)
        ·
          refine ⟨11265486767121291832284293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7510324511414194554856195 11265486767121291832284293)
          ·
            refine ⟨2112278768835242218553305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11265486767121291832284293 2112278768835242218553305)
            ·
              refine ⟨1584209076626431663914979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2112278768835242218553305 1584209076626431663914979)
              ·
                refine ⟨2376313614939647495872469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584209076626431663914979 2376313614939647495872469)
                ·
                  refine ⟨55694850350147988184511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2376313614939647495872469 55694850350147988184511)
                  ·
                    rfl

theorem cell23_976188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 7].length) (baseStart_976188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976188 prefixEnd_976188 := by exact prefixLift 976188
  have htrace : WordTrace (prefixWord ++ tailWord_976188) baseStart_976188 baseEnd_976188 := by
    simpa [prefixWord, tailWord_976188, baseEnd_976188] using wordTrace_append hprefix tailTrace_976188
  have hstable : (prefixWord ++ tailWord_976188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976188).length < 2 ^ (prefixWord ++ tailWord_976188).sum := by decide
  have hdescent : baseEnd_976188 < baseStart_976188 := by decide
  rcases family_descends (prefixWord ++ tailWord_976188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976199 : List Nat := [1, 1, 4, 1, 2, 4, 3, 1, 2, 2, 2]
def baseStart_976199 : Nat := 118140960795 + 976199 * 2 ^ 59
def prefixEnd_976199 : Nat := 4983230072969 + 3 ^ 40 * 976199 * 2
def baseEnd_976199 : Nat := 501259301438531350623049

theorem tailTrace_976199 : CollatzResearch.WordTrace tailWord_976199 prefixEnd_976199 501259301438531350623049 := by
  unfold tailWord_976199
  simp only [CollatzResearch.WordTrace]
  refine ⟨35604902590405219360931651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23736601726936812907287767 35604902590405219360931651)
  ·
    refine ⟨53407353885607829041397477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35604902590405219360931651 53407353885607829041397477)
    ·
      refine ⟨10013878853551467945262027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53407353885607829041397477 10013878853551467945262027)
      ·
        refine ⟨15020818280327201917893041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10013878853551467945262027 15020818280327201917893041)
        ·
          refine ⟨11265613710245401438419781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15020818280327201917893041 11265613710245401438419781)
          ·
            refine ⟨2112302570671012769703709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11265613710245401438419781 2112302570671012769703709)
            ·
              refine ⟨792113464001629788638891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2112302570671012769703709 792113464001629788638891)
              ·
                refine ⟨1188170196002444682958337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792113464001629788638891 1188170196002444682958337)
                ·
                  refine ⟨891127647001833512218753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1188170196002444682958337 891127647001833512218753)
                  ·
                    refine ⟨668345735251375134164065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 891127647001833512218753 668345735251375134164065)
                    ·
                      refine ⟨501259301438531350623049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668345735251375134164065 501259301438531350623049)
                      ·
                        rfl

theorem cell23_976199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_976199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976199 prefixEnd_976199 := by exact prefixLift 976199
  have htrace : WordTrace (prefixWord ++ tailWord_976199) baseStart_976199 baseEnd_976199 := by
    simpa [prefixWord, tailWord_976199, baseEnd_976199] using wordTrace_append hprefix tailTrace_976199
  have hstable : (prefixWord ++ tailWord_976199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976199).length < 2 ^ (prefixWord ++ tailWord_976199).sum := by decide
  have hdescent : baseEnd_976199 < baseStart_976199 := by decide
  rcases family_descends (prefixWord ++ tailWord_976199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976201 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 1, 7]
def baseStart_976201 : Nat := 118140960795 + 976201 * 2 ^ 59
def prefixEnd_976201 : Nat := 4983230072969 + 3 ^ 40 * 976201 * 2
def baseEnd_976201 : Nat := 167086776133280114266013

theorem tailTrace_976201 : CollatzResearch.WordTrace tailWord_976201 prefixEnd_976201 167086776133280114266013 := by
  unfold tailWord_976201
  simp only [CollatzResearch.WordTrace]
  refine ⟨35604975536397973702504457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23736650357598649135002971 35604975536397973702504457)
  ·
    refine ⟨26703731652298480276878343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35604975536397973702504457 26703731652298480276878343)
    ·
      refine ⟨40055597478447720415317515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26703731652298480276878343 40055597478447720415317515)
      ·
        refine ⟨60083396217671580622976273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40055597478447720415317515 60083396217671580622976273)
        ·
          refine ⟨45062547163253685467232205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60083396217671580622976273 45062547163253685467232205)
          ·
            refine ⟨16898455186220132050212077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45062547163253685467232205 16898455186220132050212077)
            ·
              refine ⟨6336920694832549518829529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16898455186220132050212077 6336920694832549518829529)
              ·
                refine ⟨4752690521124412139122147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6336920694832549518829529 4752690521124412139122147)
                ·
                  refine ⟨7129035781686618208683221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4752690521124412139122147 7129035781686618208683221)
                  ·
                    refine ⟨167086776133280114266013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7129035781686618208683221 167086776133280114266013)
                    ·
                      rfl

theorem cell23_976201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 7].length) (baseStart_976201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976201 prefixEnd_976201 := by exact prefixLift 976201
  have htrace : WordTrace (prefixWord ++ tailWord_976201) baseStart_976201 baseEnd_976201 := by
    simpa [prefixWord, tailWord_976201, baseEnd_976201] using wordTrace_append hprefix tailTrace_976201
  have hstable : (prefixWord ++ tailWord_976201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976201).length < 2 ^ (prefixWord ++ tailWord_976201).sum := by decide
  have hdescent : baseEnd_976201 < baseStart_976201 := by decide
  rcases family_descends (prefixWord ++ tailWord_976201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976245 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_976245 : Nat := 118140960795 + 976245 * 2 ^ 59
def prefixEnd_976245 : Nat := 4983230072969 + 3 ^ 40 * 976245 * 2
def baseEnd_976245 : Nat := 501282921548638170647837

theorem tailTrace_976245 : CollatzResearch.WordTrace tailWord_976245 prefixEnd_976245 501282921548638170647837 := by
  unfold tailWord_976245
  simp only [CollatzResearch.WordTrace]
  refine ⟨35606580348238569217106189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23737720232159046144737459 35606580348238569217106189)
  ·
    refine ⟨13352467630589463456414821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35606580348238569217106189 13352467630589463456414821)
    ·
      refine ⟨2503587680735524398077779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13352467630589463456414821 2503587680735524398077779)
      ·
        refine ⟨3755381521103286597116669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503587680735524398077779 3755381521103286597116669)
        ·
          refine ⟨1408268070413732473918751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3755381521103286597116669 1408268070413732473918751)
          ·
            refine ⟨2112402105620598710878127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408268070413732473918751 2112402105620598710878127)
            ·
              refine ⟨3168603158430898066317191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112402105620598710878127 3168603158430898066317191)
              ·
                refine ⟨4752904737646347099475787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168603158430898066317191 4752904737646347099475787)
                ·
                  refine ⟨7129357106469520649213681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4752904737646347099475787 7129357106469520649213681)
                  ·
                    refine ⟨5347017829852140486910261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7129357106469520649213681 5347017829852140486910261)
                    ·
                      refine ⟨501282921548638170647837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5347017829852140486910261 501282921548638170647837)
                      ·
                        rfl

theorem cell23_976245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_976245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976245 prefixEnd_976245 := by exact prefixLift 976245
  have htrace : WordTrace (prefixWord ++ tailWord_976245) baseStart_976245 baseEnd_976245 := by
    simpa [prefixWord, tailWord_976245, baseEnd_976245] using wordTrace_append hprefix tailTrace_976245
  have hstable : (prefixWord ++ tailWord_976245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976245).length < 2 ^ (prefixWord ++ tailWord_976245).sum := by decide
  have hdescent : baseEnd_976245 < baseStart_976245 := by decide
  rcases family_descends (prefixWord ++ tailWord_976245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976282 : List Nat := [3, 1, 1, 4, 1, 1, 2, 5, 1, 4]
def baseStart_976282 : Nat := 118140960795 + 976282 * 2 ^ 59
def prefixEnd_976282 : Nat := 4983230072969 + 3 ^ 40 * 976282 * 2
def baseEnd_976282 : Nat := 167100640110951508628389

theorem tailTrace_976282 : CollatzResearch.WordTrace tailWord_976282 prefixEnd_976282 167100640110951508628389 := by
  unfold tailWord_976282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8901982462276131134050775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23738619899403016357468733 8901982462276131134050775)
  ·
    refine ⟨13352973693414196701076163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8901982462276131134050775 13352973693414196701076163)
    ·
      refine ⟨20029460540121295051614245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13352973693414196701076163 20029460540121295051614245)
      ·
        refine ⟨3755523851272742822177671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20029460540121295051614245 3755523851272742822177671)
        ·
          refine ⟨5633285776909114233266507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3755523851272742822177671 5633285776909114233266507)
          ·
            refine ⟨8449928665363671349899761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5633285776909114233266507 8449928665363671349899761)
            ·
              refine ⟨6337446499022753512424821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8449928665363671349899761 6337446499022753512424821)
              ·
                refine ⟨594135609283383141789827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6337446499022753512424821 594135609283383141789827)
                ·
                  refine ⟨891203413925074712684741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594135609283383141789827 891203413925074712684741)
                  ·
                    refine ⟨167100640110951508628389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 891203413925074712684741 167100640110951508628389)
                    ·
                      rfl

theorem cell23_976282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_976282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976282 prefixEnd_976282 := by exact prefixLift 976282
  have htrace : WordTrace (prefixWord ++ tailWord_976282) baseStart_976282 baseEnd_976282 := by
    simpa [prefixWord, tailWord_976282, baseEnd_976282] using wordTrace_append hprefix tailTrace_976282
  have hstable : (prefixWord ++ tailWord_976282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976282).length < 2 ^ (prefixWord ++ tailWord_976282).sum := by decide
  have hdescent : baseEnd_976282 < baseStart_976282 := by decide
  rcases family_descends (prefixWord ++ tailWord_976282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976295 : List Nat := [1, 1, 6, 1, 1, 1, 4, 2, 6]
def baseStart_976295 : Nat := 118140960795 + 976295 * 2 ^ 59
def prefixEnd_976295 : Nat := 4983230072969 + 3 ^ 40 * 976295 * 2
def baseEnd_976295 : Nat := 55700955064595886113623

theorem tailTrace_976295 : CollatzResearch.WordTrace tailWord_976295 prefixEnd_976295 55700955064595886113623 := by
  unfold tailWord_976295
  simp only [CollatzResearch.WordTrace]
  refine ⟨35608403998057427756426339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23738935998704951837617559 35608403998057427756426339)
  ·
    refine ⟨53412605997086141634639509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35608403998057427756426339 53412605997086141634639509)
    ·
      refine ⟨2503715906113412889123727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53412605997086141634639509 2503715906113412889123727)
      ·
        refine ⟨3755573859170119333685591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503715906113412889123727 3755573859170119333685591)
        ·
          refine ⟨5633360788755179000528387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3755573859170119333685591 5633360788755179000528387)
          ·
            refine ⟨8450041183132768500792581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5633360788755179000528387 8450041183132768500792581)
            ·
              refine ⟨1584382721837394093898609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8450041183132768500792581 1584382721837394093898609)
              ·
                refine ⟨1188287041378045570423957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584382721837394093898609 1188287041378045570423957)
                ·
                  refine ⟨55700955064595886113623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1188287041378045570423957 55700955064595886113623)
                  ·
                    rfl

theorem cell23_976295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 6].length) (baseStart_976295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976295 prefixEnd_976295 := by exact prefixLift 976295
  have htrace : WordTrace (prefixWord ++ tailWord_976295) baseStart_976295 baseEnd_976295 := by
    simpa [prefixWord, tailWord_976295, baseEnd_976295] using wordTrace_append hprefix tailTrace_976295
  have hstable : (prefixWord ++ tailWord_976295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976295).length < 2 ^ (prefixWord ++ tailWord_976295).sum := by decide
  have hdescent : baseEnd_976295 < baseStart_976295 := by decide
  rcases family_descends (prefixWord ++ tailWord_976295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976318 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_976318 : Nat := 118140960795 + 976318 * 2 ^ 59
def prefixEnd_976318 : Nat := 4983230072969 + 3 ^ 40 * 976318 * 2
def baseEnd_976318 : Nat := 501320405636416385035001

theorem tailTrace_976318 : CollatzResearch.WordTrace tailWord_976318 prefixEnd_976318 501320405636416385035001 := by
  unfold tailWord_976318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4451155359621762835564201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23739495251316068456342405 4451155359621762835564201)
  ·
    refine ⟨3338366519716322126673151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4451155359621762835564201 3338366519716322126673151)
    ·
      refine ⟨5007549779574483190009727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3338366519716322126673151 5007549779574483190009727)
      ·
        refine ⟨7511324669361724785014591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5007549779574483190009727 7511324669361724785014591)
        ·
          refine ⟨11266987004042587177521887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7511324669361724785014591 11266987004042587177521887)
          ·
            refine ⟨16900480506063880766282831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11266987004042587177521887 16900480506063880766282831)
            ·
              refine ⟨25350720759095821149424247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16900480506063880766282831 25350720759095821149424247)
              ·
                refine ⟨38026081138643731724136371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25350720759095821149424247 38026081138643731724136371)
                ·
                  refine ⟨57039121707965597586204557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38026081138643731724136371 57039121707965597586204557)
                  ·
                    refine ⟨21389670640487099094826709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57039121707965597586204557 21389670640487099094826709)
                    ·
                      refine ⟨501320405636416385035001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21389670640487099094826709 501320405636416385035001)
                      ·
                        rfl

theorem cell23_976318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_976318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976318 prefixEnd_976318 := by exact prefixLift 976318
  have htrace : WordTrace (prefixWord ++ tailWord_976318) baseStart_976318 baseEnd_976318 := by
    simpa [prefixWord, tailWord_976318, baseEnd_976318] using wordTrace_append hprefix tailTrace_976318
  have hstable : (prefixWord ++ tailWord_976318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976318).length < 2 ^ (prefixWord ++ tailWord_976318).sum := by decide
  have hdescent : baseEnd_976318 < baseStart_976318 := by decide
  rcases family_descends (prefixWord ++ tailWord_976318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976332 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 1, 5, 2]
def baseStart_976332 : Nat := 118140960795 + 976332 * 2 ^ 59
def prefixEnd_976332 : Nat := 4983230072969 + 3 ^ 40 * 976332 * 2
def baseEnd_976332 : Nat := 501327594365579330259937

theorem tailTrace_976332 : CollatzResearch.WordTrace tailWord_976332 prefixEnd_976332 501327594365579330259937 := by
  unfold tailWord_976332
  simp only [CollatzResearch.WordTrace]
  refine ⟨17804876749461691537761625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23739835665948922050348833 17804876749461691537761625)
  ·
    refine ⟨13353657562096268653321219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17804876749461691537761625 13353657562096268653321219)
    ·
      refine ⟨20030486343144402979981829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13353657562096268653321219 20030486343144402979981829)
      ·
        refine ⟨3755716189339575558746593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20030486343144402979981829 3755716189339575558746593)
        ·
          refine ⟨2816787142004681669059945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3755716189339575558746593 2816787142004681669059945)
          ·
            refine ⟨2112590356503511251794959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2816787142004681669059945 2112590356503511251794959)
            ·
              refine ⟨3168885534755266877692439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112590356503511251794959 3168885534755266877692439)
              ·
                refine ⟨4753328302132900316538659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168885534755266877692439 4753328302132900316538659)
                ·
                  refine ⟨7129992453199350474807989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753328302132900316538659 7129992453199350474807989)
                  ·
                    refine ⟨668436792487439107013249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7129992453199350474807989 668436792487439107013249)
                    ·
                      refine ⟨501327594365579330259937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668436792487439107013249 501327594365579330259937)
                      ·
                        rfl

theorem cell23_976332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_976332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976332 prefixEnd_976332 := by exact prefixLift 976332
  have htrace : WordTrace (prefixWord ++ tailWord_976332) baseStart_976332 baseEnd_976332 := by
    simpa [prefixWord, tailWord_976332, baseEnd_976332] using wordTrace_append hprefix tailTrace_976332
  have hstable : (prefixWord ++ tailWord_976332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976332).length < 2 ^ (prefixWord ++ tailWord_976332).sum := by decide
  have hdescent : baseEnd_976332 < baseStart_976332 := by decide
  rcases family_descends (prefixWord ++ tailWord_976332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976385 : List Nat := [1, 2, 4, 1, 4, 1, 1, 9]
def baseStart_976385 : Nat := 118140960795 + 976385 * 2 ^ 59
def prefixEnd_976385 : Nat := 4983230072969 + 3 ^ 40 * 976385 * 2
def baseEnd_976385 : Nat := 18568696623713615662859

theorem tailTrace_976385 : CollatzResearch.WordTrace tailWord_976385 prefixEnd_976385 18568696623713615662859 := by
  unfold tailWord_976385
  simp only [CollatzResearch.WordTrace]
  refine ⟨35611686567731373127202609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23741124378487582084801739 35611686567731373127202609)
  ·
    refine ⟨26708764925798529845401957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35611686567731373127202609 26708764925798529845401957)
    ·
      refine ⟨5007893423587224346012867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26708764925798529845401957 5007893423587224346012867)
      ·
        refine ⟨7511840135380836519019301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5007893423587224346012867 7511840135380836519019301)
        ·
          refine ⟨1408470025383906847316119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7511840135380836519019301 1408470025383906847316119)
          ·
            refine ⟨2112705038075860270974179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408470025383906847316119 2112705038075860270974179)
            ·
              refine ⟨3169057557113790406461269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112705038075860270974179 3169057557113790406461269)
              ·
                refine ⟨18568696623713615662859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3169057557113790406461269 18568696623713615662859)
                ·
                  rfl

theorem cell23_976385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 9].length) (baseStart_976385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976385 prefixEnd_976385 := by exact prefixLift 976385
  have htrace : WordTrace (prefixWord ++ tailWord_976385) baseStart_976385 baseEnd_976385 := by
    simpa [prefixWord, tailWord_976385, baseEnd_976385] using wordTrace_append hprefix tailTrace_976385
  have hstable : (prefixWord ++ tailWord_976385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976385).length < 2 ^ (prefixWord ++ tailWord_976385).sum := by decide
  have hdescent : baseEnd_976385 < baseStart_976385 := by decide
  rcases family_descends (prefixWord ++ tailWord_976385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976412 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_976412 : Nat := 118140960795 + 976412 * 2 ^ 59
def prefixEnd_976412 : Nat := 4983230072969 + 3 ^ 40 * 976412 * 2
def baseEnd_976412 : Nat := 501368672817939017259569

theorem tailTrace_976412 : CollatzResearch.WordTrace tailWord_976412 prefixEnd_976412 501368672817939017259569 := by
  unfold tailWord_976412
  simp only [CollatzResearch.WordTrace]
  refine ⟨17806335669316778369217745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23741780892422371158956993 17806335669316778369217745)
  ·
    refine ⟨13354751751987583776913309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17806335669316778369217745 13354751751987583776913309)
    ·
      refine ⟨5008031906995343916342491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13354751751987583776913309 5008031906995343916342491)
      ·
        refine ⟨7512047860493015874513737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5008031906995343916342491 7512047860493015874513737)
        ·
          refine ⟨5634035895369761905885303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7512047860493015874513737 5634035895369761905885303)
          ·
            refine ⟨8451053843054642858827955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634035895369761905885303 8451053843054642858827955)
            ·
              refine ⟨12676580764581964288241933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8451053843054642858827955 12676580764581964288241933)
              ·
                refine ⟨4753717786718236608090725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12676580764581964288241933 4753717786718236608090725)
                ·
                  refine ⟨891322085009669364017011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4753717786718236608090725 891322085009669364017011)
                  ·
                    refine ⟨1336983127514504046025517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 891322085009669364017011 1336983127514504046025517)
                    ·
                      refine ⟨501368672817939017259569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1336983127514504046025517 501368672817939017259569)
                      ·
                        rfl

theorem cell23_976412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_976412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976412 prefixEnd_976412 := by exact prefixLift 976412
  have htrace : WordTrace (prefixWord ++ tailWord_976412) baseStart_976412 baseEnd_976412 := by
    simpa [prefixWord, tailWord_976412, baseEnd_976412] using wordTrace_append hprefix tailTrace_976412
  have hstable : (prefixWord ++ tailWord_976412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976412).length < 2 ^ (prefixWord ++ tailWord_976412).sum := by decide
  have hdescent : baseEnd_976412 < baseStart_976412 := by decide
  rcases family_descends (prefixWord ++ tailWord_976412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976413 : List Nat := [1, 4, 2, 2, 1, 1, 5, 2, 1, 2, 2]
def baseStart_976413 : Nat := 118140960795 + 976413 * 2 ^ 59
def prefixEnd_976413 : Nat := 4983230072969 + 3 ^ 40 * 976413 * 2
def baseEnd_976413 : Nat := 501369186298593513347065

theorem tailTrace_976413 : CollatzResearch.WordTrace tailWord_976413 prefixEnd_976413 501369186298593513347065 := by
  unfold tailWord_976413
  simp only [CollatzResearch.WordTrace]
  refine ⟨35612707811629933909221893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23741805207753289272814595 35612707811629933909221893)
  ·
    refine ⟨6677382714680612607979105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35612707811629933909221893 6677382714680612607979105)
    ·
      refine ⟨5008037036010459455984329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6677382714680612607979105 5008037036010459455984329)
      ·
        refine ⟨3756027777007844591988247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5008037036010459455984329 3756027777007844591988247)
        ·
          refine ⟨5634041665511766887982371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756027777007844591988247 5634041665511766887982371)
          ·
            refine ⟨8451062498267650331973557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634041665511766887982371 8451062498267650331973557)
            ·
              refine ⟨792287109212592218622521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8451062498267650331973557 792287109212592218622521)
              ·
                refine ⟨594215331909444163966891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792287109212592218622521 594215331909444163966891)
                ·
                  refine ⟨891322997864166245950337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594215331909444163966891 891322997864166245950337)
                  ·
                    refine ⟨668492248398124684462753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 891322997864166245950337 668492248398124684462753)
                    ·
                      refine ⟨501369186298593513347065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668492248398124684462753 501369186298593513347065)
                      ·
                        rfl

theorem cell23_976413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_976413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976413 prefixEnd_976413 := by exact prefixLift 976413
  have htrace : WordTrace (prefixWord ++ tailWord_976413) baseStart_976413 baseEnd_976413 := by
    simpa [prefixWord, tailWord_976413, baseEnd_976413] using wordTrace_append hprefix tailTrace_976413
  have hstable : (prefixWord ++ tailWord_976413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976413).length < 2 ^ (prefixWord ++ tailWord_976413).sum := by decide
  have hdescent : baseEnd_976413 < baseStart_976413 := by decide
  rcases family_descends (prefixWord ++ tailWord_976413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976439 : List Nat := [1, 1, 3, 1, 2, 4, 3, 2, 1, 3, 2]
def baseStart_976439 : Nat := 118140960795 + 976439 * 2 ^ 59
def prefixEnd_976439 : Nat := 4983230072969 + 3 ^ 40 * 976439 * 2
def baseEnd_976439 : Nat := 501382536795610411621945

theorem tailTrace_976439 : CollatzResearch.WordTrace tailWord_976439 prefixEnd_976439 501382536795610411621945 := by
  unfold tailWord_976439
  simp only [CollatzResearch.WordTrace]
  refine ⟨35613656109535740349668371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23742437406357160233112247 35613656109535740349668371)
  ·
    refine ⟨53420484164303610524502557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35613656109535740349668371 53420484164303610524502557)
    ·
      refine ⟨20032681561613853946688459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53420484164303610524502557 20032681561613853946688459)
      ·
        refine ⟨30049022342420780920032689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20032681561613853946688459 30049022342420780920032689)
        ·
          refine ⟨22536766756815585690024517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30049022342420780920032689 22536766756815585690024517)
          ·
            refine ⟨4225643766902922316879597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22536766756815585690024517 4225643766902922316879597)
            ·
              refine ⟨1584616412588595868829849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4225643766902922316879597 1584616412588595868829849)
              ·
                refine ⟨1188462309441446901622387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584616412588595868829849 1188462309441446901622387)
                ·
                  refine ⟨1782693464162170352433581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1188462309441446901622387 1782693464162170352433581)
                  ·
                    refine ⟨668510049060813882162593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1782693464162170352433581 668510049060813882162593)
                    ·
                      refine ⟨501382536795610411621945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668510049060813882162593 501382536795610411621945)
                      ·
                        rfl

theorem cell23_976439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 3, 2].length) (baseStart_976439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976439 prefixEnd_976439 := by exact prefixLift 976439
  have htrace : WordTrace (prefixWord ++ tailWord_976439) baseStart_976439 baseEnd_976439 := by
    simpa [prefixWord, tailWord_976439, baseEnd_976439] using wordTrace_append hprefix tailTrace_976439
  have hstable : (prefixWord ++ tailWord_976439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976439).length < 2 ^ (prefixWord ++ tailWord_976439).sum := by decide
  have hdescent : baseEnd_976439 < baseStart_976439 := by decide
  rcases family_descends (prefixWord ++ tailWord_976439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976465 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_976465 : Nat := 118140960795 + 976465 * 2 ^ 59
def prefixEnd_976465 : Nat := 4983230072969 + 3 ^ 40 * 976465 * 2
def baseEnd_976465 : Nat := 501395887292627309896825

theorem tailTrace_976465 : CollatzResearch.WordTrace tailWord_976465 prefixEnd_976465 501395887292627309896825 := by
  unfold tailWord_976465
  simp only [CollatzResearch.WordTrace]
  refine ⟨35614604407441546790114849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23743069604961031193409899 35614604407441546790114849)
  ·
    refine ⟨26710953305581160092586137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35614604407441546790114849 26710953305581160092586137)
    ·
      refine ⟨20033214979185870069439603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26710953305581160092586137 20033214979185870069439603)
      ·
        refine ⟨30049822468778805104159405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20033214979185870069439603 30049822468778805104159405)
        ·
          refine ⟨11268683425792051914059777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30049822468778805104159405 11268683425792051914059777)
          ·
            refine ⟨8451512569344038935544833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11268683425792051914059777 8451512569344038935544833)
            ·
              refine ⟨6338634427008029201658625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8451512569344038935544833 6338634427008029201658625)
              ·
                refine ⟨4753975820256021901243969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6338634427008029201658625 4753975820256021901243969)
                ·
                  refine ⟨3565481865192016425932977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4753975820256021901243969 3565481865192016425932977)
                  ·
                    refine ⟨2674111398894012319449733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3565481865192016425932977 2674111398894012319449733)
                    ·
                      refine ⟨501395887292627309896825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2674111398894012319449733 501395887292627309896825)
                      ·
                        rfl

theorem cell23_976465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_976465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976465 prefixEnd_976465 := by exact prefixLift 976465
  have htrace : WordTrace (prefixWord ++ tailWord_976465) baseStart_976465 baseEnd_976465 := by
    simpa [prefixWord, tailWord_976465, baseEnd_976465] using wordTrace_append hprefix tailTrace_976465
  have hstable : (prefixWord ++ tailWord_976465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976465).length < 2 ^ (prefixWord ++ tailWord_976465).sum := by decide
  have hdescent : baseEnd_976465 < baseStart_976465 := by decide
  rcases family_descends (prefixWord ++ tailWord_976465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976505 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 1, 7]
def baseStart_976505 : Nat := 118140960795 + 976505 * 2 ^ 59
def prefixEnd_976505 : Nat := 4983230072969 + 3 ^ 40 * 976505 * 2
def baseEnd_976505 : Nat := 167138808839602384465547

theorem tailTrace_976505 : CollatzResearch.WordTrace tailWord_976505 prefixEnd_976505 167138808839602384465547 := by
  unfold tailWord_976505
  simp only [CollatzResearch.WordTrace]
  refine ⟨35616063327296633621570969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23744042218197755747713979 35616063327296633621570969)
  ·
    refine ⟨26712047495472475216178227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35616063327296633621570969 26712047495472475216178227)
    ·
      refine ⟨40068071243208712824267341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26712047495472475216178227 40068071243208712824267341)
      ·
        refine ⟨15025526716203267309100253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40068071243208712824267341 15025526716203267309100253)
        ·
          refine ⟨5634572518576225240912595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15025526716203267309100253 5634572518576225240912595)
          ·
            refine ⟨8451858777864337861368893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634572518576225240912595 8451858777864337861368893)
            ·
              refine ⟨3169447041699126698013335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8451858777864337861368893 3169447041699126698013335)
              ·
                refine ⟨4754170562548690047020003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169447041699126698013335 4754170562548690047020003)
                ·
                  refine ⟨7131255843823035070530005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4754170562548690047020003 7131255843823035070530005)
                  ·
                    refine ⟨167138808839602384465547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7131255843823035070530005 167138808839602384465547)
                    ·
                      rfl

theorem cell23_976505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 7].length) (baseStart_976505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976505 prefixEnd_976505 := by exact prefixLift 976505
  have htrace : WordTrace (prefixWord ++ tailWord_976505) baseStart_976505 baseEnd_976505 := by
    simpa [prefixWord, tailWord_976505, baseEnd_976505] using wordTrace_append hprefix tailTrace_976505
  have hstable : (prefixWord ++ tailWord_976505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976505).length < 2 ^ (prefixWord ++ tailWord_976505).sum := by decide
  have hdescent : baseEnd_976505 < baseStart_976505 := by decide
  rcases family_descends (prefixWord ++ tailWord_976505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976509 : List Nat := [1, 4, 1, 1, 4, 2, 2, 3, 5]
def baseStart_976509 : Nat := 118140960795 + 976509 * 2 ^ 59
def prefixEnd_976509 : Nat := 4983230072969 + 3 ^ 40 * 976509 * 2
def baseEnd_976509 : Nat := 55713164493491681971847

theorem tailTrace_976509 : CollatzResearch.WordTrace tailWord_976509 prefixEnd_976509 55713164493491681971847 := by
  unfold tailWord_976509
  simp only [CollatzResearch.WordTrace]
  refine ⟨35616209219282142304716581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23744139479521428203144387 35616209219282142304716581)
  ·
    refine ⟨6678039228615401682134359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35616209219282142304716581 6678039228615401682134359)
    ·
      refine ⟨10017058842923102523201539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6678039228615401682134359 10017058842923102523201539)
      ·
        refine ⟨15025588264384653784802309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10017058842923102523201539 15025588264384653784802309)
        ·
          refine ⟨2817297799572122584650433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15025588264384653784802309 2817297799572122584650433)
          ·
            refine ⟨2112973349679091938487825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2817297799572122584650433 2112973349679091938487825)
            ·
              refine ⟨1584730012259318953865869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2112973349679091938487825 1584730012259318953865869)
              ·
                refine ⟨594273754597244607699701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1584730012259318953865869 594273754597244607699701)
                ·
                  refine ⟨55713164493491681971847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 594273754597244607699701 55713164493491681971847)
                  ·
                    rfl

theorem cell23_976509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_976509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976509 prefixEnd_976509 := by exact prefixLift 976509
  have htrace : WordTrace (prefixWord ++ tailWord_976509) baseStart_976509 baseEnd_976509 := by
    simpa [prefixWord, tailWord_976509, baseEnd_976509] using wordTrace_append hprefix tailTrace_976509
  have hstable : (prefixWord ++ tailWord_976509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976509).length < 2 ^ (prefixWord ++ tailWord_976509).sum := by decide
  have hdescent : baseEnd_976509 < baseStart_976509 := by decide
  rcases family_descends (prefixWord ++ tailWord_976509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976520 : List Nat := [2, 1, 3, 5, 1, 2, 1, 2, 2, 2, 2]
def baseStart_976520 : Nat := 118140960795 + 976520 * 2 ^ 59
def prefixEnd_976520 : Nat := 4983230072969 + 3 ^ 40 * 976520 * 2
def baseEnd_976520 : Nat := 501424128728624594709073

theorem tailTrace_976520 : CollatzResearch.WordTrace tailWord_976520 prefixEnd_976520 501424128728624594709073 := by
  unfold tailWord_976520
  simp only [CollatzResearch.WordTrace]
  refine ⟨17808305211121145591683507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23744406948161527455578009 17808305211121145591683507)
  ·
    refine ⟨26712457816681718387525261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17808305211121145591683507 26712457816681718387525261)
    ·
      refine ⟨10017171681255644395321973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26712457816681718387525261 10017171681255644395321973)
      ·
        refine ⟨939109845117716662061435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10017171681255644395321973 939109845117716662061435)
        ·
          refine ⟨1408664767676574993092153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939109845117716662061435 1408664767676574993092153)
          ·
            refine ⟨1056498575757431244819115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1408664767676574993092153 1056498575757431244819115)
            ·
              refine ⟨1584747863636146867228673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056498575757431244819115 1584747863636146867228673)
              ·
                refine ⟨1188560897727110150421505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584747863636146867228673 1188560897727110150421505)
                ·
                  refine ⟨891420673295332612816129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1188560897727110150421505 891420673295332612816129)
                  ·
                    refine ⟨668565504971499459612097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 891420673295332612816129 668565504971499459612097)
                    ·
                      refine ⟨501424128728624594709073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668565504971499459612097 501424128728624594709073)
                      ·
                        rfl

theorem cell23_976520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_976520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976520 prefixEnd_976520 := by exact prefixLift 976520
  have htrace : WordTrace (prefixWord ++ tailWord_976520) baseStart_976520 baseEnd_976520 := by
    simpa [prefixWord, tailWord_976520, baseEnd_976520] using wordTrace_append hprefix tailTrace_976520
  have hstable : (prefixWord ++ tailWord_976520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976520).length < 2 ^ (prefixWord ++ tailWord_976520).sum := by decide
  have hdescent : baseEnd_976520 < baseStart_976520 := by decide
  rcases family_descends (prefixWord ++ tailWord_976520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976562 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_976562 : Nat := 118140960795 + 976562 * 2 ^ 59
def prefixEnd_976562 : Nat := 4983230072969 + 3 ^ 40 * 976562 * 2
def baseEnd_976562 : Nat := 501445694916113430383879

theorem tailTrace_976562 : CollatzResearch.WordTrace tailWord_976562 prefixEnd_976562 501445694916113430383879 := by
  unfold tailWord_976562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8904535572022533089098985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23745428192060088237597293 8904535572022533089098985)
  ·
    refine ⟨6678401679016899816824239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8904535572022533089098985 6678401679016899816824239)
    ·
      refine ⟨10017602518525349725236359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6678401679016899816824239 10017602518525349725236359)
      ·
        refine ⟨15026403777788024587854539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10017602518525349725236359 15026403777788024587854539)
        ·
          refine ⟨22539605666682036881781809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15026403777788024587854539 22539605666682036881781809)
          ·
            refine ⟨16904704250011527661336357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22539605666682036881781809 16904704250011527661336357)
            ·
              refine ⟨3169632046877161436500567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16904704250011527661336357 3169632046877161436500567)
              ·
                refine ⟨4754448070315742154750851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169632046877161436500567 4754448070315742154750851)
                ·
                  refine ⟨7131672105473613232126277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4754448070315742154750851 7131672105473613232126277)
                  ·
                    refine ⟨1337188519776302481023677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7131672105473613232126277 1337188519776302481023677)
                    ·
                      refine ⟨501445694916113430383879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1337188519776302481023677 501445694916113430383879)
                      ·
                        rfl

theorem cell23_976562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_976562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976562 prefixEnd_976562 := by exact prefixLift 976562
  have htrace : WordTrace (prefixWord ++ tailWord_976562) baseStart_976562 baseEnd_976562 := by
    simpa [prefixWord, tailWord_976562, baseEnd_976562] using wordTrace_append hprefix tailTrace_976562
  have hstable : (prefixWord ++ tailWord_976562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976562).length < 2 ^ (prefixWord ++ tailWord_976562).sum := by decide
  have hdescent : baseEnd_976562 < baseStart_976562 := by decide
  rcases family_descends (prefixWord ++ tailWord_976562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976586 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 3, 4]
def baseStart_976586 : Nat := 118140960795 + 976586 * 2 ^ 59
def prefixEnd_976586 : Nat := 4983230072969 + 3 ^ 40 * 976586 * 2
def baseEnd_976586 : Nat := 167152672817273778827923

theorem tailTrace_976586 : CollatzResearch.WordTrace tailWord_976586 prefixEnd_976586 167152672817273778827923 := by
  unfold tailWord_976586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8904754410000796113817403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23746011760002122970179741 8904754410000796113817403)
  ·
    refine ⟨13357131615001194170726105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8904754410000796113817403 13357131615001194170726105)
    ·
      refine ⟨10017848711250895628044579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13357131615001194170726105 10017848711250895628044579)
      ·
        refine ⟨15026773066876343442066869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10017848711250895628044579 15026773066876343442066869)
        ·
          refine ⟨1408759975019657197693769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15026773066876343442066869 1408759975019657197693769)
          ·
            refine ⟨1056569981264742898270327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1408759975019657197693769 1056569981264742898270327)
            ·
              refine ⟨1584854971897114347405491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056569981264742898270327 1584854971897114347405491)
              ·
                refine ⟨2377282457845671521108237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584854971897114347405491 2377282457845671521108237)
                ·
                  refine ⟨891480921692126820415589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2377282457845671521108237 891480921692126820415589)
                  ·
                    refine ⟨167152672817273778827923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 891480921692126820415589 167152672817273778827923)
                    ·
                      rfl

theorem cell23_976586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_976586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976586 prefixEnd_976586 := by exact prefixLift 976586
  have htrace : WordTrace (prefixWord ++ tailWord_976586) baseStart_976586 baseEnd_976586 := by
    simpa [prefixWord, tailWord_976586, baseEnd_976586] using wordTrace_append hprefix tailTrace_976586
  have hstable : (prefixWord ++ tailWord_976586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976586).length < 2 ^ (prefixWord ++ tailWord_976586).sum := by decide
  have hdescent : baseEnd_976586 < baseStart_976586 := by decide
  rcases family_descends (prefixWord ++ tailWord_976586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976612 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_976612 : Nat := 118140960795 + 976612 * 2 ^ 59
def prefixEnd_976612 : Nat := 4983230072969 + 3 ^ 40 * 976612 * 2
def baseEnd_976612 : Nat := 167157122982946078252883

theorem tailTrace_976612 : CollatzResearch.WordTrace tailWord_976612 prefixEnd_976612 167157122982946078252883 := by
  unfold tailWord_976612
  simp only [CollatzResearch.WordTrace]
  refine ⟨17809982968954495447858045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23746643958605993930477393 17809982968954495447858045)
  ·
    refine ⟨6678743613357935792946767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17809982968954495447858045 6678743613357935792946767)
    ·
      refine ⟨10018115420036903689420151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6678743613357935792946767 10018115420036903689420151)
      ·
        refine ⟨15027173130055355534130227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10018115420036903689420151 15027173130055355534130227)
        ·
          refine ⟨22540759695083033301195341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15027173130055355534130227 22540759695083033301195341)
          ·
            refine ⟨8452784885656137487948253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22540759695083033301195341 8452784885656137487948253)
            ·
              refine ⟨3169794332121051557980595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8452784885656137487948253 3169794332121051557980595)
              ·
                refine ⟨4754691498181577336970893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169794332121051557980595 4754691498181577336970893)
                ·
                  refine ⟨1783009311818091501364085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4754691498181577336970893 1783009311818091501364085)
                  ·
                    refine ⟨167157122982946078252883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1783009311818091501364085 167157122982946078252883)
                    ·
                      rfl

theorem cell23_976612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_976612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976612 prefixEnd_976612 := by exact prefixLift 976612
  have htrace : WordTrace (prefixWord ++ tailWord_976612) baseStart_976612 baseEnd_976612 := by
    simpa [prefixWord, tailWord_976612, baseEnd_976612] using wordTrace_append hprefix tailTrace_976612
  have hstable : (prefixWord ++ tailWord_976612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976612).length < 2 ^ (prefixWord ++ tailWord_976612).sum := by decide
  have hdescent : baseEnd_976612 < baseStart_976612 := by decide
  rcases family_descends (prefixWord ++ tailWord_976612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976619 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 2, 3, 2]
def baseStart_976619 : Nat := 118140960795 + 976619 * 2 ^ 59
def prefixEnd_976619 : Nat := 4983230072969 + 3 ^ 40 * 976619 * 2
def baseEnd_976619 : Nat := 501474963313419707371117

theorem tailTrace_976619 : CollatzResearch.WordTrace tailWord_976619 prefixEnd_976619 501474963313419707371117 := by
  unfold tailWord_976619
  simp only [CollatzResearch.WordTrace]
  refine ⟨35620221248883631091220911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23746814165922420727480607 35620221248883631091220911)
  ·
    refine ⟨53430331873325446636831367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35620221248883631091220911 53430331873325446636831367)
    ·
      refine ⟨80145497809988169955247051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53430331873325446636831367 80145497809988169955247051)
      ·
        refine ⟨120218246714982254932870577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80145497809988169955247051 120218246714982254932870577)
        ·
          refine ⟨90163685036236691199652933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120218246714982254932870577 90163685036236691199652933)
          ·
            refine ⟨16905690944294379599934925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90163685036236691199652933 16905690944294379599934925)
            ·
              refine ⟨6339634104110392349975597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16905690944294379599934925 6339634104110392349975597)
              ·
                refine ⟨2377362789041397131240849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6339634104110392349975597 2377362789041397131240849)
                ·
                  refine ⟨1783022091781047848430637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2377362789041397131240849 1783022091781047848430637)
                  ·
                    refine ⟨668633284417892943161489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1783022091781047848430637 668633284417892943161489)
                    ·
                      refine ⟨501474963313419707371117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668633284417892943161489 501474963313419707371117)
                      ·
                        rfl

theorem cell23_976619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 3, 2].length) (baseStart_976619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976619 prefixEnd_976619 := by exact prefixLift 976619
  have htrace : WordTrace (prefixWord ++ tailWord_976619) baseStart_976619 baseEnd_976619 := by
    simpa [prefixWord, tailWord_976619, baseEnd_976619] using wordTrace_append hprefix tailTrace_976619
  have hstable : (prefixWord ++ tailWord_976619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976619).length < 2 ^ (prefixWord ++ tailWord_976619).sum := by decide
  have hdescent : baseEnd_976619 < baseStart_976619 := by decide
  rcases family_descends (prefixWord ++ tailWord_976619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976643 : List Nat := [1, 1, 1, 3, 2, 2, 6, 2, 1, 1, 3]
def baseStart_976643 : Nat := 118140960795 + 976643 * 2 ^ 59
def prefixEnd_976643 : Nat := 4983230072969 + 3 ^ 40 * 976643 * 2
def baseEnd_976643 : Nat := 501487286849127613471007

theorem tailTrace_976643 : CollatzResearch.WordTrace tailWord_976643 prefixEnd_976643 501487286849127613471007 := by
  unfold tailWord_976643
  simp only [CollatzResearch.WordTrace]
  refine ⟨35621096600796683190094583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23747397733864455460063055 35621096600796683190094583)
  ·
    refine ⟨53431644901195024785141875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35621096600796683190094583 53431644901195024785141875)
    ·
      refine ⟨80147467351792537177712813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53431644901195024785141875 80147467351792537177712813)
      ·
        refine ⟨30055300256922201441642305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80147467351792537177712813 30055300256922201441642305)
        ·
          refine ⟨22541475192691651081231729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30055300256922201441642305 22541475192691651081231729)
          ·
            refine ⟨16906106394518738310923797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22541475192691651081231729 16906106394518738310923797)
            ·
              refine ⟨792473737243065858324553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16906106394518738310923797 792473737243065858324553)
              ·
                refine ⟨594355302932299393743415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792473737243065858324553 594355302932299393743415)
                ·
                  refine ⟨891532954398449090615123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594355302932299393743415 891532954398449090615123)
                  ·
                    refine ⟨1337299431597673635922685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 891532954398449090615123 1337299431597673635922685)
                    ·
                      refine ⟨501487286849127613471007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1337299431597673635922685 501487286849127613471007)
                      ·
                        rfl

theorem cell23_976643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 1, 1, 3].length) (baseStart_976643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976643 prefixEnd_976643 := by exact prefixLift 976643
  have htrace : WordTrace (prefixWord ++ tailWord_976643) baseStart_976643 baseEnd_976643 := by
    simpa [prefixWord, tailWord_976643, baseEnd_976643] using wordTrace_append hprefix tailTrace_976643
  have hstable : (prefixWord ++ tailWord_976643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976643).length < 2 ^ (prefixWord ++ tailWord_976643).sum := by decide
  have hdescent : baseEnd_976643 < baseStart_976643 := by decide
  rcases family_descends (prefixWord ++ tailWord_976643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976652 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 1, 1, 5]
def baseStart_976652 : Nat := 118140960795 + 976652 * 2 ^ 59
def prefixEnd_976652 : Nat := 4983230072969 + 3 ^ 40 * 976652 * 2
def baseEnd_976652 : Nat := 501491908175018078258465

theorem tailTrace_976652 : CollatzResearch.WordTrace tailWord_976652 prefixEnd_976652 501491908175018078258465 := by
  unfold tailWord_976652
  simp only [CollatzResearch.WordTrace]
  refine ⟨17810712428882038863586105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23747616571842718484781473 17810712428882038863586105)
  ·
    refine ⟨13358034321661529147689579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17810712428882038863586105 13358034321661529147689579)
    ·
      refine ⟨20037051482492293721534369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13358034321661529147689579 20037051482492293721534369)
      ·
        refine ⟨15027788611869220291150777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20037051482492293721534369 15027788611869220291150777)
        ·
          refine ⟨11270841458901915218363083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15027788611869220291150777 11270841458901915218363083)
          ·
            refine ⟨16906262188352872827544625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11270841458901915218363083 16906262188352872827544625)
            ·
              refine ⟨12679696641264654620658469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16906262188352872827544625 12679696641264654620658469)
              ·
                refine ⟨2377443120237122741373463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12679696641264654620658469 2377443120237122741373463)
                ·
                  refine ⟨3566164680355684112060195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2377443120237122741373463 3566164680355684112060195)
                  ·
                    refine ⟨5349247020533526168090293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3566164680355684112060195 5349247020533526168090293)
                    ·
                      refine ⟨501491908175018078258465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5349247020533526168090293 501491908175018078258465)
                      ·
                        rfl

theorem cell23_976652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_976652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976652 prefixEnd_976652 := by exact prefixLift 976652
  have htrace : WordTrace (prefixWord ++ tailWord_976652) baseStart_976652 baseEnd_976652 := by
    simpa [prefixWord, tailWord_976652, baseEnd_976652] using wordTrace_append hprefix tailTrace_976652
  have hstable : (prefixWord ++ tailWord_976652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976652).length < 2 ^ (prefixWord ++ tailWord_976652).sum := by decide
  have hdescent : baseEnd_976652 < baseStart_976652 := by decide
  rcases family_descends (prefixWord ++ tailWord_976652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976655 : List Nat := [1, 1, 2, 1, 1, 1, 4, 12]
def baseStart_976655 : Nat := 118140960795 + 976655 * 2 ^ 59
def prefixEnd_976655 : Nat := 4983230072969 + 3 ^ 40 * 976655 * 2
def baseEnd_976655 : Nat := 18573831430258576537813

theorem tailTrace_976655 : CollatzResearch.WordTrace tailWord_976655 prefixEnd_976655 18573831430258576537813 := by
  unfold tailWord_976655
  simp only [CollatzResearch.WordTrace]
  refine ⟨35621534276753209239531419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23747689517835472826354279 35621534276753209239531419)
  ·
    refine ⟨53432301415129813859297129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35621534276753209239531419 53432301415129813859297129)
    ·
      refine ⟨40074226061347360394472847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53432301415129813859297129 40074226061347360394472847)
      ·
        refine ⟨60111339092021040591709271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40074226061347360394472847 60111339092021040591709271)
        ·
          refine ⟨90167008638031560887563907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60111339092021040591709271 90167008638031560887563907)
          ·
            refine ⟨135250512957047341331345861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90167008638031560887563907 135250512957047341331345861)
            ·
              refine ⟨25359471179446376499627349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135250512957047341331345861 25359471179446376499627349)
              ·
                refine ⟨18573831430258576537813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 25359471179446376499627349 18573831430258576537813)
                ·
                  rfl

theorem cell23_976655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 12].length) (baseStart_976655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976655 prefixEnd_976655 := by exact prefixLift 976655
  have htrace : WordTrace (prefixWord ++ tailWord_976655) baseStart_976655 baseEnd_976655 := by
    simpa [prefixWord, tailWord_976655, baseEnd_976655] using wordTrace_append hprefix tailTrace_976655
  have hstable : (prefixWord ++ tailWord_976655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976655).length < 2 ^ (prefixWord ++ tailWord_976655).sum := by decide
  have hdescent : baseEnd_976655 < baseStart_976655 := by decide
  rcases family_descends (prefixWord ++ tailWord_976655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976666 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2]
def baseStart_976666 : Nat := 118140960795 + 976666 * 2 ^ 59
def prefixEnd_976666 : Nat := 4983230072969 + 3 ^ 40 * 976666 * 2
def baseEnd_976666 : Nat := 501499096904181023483401

theorem tailTrace_976666 : CollatzResearch.WordTrace tailWord_976666 prefixEnd_976666 501499096904181023483401 := by
  unfold tailWord_976666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8905483869928339529545463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23747956986475572078787901 8905483869928339529545463)
  ·
    refine ⟨13358225804892509294318195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8905483869928339529545463 13358225804892509294318195)
    ·
      refine ⟨20037338707338763941477293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13358225804892509294318195 20037338707338763941477293)
      ·
        refine ⟨7514002015252036478053985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20037338707338763941477293 7514002015252036478053985)
        ·
          refine ⟨5635501511439027358540489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7514002015252036478053985 5635501511439027358540489)
          ·
            refine ⟨4226626133579270518905367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5635501511439027358540489 4226626133579270518905367)
            ·
              refine ⟨6339939200368905778358051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4226626133579270518905367 6339939200368905778358051)
              ·
                refine ⟨9509908800553358667537077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6339939200368905778358051 9509908800553358667537077)
                ·
                  refine ⟨891553950051877375081601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9509908800553358667537077 891553950051877375081601)
                  ·
                    refine ⟨668665462538908031311201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 891553950051877375081601 668665462538908031311201)
                    ·
                      refine ⟨501499096904181023483401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668665462538908031311201 501499096904181023483401)
                      ·
                        rfl

theorem cell23_976666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_976666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976666 prefixEnd_976666 := by exact prefixLift 976666
  have htrace : WordTrace (prefixWord ++ tailWord_976666) baseStart_976666 baseEnd_976666 := by
    simpa [prefixWord, tailWord_976666, baseEnd_976666] using wordTrace_append hprefix tailTrace_976666
  have hstable : (prefixWord ++ tailWord_976666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976666).length < 2 ^ (prefixWord ++ tailWord_976666).sum := by decide
  have hdescent : baseEnd_976666 < baseStart_976666 := by decide
  rcases family_descends (prefixWord ++ tailWord_976666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976670 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_976670 : Nat := 118140960795 + 976670 * 2 ^ 59
def prefixEnd_976670 : Nat := 4983230072969 + 3 ^ 40 * 976670 * 2
def baseEnd_976670 : Nat := 501501150826799007833383

theorem tailTrace_976670 : CollatzResearch.WordTrace tailWord_976670 prefixEnd_976670 501501150826799007833383 := by
  unfold tailWord_976670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4452760171462358350165933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23748054247799244534218309 4452760171462358350165933)
  ·
    refine ⟨1669785064298384381312225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4452760171462358350165933 1669785064298384381312225)
    ·
      refine ⟨1252338798223788285984169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1669785064298384381312225 1252338798223788285984169)
      ·
        refine ⟨939254098667841214488127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1252338798223788285984169 939254098667841214488127)
        ·
          refine ⟨1408881148001761821732191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939254098667841214488127 1408881148001761821732191)
          ·
            refine ⟨2113321722002642732598287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408881148001761821732191 2113321722002642732598287)
            ·
              refine ⟨3169982583003964098897431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113321722002642732598287 3169982583003964098897431)
              ·
                refine ⟨4754973874505946148346147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169982583003964098897431 4754973874505946148346147)
                ·
                  refine ⟨7132460811758919222519221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4754973874505946148346147 7132460811758919222519221)
                  ·
                    refine ⟨668668201102398677111177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7132460811758919222519221 668668201102398677111177)
                    ·
                      refine ⟨501501150826799007833383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668668201102398677111177 501501150826799007833383)
                      ·
                        rfl

theorem cell23_976670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_976670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976670 prefixEnd_976670 := by exact prefixLift 976670
  have htrace : WordTrace (prefixWord ++ tailWord_976670) baseStart_976670 baseEnd_976670 := by
    simpa [prefixWord, tailWord_976670, baseEnd_976670] using wordTrace_append hprefix tailTrace_976670
  have hstable : (prefixWord ++ tailWord_976670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976670).length < 2 ^ (prefixWord ++ tailWord_976670).sum := by decide
  have hdescent : baseEnd_976670 < baseStart_976670 := by decide
  rcases family_descends (prefixWord ++ tailWord_976670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976693 : List Nat := [1, 3, 3, 1, 4, 2, 1, 2, 2, 4]
def baseStart_976693 : Nat := 118140960795 + 976693 * 2 ^ 59
def prefixEnd_976693 : Nat := 4983230072969 + 3 ^ 40 * 976693 * 2
def baseEnd_976693 : Nat := 167170986960617472615259

theorem tailTrace_976693 : CollatzResearch.WordTrace tailWord_976693 prefixEnd_976693 167170986960617472615259 := by
  unfold tailWord_976693
  simp only [CollatzResearch.WordTrace]
  refine ⟨35622920250615541729414733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23748613500410361152943155 35622920250615541729414733)
  ·
    refine ⟨13358595093980828148530525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35622920250615541729414733 13358595093980828148530525)
    ·
      refine ⟨5009473160242810555698947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13358595093980828148530525 5009473160242810555698947)
      ·
        refine ⟨7514209740364215833548421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5009473160242810555698947 7514209740364215833548421)
        ·
          refine ⟨1408914326318290468790329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7514209740364215833548421 1408914326318290468790329)
          ·
            refine ⟨1056685744738717851592747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1408914326318290468790329 1056685744738717851592747)
            ·
              refine ⟨1585028617108076777389121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1056685744738717851592747 1585028617108076777389121)
              ·
                refine ⟨1188771462831057583041841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1585028617108076777389121 1188771462831057583041841)
                ·
                  refine ⟨891578597123293187281381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1188771462831057583041841 891578597123293187281381)
                  ·
                    refine ⟨167170986960617472615259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 891578597123293187281381 167170986960617472615259)
                    ·
                      rfl

theorem cell23_976693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_976693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976693 prefixEnd_976693 := by exact prefixLift 976693
  have htrace : WordTrace (prefixWord ++ tailWord_976693) baseStart_976693 baseEnd_976693 := by
    simpa [prefixWord, tailWord_976693, baseEnd_976693] using wordTrace_append hprefix tailTrace_976693
  have hstable : (prefixWord ++ tailWord_976693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976693).length < 2 ^ (prefixWord ++ tailWord_976693).sum := by decide
  have hdescent : baseEnd_976693 < baseStart_976693 := by decide
  rcases family_descends (prefixWord ++ tailWord_976693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976773 : List Nat := [1, 3, 1, 1, 3, 2, 3, 3, 2, 2, 2]
def baseStart_976773 : Nat := 118140960795 + 976773 * 2 ^ 59
def prefixEnd_976773 : Nat := 4983230072969 + 3 ^ 40 * 976773 * 2
def baseEnd_976773 : Nat := 501554039334212104845409

theorem tailTrace_976773 : CollatzResearch.WordTrace tailWord_976773 prefixEnd_976773 501554039334212104845409 := by
  unfold tailWord_976773
  simp only [CollatzResearch.WordTrace]
  refine ⟨35625838090325715392326973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23750558726883810261551315 35625838090325715392326973)
  ·
    refine ⟨13359689283872143272122615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35625838090325715392326973 13359689283872143272122615)
    ·
      refine ⟨20039533925808214908183923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13359689283872143272122615 20039533925808214908183923)
      ·
        refine ⟨30059300888712322362275885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20039533925808214908183923 30059300888712322362275885)
        ·
          refine ⟨11272237833267120885853457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30059300888712322362275885 11272237833267120885853457)
          ·
            refine ⟨8454178374950340664390093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11272237833267120885853457 8454178374950340664390093)
            ·
              refine ⟨3170316890606377749146285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8454178374950340664390093 3170316890606377749146285)
              ·
                refine ⟨1188868833977391655929857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3170316890606377749146285 1188868833977391655929857)
                ·
                  refine ⟨891651625483043741947393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1188868833977391655929857 891651625483043741947393)
                  ·
                    refine ⟨668738719112282806460545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 891651625483043741947393 668738719112282806460545)
                    ·
                      refine ⟨501554039334212104845409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668738719112282806460545 501554039334212104845409)
                      ·
                        rfl

theorem cell23_976773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 2, 2].length) (baseStart_976773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976773 prefixEnd_976773 := by exact prefixLift 976773
  have htrace : WordTrace (prefixWord ++ tailWord_976773) baseStart_976773 baseEnd_976773 := by
    simpa [prefixWord, tailWord_976773, baseEnd_976773] using wordTrace_append hprefix tailTrace_976773
  have hstable : (prefixWord ++ tailWord_976773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976773).length < 2 ^ (prefixWord ++ tailWord_976773).sum := by decide
  have hdescent : baseEnd_976773 < baseStart_976773 := by decide
  rcases family_descends (prefixWord ++ tailWord_976773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976812 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_976812 : Nat := 118140960795 + 976812 * 2 ^ 59
def prefixEnd_976812 : Nat := 4983230072969 + 3 ^ 40 * 976812 * 2
def baseEnd_976812 : Nat := 501574065079737452257729

theorem tailTrace_976812 : CollatzResearch.WordTrace tailWord_976812 prefixEnd_976812 501574065079737452257729 := by
  unfold tailWord_976812
  simp only [CollatzResearch.WordTrace]
  refine ⟨17813630268592212526498345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23751507024789616701997793 17813630268592212526498345)
  ·
    refine ⟨13360222701444159394873759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17813630268592212526498345 13360222701444159394873759)
    ·
      refine ⟨20040334052166239092310639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13360222701444159394873759 20040334052166239092310639)
      ·
        refine ⟨30060501078249358638465959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20040334052166239092310639 30060501078249358638465959)
        ·
          refine ⟨45090751617374037957698939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30060501078249358638465959 45090751617374037957698939)
          ·
            refine ⟨67636127426061056936548409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45090751617374037957698939 67636127426061056936548409)
            ·
              refine ⟨50727095569545792702411307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67636127426061056936548409 50727095569545792702411307)
              ·
                refine ⟨76090643354318689053616961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50727095569545792702411307 76090643354318689053616961)
                ·
                  refine ⟨57067982515739016790212721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76090643354318689053616961 57067982515739016790212721)
                  ·
                    refine ⟨42800986886804262592659541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57067982515739016790212721 42800986886804262592659541)
                    ·
                      refine ⟨501574065079737452257729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 42800986886804262592659541 501574065079737452257729)
                      ·
                        rfl

theorem cell23_976812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_976812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976812 prefixEnd_976812 := by exact prefixLift 976812
  have htrace : WordTrace (prefixWord ++ tailWord_976812) baseStart_976812 baseEnd_976812 := by
    simpa [prefixWord, tailWord_976812, baseEnd_976812] using wordTrace_append hprefix tailTrace_976812
  have hstable : (prefixWord ++ tailWord_976812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976812).length < 2 ^ (prefixWord ++ tailWord_976812).sum := by decide
  have hdescent : baseEnd_976812 < baseStart_976812 := by decide
  rcases family_descends (prefixWord ++ tailWord_976812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976846 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2]
def baseStart_976846 : Nat := 118140960795 + 976846 * 2 ^ 59
def prefixEnd_976846 : Nat := 4983230072969 + 3 ^ 40 * 976846 * 2
def baseEnd_976846 : Nat := 501591523421990319232573

theorem tailTrace_976846 : CollatzResearch.WordTrace tailWord_976846 prefixEnd_976846 501591523421990319232573 := by
  unfold tailWord_976846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4453562577382656107466799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23752333746040832573156261 4453562577382656107466799)
  ·
    refine ⟨6680343866073984161200199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4453562577382656107466799 6680343866073984161200199)
    ·
      refine ⟨10020515799110976241800299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6680343866073984161200199 10020515799110976241800299)
      ·
        refine ⟨15030773698666464362700449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10020515799110976241800299 15030773698666464362700449)
        ·
          refine ⟨11273080273999848272025337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15030773698666464362700449 11273080273999848272025337)
          ·
            refine ⟨8454810205499886204019003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11273080273999848272025337 8454810205499886204019003)
            ·
              refine ⟨12682215308249829306028505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8454810205499886204019003 12682215308249829306028505)
              ·
                refine ⟨9511661481187371979521379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12682215308249829306028505 9511661481187371979521379)
                ·
                  refine ⟨14267492221781057969282069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9511661481187371979521379 14267492221781057969282069)
                  ·
                    refine ⟨668788697895987092310097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14267492221781057969282069 668788697895987092310097)
                    ·
                      refine ⟨501591523421990319232573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668788697895987092310097 501591523421990319232573)
                      ·
                        rfl

theorem cell23_976846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_976846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976846 prefixEnd_976846 := by exact prefixLift 976846
  have htrace : WordTrace (prefixWord ++ tailWord_976846) baseStart_976846 baseEnd_976846 := by
    simpa [prefixWord, tailWord_976846, baseEnd_976846] using wordTrace_append hprefix tailTrace_976846
  have hstable : (prefixWord ++ tailWord_976846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976846).length < 2 ^ (prefixWord ++ tailWord_976846).sum := by decide
  have hdescent : baseEnd_976846 < baseStart_976846 := by decide
  rcases family_descends (prefixWord ++ tailWord_976846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976896 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 5, 1, 3]
def baseStart_976896 : Nat := 118140960795 + 976896 * 2 ^ 59
def prefixEnd_976896 : Nat := 4983230072969 + 3 ^ 40 * 976896 * 2
def baseEnd_976896 : Nat := 501617197454715123607343

theorem tailTrace_976896 : CollatzResearch.WordTrace tailWord_976896 prefixEnd_976896 501617197454715123607343 := by
  unfold tailWord_976896
  simp only [CollatzResearch.WordTrace]
  refine ⟨17815162134440053699527271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23753549512586738266036361 17815162134440053699527271)
  ·
    refine ⟨26722743201660080549290907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17815162134440053699527271 26722743201660080549290907)
    ·
      refine ⟨40084114802490120823936361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26722743201660080549290907 40084114802490120823936361)
      ·
        refine ⟨30063086101867590617952271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40084114802490120823936361 30063086101867590617952271)
        ·
          refine ⟨45094629152801385926928407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30063086101867590617952271 45094629152801385926928407)
          ·
            refine ⟨67641943729202078890392611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45094629152801385926928407 67641943729202078890392611)
            ·
              refine ⟨101462915593803118335588917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67641943729202078890392611 101462915593803118335588917)
              ·
                refine ⟨9512148336919042343961461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101462915593803118335588917 9512148336919042343961461)
                ·
                  refine ⟨891763906586160219746387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9512148336919042343961461 891763906586160219746387)
                  ·
                    refine ⟨1337645859879240329619581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 891763906586160219746387 1337645859879240329619581)
                    ·
                      refine ⟨501617197454715123607343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1337645859879240329619581 501617197454715123607343)
                      ·
                        rfl

theorem cell23_976896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_976896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976896 prefixEnd_976896 := by exact prefixLift 976896
  have htrace : WordTrace (prefixWord ++ tailWord_976896) baseStart_976896 baseEnd_976896 := by
    simpa [prefixWord, tailWord_976896, baseEnd_976896] using wordTrace_append hprefix tailTrace_976896
  have hstable : (prefixWord ++ tailWord_976896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976896).length < 2 ^ (prefixWord ++ tailWord_976896).sum := by decide
  have hdescent : baseEnd_976896 < baseStart_976896 := by decide
  rcases family_descends (prefixWord ++ tailWord_976896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976899 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 3, 5]
def baseStart_976899 : Nat := 118140960795 + 976899 * 2 ^ 59
def prefixEnd_976899 : Nat := 4983230072969 + 3 ^ 40 * 976899 * 2
def baseEnd_976899 : Nat := 167206245965559537289943

theorem tailTrace_976899 : CollatzResearch.WordTrace tailWord_976899 prefixEnd_976899 167206245965559537289943 := by
  unfold tailWord_976899
  simp only [CollatzResearch.WordTrace]
  refine ⟨35630433687869238911413751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23753622458579492607609167 35630433687869238911413751)
  ·
    refine ⟨53445650531803858367120627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35630433687869238911413751 53445650531803858367120627)
    ·
      refine ⟨80168475797705787550680941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53445650531803858367120627 80168475797705787550680941)
      ·
        refine ⟨30063178424139670331505353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80168475797705787550680941 30063178424139670331505353)
        ·
          refine ⟨22547383818104752748629015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30063178424139670331505353 22547383818104752748629015)
          ·
            refine ⟨33821075727157129122943523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22547383818104752748629015 33821075727157129122943523)
            ·
              refine ⟨50731613590735693684415285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33821075727157129122943523 50731613590735693684415285)
              ·
                refine ⟨4756088774131471282913933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50731613590735693684415285 4756088774131471282913933)
                ·
                  refine ⟨1783533290299301731092725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4756088774131471282913933 1783533290299301731092725)
                  ·
                    refine ⟨167206245965559537289943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1783533290299301731092725 167206245965559537289943)
                    ·
                      rfl

theorem cell23_976899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 5].length) (baseStart_976899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976899 prefixEnd_976899 := by exact prefixLift 976899
  have htrace : WordTrace (prefixWord ++ tailWord_976899) baseStart_976899 baseEnd_976899 := by
    simpa [prefixWord, tailWord_976899, baseEnd_976899] using wordTrace_append hprefix tailTrace_976899
  have hstable : (prefixWord ++ tailWord_976899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976899).length < 2 ^ (prefixWord ++ tailWord_976899).sum := by decide
  have hdescent : baseEnd_976899 < baseStart_976899 := by decide
  rcases family_descends (prefixWord ++ tailWord_976899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976939 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 5]
def baseStart_976939 : Nat := 118140960795 + 976939 * 2 ^ 59
def prefixEnd_976939 : Nat := 4983230072969 + 3 ^ 40 * 976939 * 2
def baseEnd_976939 : Nat := 501639277122858455369645

theorem tailTrace_976939 : CollatzResearch.WordTrace tailWord_976939 prefixEnd_976939 501639277122858455369645 := by
  unfold tailWord_976939
  simp only [CollatzResearch.WordTrace]
  refine ⟨35631892607724325742869871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23754595071816217161913247 35631892607724325742869871)
  ·
    refine ⟨53447838911586488614304807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35631892607724325742869871 53447838911586488614304807)
    ·
      refine ⟨80171758367379732921457211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53447838911586488614304807 80171758367379732921457211)
      ·
        refine ⟨120257637551069599382185817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80171758367379732921457211 120257637551069599382185817)
        ·
          refine ⟨90193228163302199536639363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120257637551069599382185817 90193228163302199536639363)
          ·
            refine ⟨135289842244953299304959045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90193228163302199536639363 135289842244953299304959045)
            ·
              refine ⟨25366845420928743619679821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135289842244953299304959045 25366845420928743619679821)
              ·
                refine ⟨9512567032848278857379933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25366845420928743619679821 9512567032848278857379933)
                ·
                  refine ⟨3567212637318104571517475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9512567032848278857379933 3567212637318104571517475)
                  ·
                    refine ⟨5350818955977156857276213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3567212637318104571517475 5350818955977156857276213)
                    ·
                      refine ⟨501639277122858455369645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5350818955977156857276213 501639277122858455369645)
                      ·
                        rfl

theorem cell23_976939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 5].length) (baseStart_976939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976939 prefixEnd_976939 := by exact prefixLift 976939
  have htrace : WordTrace (prefixWord ++ tailWord_976939) baseStart_976939 baseEnd_976939 := by
    simpa [prefixWord, tailWord_976939, baseEnd_976939] using wordTrace_append hprefix tailTrace_976939
  have hstable : (prefixWord ++ tailWord_976939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976939).length < 2 ^ (prefixWord ++ tailWord_976939).sum := by decide
  have hdescent : baseEnd_976939 < baseStart_976939 := by decide
  rcases family_descends (prefixWord ++ tailWord_976939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976953 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 3, 1, 4]
def baseStart_976953 : Nat := 118140960795 + 976953 * 2 ^ 59
def prefixEnd_976953 : Nat := 4983230072969 + 3 ^ 40 * 976953 * 2
def baseEnd_976953 : Nat := 501646465852021400594581

theorem tailTrace_976953 : CollatzResearch.WordTrace tailWord_976953 prefixEnd_976953 501646465852021400594581 := by
  unfold tailWord_976953
  simp only [CollatzResearch.WordTrace]
  refine ⟨35632403229673606133879513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23754935486449070755919675 35632403229673606133879513)
  ·
    refine ⟨26724302422255204600409635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35632403229673606133879513 26724302422255204600409635)
    ·
      refine ⟨40086453633382806900614453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26724302422255204600409635 40086453633382806900614453)
      ·
        refine ⟨3758105028129638146932605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40086453633382806900614453 3758105028129638146932605)
        ·
          refine ⟨1409289385548614305099727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3758105028129638146932605 1409289385548614305099727)
          ·
            refine ⟨2113934078322921457649591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409289385548614305099727 2113934078322921457649591)
            ·
              refine ⟨3170901117484382186474387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113934078322921457649591 3170901117484382186474387)
              ·
                refine ⟨4756351676226573279711581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3170901117484382186474387 4756351676226573279711581)
                ·
                  refine ⟨1783631878584964979891843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4756351676226573279711581 1783631878584964979891843)
                  ·
                    refine ⟨2675447817877447469837765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1783631878584964979891843 2675447817877447469837765)
                    ·
                      refine ⟨501646465852021400594581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2675447817877447469837765 501646465852021400594581)
                      ·
                        rfl

theorem cell23_976953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_976953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976953 prefixEnd_976953 := by exact prefixLift 976953
  have htrace : WordTrace (prefixWord ++ tailWord_976953) baseStart_976953 baseEnd_976953 := by
    simpa [prefixWord, tailWord_976953, baseEnd_976953] using wordTrace_append hprefix tailTrace_976953
  have hstable : (prefixWord ++ tailWord_976953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976953).length < 2 ^ (prefixWord ++ tailWord_976953).sum := by decide
  have hdescent : baseEnd_976953 < baseStart_976953 := by decide
  rcases family_descends (prefixWord ++ tailWord_976953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976959 : List Nat := [1, 1, 2, 2, 3, 1, 4, 9]
def baseStart_976959 : Nat := 118140960795 + 976959 * 2 ^ 59
def prefixEnd_976959 : Nat := 4983230072969 + 3 ^ 40 * 976959 * 2
def baseEnd_976959 : Nat := 18579612842072162115539

theorem tailTrace_976959 : CollatzResearch.WordTrace tailWord_976959 prefixEnd_976959 18579612842072162115539 := by
  unfold tailWord_976959
  simp only [CollatzResearch.WordTrace]
  refine ⟨35632622067651869158597931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23755081378434579439065287 35632622067651869158597931)
  ·
    refine ⟨53448933101477803737896897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35632622067651869158597931 53448933101477803737896897)
    ·
      refine ⟨40086699826108352803422673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53448933101477803737896897 40086699826108352803422673)
      ·
        refine ⟨30065024869581264602567005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40086699826108352803422673 30065024869581264602567005)
        ·
          refine ⟨11274384326092974225962627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30065024869581264602567005 11274384326092974225962627)
          ·
            refine ⟨16911576489139461338943941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11274384326092974225962627 16911576489139461338943941)
            ·
              refine ⟨3170920591713649001051989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16911576489139461338943941 3170920591713649001051989)
              ·
                refine ⟨18579612842072162115539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3170920591713649001051989 18579612842072162115539)
                ·
                  rfl

theorem cell23_976959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 9].length) (baseStart_976959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976959 prefixEnd_976959 := by exact prefixLift 976959
  have htrace : WordTrace (prefixWord ++ tailWord_976959) baseStart_976959 baseEnd_976959 := by
    simpa [prefixWord, tailWord_976959, baseEnd_976959] using wordTrace_append hprefix tailTrace_976959
  have hstable : (prefixWord ++ tailWord_976959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976959).length < 2 ^ (prefixWord ++ tailWord_976959).sum := by decide
  have hdescent : baseEnd_976959 < baseStart_976959 := by decide
  rcases family_descends (prefixWord ++ tailWord_976959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_976986 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3]
def baseStart_976986 : Nat := 118140960795 + 976986 * 2 ^ 59
def prefixEnd_976986 : Nat := 4983230072969 + 3 ^ 40 * 976986 * 2
def baseEnd_976986 : Nat := 501663410713619771481929

theorem tailTrace_976986 : CollatzResearch.WordTrace tailWord_976986 prefixEnd_976986 501663410713619771481929 := by
  unfold tailWord_976986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8908401709638513192457703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23755737892369368513220541 8908401709638513192457703)
  ·
    refine ⟨13362602564457769788686555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8908401709638513192457703 13362602564457769788686555)
    ·
      refine ⟨20043903846686654683029833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13362602564457769788686555 20043903846686654683029833)
      ·
        refine ⟨15032927885014991012272375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20043903846686654683029833 15032927885014991012272375)
        ·
          refine ⟨22549391827522486518408563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15032927885014991012272375 22549391827522486518408563)
          ·
            refine ⟨33824087741283729777612845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22549391827522486518408563 33824087741283729777612845)
            ·
              refine ⟨12684032902981398666604817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33824087741283729777612845 12684032902981398666604817)
              ·
                refine ⟨9513024677236048999953613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12684032902981398666604817 9513024677236048999953613)
                ·
                  refine ⟨3567384253963518374982605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9513024677236048999953613 3567384253963518374982605)
                  ·
                    refine ⟨1337769095236319390618477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3567384253963518374982605 1337769095236319390618477)
                    ·
                      refine ⟨501663410713619771481929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1337769095236319390618477 501663410713619771481929)
                      ·
                        rfl

theorem cell23_976986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_976986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_976986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_976986 prefixEnd_976986 := by exact prefixLift 976986
  have htrace : WordTrace (prefixWord ++ tailWord_976986) baseStart_976986 baseEnd_976986 := by
    simpa [prefixWord, tailWord_976986, baseEnd_976986] using wordTrace_append hprefix tailTrace_976986
  have hstable : (prefixWord ++ tailWord_976986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_976986).length < 2 ^ (prefixWord ++ tailWord_976986).sum := by decide
  have hdescent : baseEnd_976986 < baseStart_976986 := by decide
  rcases family_descends (prefixWord ++ tailWord_976986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977006 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_977006 : Nat := 118140960795 + 977006 * 2 ^ 59
def prefixEnd_977006 : Nat := 4983230072969 + 3 ^ 40 * 977006 * 2
def baseEnd_977006 : Nat := 167224560108903231077279

theorem tailTrace_977006 : CollatzResearch.WordTrace tailWord_977006 prefixEnd_977006 167224560108903231077279 := by
  unfold tailWord_977006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4454292037310199523194859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23756224198987730790372581 4454292037310199523194859)
  ·
    refine ⟨6681438055965299284792289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4454292037310199523194859 6681438055965299284792289)
    ·
      refine ⟨5011078541973974463594217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6681438055965299284792289 5011078541973974463594217)
      ·
        refine ⟨3758308906480480847695663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5011078541973974463594217 3758308906480480847695663)
        ·
          refine ⟨5637463359720721271543495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3758308906480480847695663 5637463359720721271543495)
          ·
            refine ⟨8456195039581081907315243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5637463359720721271543495 8456195039581081907315243)
            ·
              refine ⟨12684292559371622860972865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8456195039581081907315243 12684292559371622860972865)
              ·
                refine ⟨9513219419528717145729649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12684292559371622860972865 9513219419528717145729649)
                ·
                  refine ⟨7134914564646537859297237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9513219419528717145729649 7134914564646537859297237)
                  ·
                    refine ⟨167224560108903231077279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7134914564646537859297237 167224560108903231077279)
                    ·
                      rfl

theorem cell23_977006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_977006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977006 prefixEnd_977006 := by exact prefixLift 977006
  have htrace : WordTrace (prefixWord ++ tailWord_977006) baseStart_977006 baseEnd_977006 := by
    simpa [prefixWord, tailWord_977006, baseEnd_977006] using wordTrace_append hprefix tailTrace_977006
  have hstable : (prefixWord ++ tailWord_977006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977006).length < 2 ^ (prefixWord ++ tailWord_977006).sum := by decide
  have hdescent : baseEnd_977006 < baseStart_977006 := by decide
  rcases family_descends (prefixWord ++ tailWord_977006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977054 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_977054 : Nat := 118140960795 + 977054 * 2 ^ 59
def prefixEnd_977054 : Nat := 4983230072969 + 3 ^ 40 * 977054 * 2
def baseEnd_977054 : Nat := 501698327398125505431617

theorem tailTrace_977054 : CollatzResearch.WordTrace tailWord_977054 prefixEnd_977054 501698327398125505431617 := by
  unfold tailWord_977054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4454510875288462547913277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23757391334871800255537477 4454510875288462547913277)
  ·
    refine ⟨1670441578233173455467479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4454510875288462547913277 1670441578233173455467479)
    ·
      refine ⟨2505662367349760183201219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1670441578233173455467479 2505662367349760183201219)
      ·
        refine ⟨3758493551024640274801829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505662367349760183201219 3758493551024640274801829)
        ·
          refine ⟨704717540817120051525343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3758493551024640274801829 704717540817120051525343)
          ·
            refine ⟨1057076311225680077288015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704717540817120051525343 1057076311225680077288015)
            ·
              refine ⟨1585614466838520115932023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057076311225680077288015 1585614466838520115932023)
              ·
                refine ⟨2378421700257780173898035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585614466838520115932023 2378421700257780173898035)
                ·
                  refine ⟨3567632550386670260847053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2378421700257780173898035 3567632550386670260847053)
                  ·
                    refine ⟨1337862206395001347817645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3567632550386670260847053 1337862206395001347817645)
                    ·
                      refine ⟨501698327398125505431617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1337862206395001347817645 501698327398125505431617)
                      ·
                        rfl

theorem cell23_977054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_977054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977054 prefixEnd_977054 := by exact prefixLift 977054
  have htrace : WordTrace (prefixWord ++ tailWord_977054) baseStart_977054 baseEnd_977054 := by
    simpa [prefixWord, tailWord_977054, baseEnd_977054] using wordTrace_append hprefix tailTrace_977054
  have hstable : (prefixWord ++ tailWord_977054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977054).length < 2 ^ (prefixWord ++ tailWord_977054).sum := by decide
  have hdescent : baseEnd_977054 < baseStart_977054 := by decide
  rcases family_descends (prefixWord ++ tailWord_977054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977103 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 2, 5, 2]
def baseStart_977103 : Nat := 118140960795 + 977103 * 2 ^ 59
def prefixEnd_977103 : Nat := 4983230072969 + 3 ^ 40 * 977103 * 2
def baseEnd_977103 : Nat := 501723487950195813718891

theorem tailTrace_977103 : CollatzResearch.WordTrace tailWord_977103 prefixEnd_977103 501723487950195813718891 := by
  unfold tailWord_977103
  simp only [CollatzResearch.WordTrace]
  refine ⟨35637874179130181751839963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23758582786086787834559975 35637874179130181751839963)
  ·
    refine ⟨53456811268695272627759945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35637874179130181751839963 53456811268695272627759945)
    ·
      refine ⟨40092608451521454470819959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53456811268695272627759945 40092608451521454470819959)
      ·
        refine ⟨60138912677282181706229939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40092608451521454470819959 60138912677282181706229939)
        ·
          refine ⟨90208369015923272559344909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60138912677282181706229939 90208369015923272559344909)
          ·
            refine ⟨33828138380971227209754341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90208369015923272559344909 33828138380971227209754341)
            ·
              refine ⟨6342775946432105101828939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33828138380971227209754341 6342775946432105101828939)
              ·
                refine ⟨9514163919648157652743409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6342775946432105101828939 9514163919648157652743409)
                ·
                  refine ⟨7135622939736118239557557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9514163919648157652743409 7135622939736118239557557)
                  ·
                    refine ⟨668964650600261084958521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7135622939736118239557557 668964650600261084958521)
                    ·
                      refine ⟨501723487950195813718891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 668964650600261084958521 501723487950195813718891)
                      ·
                        rfl

theorem cell23_977103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 5, 2].length) (baseStart_977103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977103 prefixEnd_977103 := by exact prefixLift 977103
  have htrace : WordTrace (prefixWord ++ tailWord_977103) baseStart_977103 baseEnd_977103 := by
    simpa [prefixWord, tailWord_977103, baseEnd_977103] using wordTrace_append hprefix tailTrace_977103
  have hstable : (prefixWord ++ tailWord_977103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977103).length < 2 ^ (prefixWord ++ tailWord_977103).sum := by decide
  have hdescent : baseEnd_977103 < baseStart_977103 := by decide
  rcases family_descends (prefixWord ++ tailWord_977103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977150 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_977150 : Nat := 118140960795 + 977150 * 2 ^ 59
def prefixEnd_977150 : Nat := 4983230072969 + 3 ^ 40 * 977150 * 2
def baseEnd_977150 : Nat := 501747621540957129831175

theorem tailTrace_977150 : CollatzResearch.WordTrace tailWord_977150 prefixEnd_977150 501747621540957129831175 := by
  unfold tailWord_977150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4454948551244988597350113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23759725606639939185867269 4454948551244988597350113)
  ·
    refine ⟨3341211413433741448012585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4454948551244988597350113 3341211413433741448012585)
    ·
      refine ⟨2505908560075306086009439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3341211413433741448012585 2505908560075306086009439)
      ·
        refine ⟨3758862840112959129014159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505908560075306086009439 3758862840112959129014159)
        ·
          refine ⟨5638294260169438693521239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3758862840112959129014159 5638294260169438693521239)
          ·
            refine ⟨8457441390254158040281859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5638294260169438693521239 8457441390254158040281859)
            ·
              refine ⟨12686162085381237060422789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8457441390254158040281859 12686162085381237060422789)
              ·
                refine ⟨2378655391008981948829273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12686162085381237060422789 2378655391008981948829273)
                ·
                  refine ⟨1783991543256736461621955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2378655391008981948829273 1783991543256736461621955)
                  ·
                    refine ⟨2675987314885104692432933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1783991543256736461621955 2675987314885104692432933)
                    ·
                      refine ⟨501747621540957129831175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2675987314885104692432933 501747621540957129831175)
                      ·
                        rfl

theorem cell23_977150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_977150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977150 prefixEnd_977150 := by exact prefixLift 977150
  have htrace : WordTrace (prefixWord ++ tailWord_977150) baseStart_977150 baseEnd_977150 := by
    simpa [prefixWord, tailWord_977150, baseEnd_977150] using wordTrace_append hprefix tailTrace_977150
  have hstable : (prefixWord ++ tailWord_977150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977150).length < 2 ^ (prefixWord ++ tailWord_977150).sum := by decide
  have hdescent : baseEnd_977150 < baseStart_977150 := by decide
  rcases family_descends (prefixWord ++ tailWord_977150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977173 : List Nat := [1, 3, 2, 1, 2, 1, 4, 3, 6]
def baseStart_977173 : Nat := 118140960795 + 977173 * 2 ^ 59
def prefixEnd_977173 : Nat := 4983230072969 + 3 ^ 40 * 977173 * 2
def baseEnd_977173 : Nat := 55751047955112282204841

theorem tailTrace_977173 : CollatzResearch.WordTrace tailWord_977173 prefixEnd_977173 55751047955112282204841 := by
  unfold tailWord_977173
  simp only [CollatzResearch.WordTrace]
  refine ⟨35640427288876583706888173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23760284859251055804592115 35640427288876583706888173)
  ·
    refine ⟨13365160233328718890083065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35640427288876583706888173 13365160233328718890083065)
    ·
      refine ⟨10023870174996539167562299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13365160233328718890083065 10023870174996539167562299)
      ·
        refine ⟨15035805262494808751343449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10023870174996539167562299 15035805262494808751343449)
        ·
          refine ⟨11276853946871106563507587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15035805262494808751343449 11276853946871106563507587)
          ·
            refine ⟨16915280920306659845261381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11276853946871106563507587 16915280920306659845261381)
            ·
              refine ⟨3171615172557498720986509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16915280920306659845261381 3171615172557498720986509)
              ·
                refine ⟨1189355689709062020369941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3171615172557498720986509 1189355689709062020369941)
                ·
                  refine ⟨55751047955112282204841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1189355689709062020369941 55751047955112282204841)
                  ·
                    rfl

theorem cell23_977173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 6].length) (baseStart_977173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977173 prefixEnd_977173 := by exact prefixLift 977173
  have htrace : WordTrace (prefixWord ++ tailWord_977173) baseStart_977173 baseEnd_977173 := by
    simpa [prefixWord, tailWord_977173, baseEnd_977173] using wordTrace_append hprefix tailTrace_977173
  have hstable : (prefixWord ++ tailWord_977173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977173).length < 2 ^ (prefixWord ++ tailWord_977173).sum := by decide
  have hdescent : baseEnd_977173 < baseStart_977173 := by decide
  rcases family_descends (prefixWord ++ tailWord_977173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977237 : List Nat := [1, 3, 2, 2, 4, 1, 2, 2, 1, 5]
def baseStart_977237 : Nat := 118140960795 + 977237 * 2 ^ 59
def prefixEnd_977237 : Nat := 4983230072969 + 3 ^ 40 * 977237 * 2
def baseEnd_977237 : Nat := 167264098119299429814425

theorem tailTrace_977237 : CollatzResearch.WordTrace tailWord_977237 prefixEnd_977237 167264098119299429814425 := by
  unfold tailWord_977237
  simp only [CollatzResearch.WordTrace]
  refine ⟨35642761560644722637217965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23761841040429815091478643 35642761560644722637217965)
  ·
    refine ⟨13366035585241770988956737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35642761560644722637217965 13366035585241770988956737)
    ·
      refine ⟨10024526688931328241717553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13366035585241770988956737 10024526688931328241717553)
      ·
        refine ⟨7518395016698496181288165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10024526688931328241717553 7518395016698496181288165)
        ·
          refine ⟨1409699065630968033991531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7518395016698496181288165 1409699065630968033991531)
          ·
            refine ⟨2114548598446452050987297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409699065630968033991531 2114548598446452050987297)
            ·
              refine ⟨1585911448834839038240473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2114548598446452050987297 1585911448834839038240473)
              ·
                refine ⟨1189433586626129278680355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1585911448834839038240473 1189433586626129278680355)
                ·
                  refine ⟨1784150379939193918020533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1189433586626129278680355 1784150379939193918020533)
                  ·
                    refine ⟨167264098119299429814425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1784150379939193918020533 167264098119299429814425)
                    ·
                      rfl

theorem cell23_977237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_977237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977237 prefixEnd_977237 := by exact prefixLift 977237
  have htrace : WordTrace (prefixWord ++ tailWord_977237) baseStart_977237 baseEnd_977237 := by
    simpa [prefixWord, tailWord_977237, baseEnd_977237] using wordTrace_append hprefix tailTrace_977237
  have hstable : (prefixWord ++ tailWord_977237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977237).length < 2 ^ (prefixWord ++ tailWord_977237).sum := by decide
  have hdescent : baseEnd_977237 < baseStart_977237 := by decide
  rcases family_descends (prefixWord ++ tailWord_977237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977294 : List Nat := [4, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3]
def baseStart_977294 : Nat := 118140960795 + 977294 * 2 ^ 59
def prefixEnd_977294 : Nat := 4983230072969 + 3 ^ 40 * 977294 * 2
def baseEnd_977294 : Nat := 501821562755204566430513

theorem tailTrace_977294 : CollatzResearch.WordTrace tailWord_977294 prefixEnd_977294 501821562755204566430513 := by
  unfold tailWord_977294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4455605065179777671505367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23763227014292147581361957 4455605065179777671505367)
  ·
    refine ⟨6683407597769666507258051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4455605065179777671505367 6683407597769666507258051)
    ·
      refine ⟨10025111396654499760887077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6683407597769666507258051 10025111396654499760887077)
      ·
        refine ⟨1879708386872718705166327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10025111396654499760887077 1879708386872718705166327)
        ·
          refine ⟨2819562580309078057749491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1879708386872718705166327 2819562580309078057749491)
          ·
            refine ⟨4229343870463617086624237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819562580309078057749491 4229343870463617086624237)
            ·
              refine ⟨1586003951423856407484089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4229343870463617086624237 1586003951423856407484089)
              ·
                refine ⟨1189502963567892305613067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1586003951423856407484089 1189502963567892305613067)
                ·
                  refine ⟨1784254445351838458419601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1189502963567892305613067 1784254445351838458419601)
                  ·
                    refine ⟨1338190834013878843814701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1784254445351838458419601 1338190834013878843814701)
                    ·
                      refine ⟨501821562755204566430513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1338190834013878843814701 501821562755204566430513)
                      ·
                        rfl

theorem cell23_977294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_977294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977294 prefixEnd_977294 := by exact prefixLift 977294
  have htrace : WordTrace (prefixWord ++ tailWord_977294) baseStart_977294 baseEnd_977294 := by
    simpa [prefixWord, tailWord_977294, baseEnd_977294] using wordTrace_append hprefix tailTrace_977294
  have hstable : (prefixWord ++ tailWord_977294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977294).length < 2 ^ (prefixWord ++ tailWord_977294).sum := by decide
  have hdescent : baseEnd_977294 < baseStart_977294 := by decide
  rcases family_descends (prefixWord ++ tailWord_977294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977303 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_977303 : Nat := 118140960795 + 977303 * 2 ^ 59
def prefixEnd_977303 : Nat := 4983230072969 + 3 ^ 40 * 977303 * 2
def baseEnd_977303 : Nat := 501826184081095031217971

theorem tailTrace_977303 : CollatzResearch.WordTrace tailWord_977303 prefixEnd_977303 501826184081095031217971 := by
  unfold tailWord_977303
  simp only [CollatzResearch.WordTrace]
  refine ⟨35645168778405615909120563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23763445852270410606080375 35645168778405615909120563)
  ·
    refine ⟨53467753167608423863680845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35645168778405615909120563 53467753167608423863680845)
    ·
      refine ⟨20050407437853158948880317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53467753167608423863680845 20050407437853158948880317)
      ·
        refine ⟨7518902789194934605830119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20050407437853158948880317 7518902789194934605830119)
        ·
          refine ⟨11278354183792401908745179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7518902789194934605830119 11278354183792401908745179)
          ·
            refine ⟨16917531275688602863117769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11278354183792401908745179 16917531275688602863117769)
            ·
              refine ⟨12688148456766452147338327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16917531275688602863117769 12688148456766452147338327)
              ·
                refine ⟨19032222685149678221007491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12688148456766452147338327 19032222685149678221007491)
                ·
                  refine ⟨28548334027724517331511237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19032222685149678221007491 28548334027724517331511237)
                  ·
                    refine ⟨5352812630198346999658357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28548334027724517331511237 5352812630198346999658357)
                    ·
                      refine ⟨501826184081095031217971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5352812630198346999658357 501826184081095031217971)
                      ·
                        rfl

theorem cell23_977303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_977303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977303 prefixEnd_977303 := by exact prefixLift 977303
  have htrace : WordTrace (prefixWord ++ tailWord_977303) baseStart_977303 baseEnd_977303 := by
    simpa [prefixWord, tailWord_977303, baseEnd_977303] using wordTrace_append hprefix tailTrace_977303
  have hstable : (prefixWord ++ tailWord_977303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977303).length < 2 ^ (prefixWord ++ tailWord_977303).sum := by decide
  have hdescent : baseEnd_977303 < baseStart_977303 := by decide
  rcases family_descends (prefixWord ++ tailWord_977303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977340 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 1, 8]
def baseStart_977340 : Nat := 118140960795 + 977340 * 2 ^ 59
def prefixEnd_977340 : Nat := 4983230072969 + 3 ^ 40 * 977340 * 2
def baseEnd_977340 : Nat := 167281727621770462151767

theorem tailTrace_977340 : CollatzResearch.WordTrace tailWord_977340 prefixEnd_977340 167281727621770462151767 := by
  unfold tailWord_977340
  simp only [CollatzResearch.WordTrace]
  refine ⟨17823259139635785614108737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23764345519514380818811649 17823259139635785614108737)
  ·
    refine ⟨13367444354726839210581553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17823259139635785614108737 13367444354726839210581553)
    ·
      refine ⟨10025583266045129407936165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13367444354726839210581553 10025583266045129407936165)
      ·
        refine ⟨1879796862383461763988031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10025583266045129407936165 1879796862383461763988031)
        ·
          refine ⟨2819695293575192645982047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1879796862383461763988031 2819695293575192645982047)
          ·
            refine ⟨4229542940362788968973071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819695293575192645982047 4229542940362788968973071)
            ·
              refine ⟨6344314410544183453459607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4229542940362788968973071 6344314410544183453459607)
              ·
                refine ⟨9516471615816275180189411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6344314410544183453459607 9516471615816275180189411)
                ·
                  refine ⟨14274707423724412770284117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9516471615816275180189411 14274707423724412770284117)
                  ·
                    refine ⟨167281727621770462151767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14274707423724412770284117 167281727621770462151767)
                    ·
                      rfl

theorem cell23_977340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_977340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977340 prefixEnd_977340 := by exact prefixLift 977340
  have htrace : WordTrace (prefixWord ++ tailWord_977340) baseStart_977340 baseEnd_977340 := by
    simpa [prefixWord, tailWord_977340, baseEnd_977340] using wordTrace_append hprefix tailTrace_977340
  have hstable : (prefixWord ++ tailWord_977340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977340).length < 2 ^ (prefixWord ++ tailWord_977340).sum := by decide
  have hdescent : baseEnd_977340 < baseStart_977340 := by decide
  rcases family_descends (prefixWord ++ tailWord_977340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977347 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 6, 2, 2]
def baseStart_977347 : Nat := 118140960795 + 977347 * 2 ^ 59
def prefixEnd_977347 : Nat := 4983230072969 + 3 ^ 40 * 977347 * 2
def baseEnd_977347 : Nat := 501848777229892859067769

theorem tailTrace_977347 : CollatzResearch.WordTrace tailWord_977347 prefixEnd_977347 501848777229892859067769 := by
  unfold tailWord_977347
  simp only [CollatzResearch.WordTrace]
  refine ⟨35646773590246211423722295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23764515726830807615814863 35646773590246211423722295)
  ·
    refine ⟨53470160385369317135583443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35646773590246211423722295 53470160385369317135583443)
    ·
      refine ⟨80205240578053975703375165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53470160385369317135583443 80205240578053975703375165)
      ·
        refine ⟨30076965216770240888765687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80205240578053975703375165 30076965216770240888765687)
        ·
          refine ⟨45115447825155361333148531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30076965216770240888765687 45115447825155361333148531)
          ·
            refine ⟨67673171737733041999722797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45115447825155361333148531 67673171737733041999722797)
            ·
              refine ⟨25377439401649890749896049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67673171737733041999722797 25377439401649890749896049)
              ·
                refine ⟨19033079551237418062422037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25377439401649890749896049 19033079551237418062422037)
                ·
                  refine ⟨892175603964253971676033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19033079551237418062422037 892175603964253971676033)
                  ·
                    refine ⟨669131702973190478757025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 892175603964253971676033 669131702973190478757025)
                    ·
                      refine ⟨501848777229892859067769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669131702973190478757025 501848777229892859067769)
                      ·
                        rfl

theorem cell23_977347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 2, 2].length) (baseStart_977347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977347 prefixEnd_977347 := by exact prefixLift 977347
  have htrace : WordTrace (prefixWord ++ tailWord_977347) baseStart_977347 baseEnd_977347 := by
    simpa [prefixWord, tailWord_977347, baseEnd_977347] using wordTrace_append hprefix tailTrace_977347
  have hstable : (prefixWord ++ tailWord_977347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977347).length < 2 ^ (prefixWord ++ tailWord_977347).sum := by decide
  have hdescent : baseEnd_977347 < baseStart_977347 := by decide
  rcases family_descends (prefixWord ++ tailWord_977347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977353 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 9]
def baseStart_977353 : Nat := 118140960795 + 977353 * 2 ^ 59
def prefixEnd_977353 : Nat := 4983230072969 + 3 ^ 40 * 977353 * 2
def baseEnd_977353 : Nat := 55761317568202203954749

theorem tailTrace_977353 : CollatzResearch.WordTrace tailWord_977353 prefixEnd_977353 55761317568202203954749 := by
  unfold tailWord_977353
  simp only [CollatzResearch.WordTrace]
  refine ⟨35646992428224474448440713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23764661618816316298960475 35646992428224474448440713)
  ·
    refine ⟨26735244321168355836330535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35646992428224474448440713 26735244321168355836330535)
    ·
      refine ⟨40102866481752533754495803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26735244321168355836330535 40102866481752533754495803)
      ·
        refine ⟨60154299722628800631743705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40102866481752533754495803 60154299722628800631743705)
        ·
          refine ⟨45115724791971600473807779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60154299722628800631743705 45115724791971600473807779)
          ·
            refine ⟨67673587187957400710711669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45115724791971600473807779 67673587187957400710711669)
            ·
              refine ⟨6344398798871006316629219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67673587187957400710711669 6344398798871006316629219)
              ·
                refine ⟨9516598198306509474943829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6344398798871006316629219 9516598198306509474943829)
                ·
                  refine ⟨55761317568202203954749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9516598198306509474943829 55761317568202203954749)
                  ·
                    rfl

theorem cell23_977353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 9].length) (baseStart_977353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977353 prefixEnd_977353 := by exact prefixLift 977353
  have htrace : WordTrace (prefixWord ++ tailWord_977353) baseStart_977353 baseEnd_977353 := by
    simpa [prefixWord, tailWord_977353, baseEnd_977353] using wordTrace_append hprefix tailTrace_977353
  have hstable : (prefixWord ++ tailWord_977353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977353).length < 2 ^ (prefixWord ++ tailWord_977353).sum := by decide
  have hdescent : baseEnd_977353 < baseStart_977353 := by decide
  rcases family_descends (prefixWord ++ tailWord_977353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977364 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_977364 : Nat := 118140960795 + 977364 * 2 ^ 59
def prefixEnd_977364 : Nat := 4983230072969 + 3 ^ 40 * 977364 * 2
def baseEnd_977364 : Nat := 501857506401019292555191

theorem tailTrace_977364 : CollatzResearch.WordTrace tailWord_977364 prefixEnd_977364 501857506401019292555191 := by
  unfold tailWord_977364
  simp only [CollatzResearch.WordTrace]
  refine ⟨17823696815592311663545573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23764929087456415551394097 17823696815592311663545573)
  ·
    refine ⟨3341943152923558436914795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17823696815592311663545573 3341943152923558436914795)
    ·
      refine ⟨5012914729385337655372193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3341943152923558436914795 5012914729385337655372193)
      ·
        refine ⟨3759686047039003241529145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5012914729385337655372193 3759686047039003241529145)
        ·
          refine ⟨2819764535279252431146859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3759686047039003241529145 2819764535279252431146859)
          ·
            refine ⟨4229646802918878646720289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819764535279252431146859 4229646802918878646720289)
            ·
              refine ⟨3172235102189158985040217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4229646802918878646720289 3172235102189158985040217)
              ·
                refine ⟨2379176326641869238780163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3172235102189158985040217 2379176326641869238780163)
                ·
                  refine ⟨3568764489962803858170245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2379176326641869238780163 3568764489962803858170245)
                  ·
                    refine ⟨669143341868025723406921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3568764489962803858170245 669143341868025723406921)
                    ·
                      refine ⟨501857506401019292555191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669143341868025723406921 501857506401019292555191)
                      ·
                        rfl

theorem cell23_977364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_977364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977364 prefixEnd_977364 := by exact prefixLift 977364
  have htrace : WordTrace (prefixWord ++ tailWord_977364) baseStart_977364 baseEnd_977364 := by
    simpa [prefixWord, tailWord_977364, baseEnd_977364] using wordTrace_append hprefix tailTrace_977364
  have hstable : (prefixWord ++ tailWord_977364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977364).length < 2 ^ (prefixWord ++ tailWord_977364).sum := by decide
  have hdescent : baseEnd_977364 < baseStart_977364 := by decide
  rcases family_descends (prefixWord ++ tailWord_977364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977381 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 4, 2, 2]
def baseStart_977381 : Nat := 118140960795 + 977381 * 2 ^ 59
def prefixEnd_977381 : Nat := 4983230072969 + 3 ^ 40 * 977381 * 2
def baseEnd_977381 : Nat := 501866235572145726042613

theorem tailTrace_977381 : CollatzResearch.WordTrace tailWord_977381 prefixEnd_977381 501866235572145726042613 := by
  unfold tailWord_977381
  simp only [CollatzResearch.WordTrace]
  refine ⟨35648013672123035230459997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23765342448082023486973331 35648013672123035230459997)
  ·
    refine ⟨13368005127046138211422499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35648013672123035230459997 13368005127046138211422499)
    ·
      refine ⟨20052007690569207317133749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13368005127046138211422499 20052007690569207317133749)
      ·
        refine ⟨1879875720990863185981289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20052007690569207317133749 1879875720990863185981289)
        ·
          refine ⟨1409906790743147389485967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1879875720990863185981289 1409906790743147389485967)
          ·
            refine ⟨2114860186114721084228951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409906790743147389485967 2114860186114721084228951)
            ·
              refine ⟨3172290279172081626343427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114860186114721084228951 3172290279172081626343427)
              ·
                refine ⟨4758435418758122439515141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3172290279172081626343427 4758435418758122439515141)
                ·
                  refine ⟨892206641017147957409089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4758435418758122439515141 892206641017147957409089)
                  ·
                    refine ⟨669154980762860968056817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 892206641017147957409089 669154980762860968056817)
                    ·
                      refine ⟨501866235572145726042613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669154980762860968056817 501866235572145726042613)
                      ·
                        rfl

theorem cell23_977381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_977381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977381 prefixEnd_977381 := by exact prefixLift 977381
  have htrace : WordTrace (prefixWord ++ tailWord_977381) baseStart_977381 baseEnd_977381 := by
    simpa [prefixWord, tailWord_977381, baseEnd_977381] using wordTrace_append hprefix tailTrace_977381
  have hstable : (prefixWord ++ tailWord_977381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977381).length < 2 ^ (prefixWord ++ tailWord_977381).sum := by decide
  have hdescent : baseEnd_977381 < baseStart_977381 := by decide
  rcases family_descends (prefixWord ++ tailWord_977381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977398 : List Nat := [5, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_977398 : Nat := 118140960795 + 977398 * 2 ^ 59
def prefixEnd_977398 : Nat := 4983230072969 + 3 ^ 40 * 977398 * 2
def baseEnd_977398 : Nat := 501874964743272159530035

theorem tailTrace_977398 : CollatzResearch.WordTrace tailWord_977398 prefixEnd_977398 501874964743272159530035 := by
  unfold tailWord_977398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2228039607066340445864303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23765755808707631422552565 2228039607066340445864303)
  ·
    refine ⟨3342059410599510668796455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2228039607066340445864303 3342059410599510668796455)
    ·
      refine ⟨5013089115899266003194683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3342059410599510668796455 5013089115899266003194683)
      ·
        refine ⟨7519633673848899004792025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5013089115899266003194683 7519633673848899004792025)
        ·
          refine ⟨5639725255386674253594019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7519633673848899004792025 5639725255386674253594019)
          ·
            refine ⟨8459587883080011380391029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5639725255386674253594019 8459587883080011380391029)
            ·
              refine ⟨793086364038751066911659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8459587883080011380391029 793086364038751066911659)
              ·
                refine ⟨1189629546058126600367489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793086364038751066911659 1189629546058126600367489)
                ·
                  refine ⟨892222159543594950275617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1189629546058126600367489 892222159543594950275617)
                  ·
                    refine ⟨669166619657696212706713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 892222159543594950275617 669166619657696212706713)
                    ·
                      refine ⟨501874964743272159530035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669166619657696212706713 501874964743272159530035)
                      ·
                        rfl

theorem cell23_977398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_977398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977398 prefixEnd_977398 := by exact prefixLift 977398
  have htrace : WordTrace (prefixWord ++ tailWord_977398) baseStart_977398 baseEnd_977398 := by
    simpa [prefixWord, tailWord_977398, baseEnd_977398] using wordTrace_append hprefix tailTrace_977398
  have hstable : (prefixWord ++ tailWord_977398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977398).length < 2 ^ (prefixWord ++ tailWord_977398).sum := by decide
  have hdescent : baseEnd_977398 < baseStart_977398 := by decide
  rcases family_descends (prefixWord ++ tailWord_977398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977437 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_977437 : Nat := 118140960795 + 977437 * 2 ^ 59
def prefixEnd_977437 : Nat := 4983230072969 + 3 ^ 40 * 977437 * 2
def baseEnd_977437 : Nat := 501894990488797506942355

theorem tailTrace_977437 : CollatzResearch.WordTrace tailWord_977437 prefixEnd_977437 501894990488797506942355 := by
  unfold tailWord_977437
  simp only [CollatzResearch.WordTrace]
  refine ⟨35650056159920156794498565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23766704106613437862999043 35650056159920156794498565)
  ·
    refine ⟨6684385529985029398968481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35650056159920156794498565 6684385529985029398968481)
    ·
      refine ⟨5013289147488772049226361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6684385529985029398968481 5013289147488772049226361)
      ·
        refine ⟨3759966860616579036919771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5013289147488772049226361 3759966860616579036919771)
        ·
          refine ⟨5639950290924868555379657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3759966860616579036919771 5639950290924868555379657)
          ·
            refine ⟨4229962718193651416534743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5639950290924868555379657 4229962718193651416534743)
            ·
              refine ⟨6344944077290477124802115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4229962718193651416534743 6344944077290477124802115)
              ·
                refine ⟨9517416115935715687203173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6344944077290477124802115 9517416115935715687203173)
                ·
                  refine ⟨1784515521737946691350595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9517416115935715687203173 1784515521737946691350595)
                  ·
                    refine ⟨2676773282606920037025893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1784515521737946691350595 2676773282606920037025893)
                    ·
                      refine ⟨501894990488797506942355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2676773282606920037025893 501894990488797506942355)
                      ·
                        rfl

theorem cell23_977437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_977437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977437 prefixEnd_977437 := by exact prefixLift 977437
  have htrace : WordTrace (prefixWord ++ tailWord_977437) baseStart_977437 baseEnd_977437 := by
    simpa [prefixWord, tailWord_977437, baseEnd_977437] using wordTrace_append hprefix tailTrace_977437
  have hstable : (prefixWord ++ tailWord_977437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977437).length < 2 ^ (prefixWord ++ tailWord_977437).sum := by decide
  have hdescent : baseEnd_977437 < baseStart_977437 := by decide
  rcases family_descends (prefixWord ++ tailWord_977437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977444 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 1, 2, 5]
def baseStart_977444 : Nat := 118140960795 + 977444 * 2 ^ 59
def prefixEnd_977444 : Nat := 4983230072969 + 3 ^ 40 * 977444 * 2
def baseEnd_977444 : Nat := 501898584853378979554823

theorem tailTrace_977444 : CollatzResearch.WordTrace tailWord_977444 prefixEnd_977444 501898584853378979554823 := by
  unfold tailWord_977444
  simp only [CollatzResearch.WordTrace]
  refine ⟨17825155735447398495001693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23766874313929864660002257 17825155735447398495001693)
  ·
    refine ⟨6684433400792774435625635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17825155735447398495001693 6684433400792774435625635)
    ·
      refine ⟨10026650101189161653438453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6684433400792774435625635 10026650101189161653438453)
      ·
        refine ⟨939998446986483905009855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10026650101189161653438453 939998446986483905009855)
        ·
          refine ⟨1409997670479725857514783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939998446986483905009855 1409997670479725857514783)
          ·
            refine ⟨2114996505719588786272175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409997670479725857514783 2114996505719588786272175)
            ·
              refine ⟨3172494758579383179408263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114996505719588786272175 3172494758579383179408263)
              ·
                refine ⟨4758742137869074769112395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3172494758579383179408263 4758742137869074769112395)
                ·
                  refine ⟨7138113206803612153668593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4758742137869074769112395 7138113206803612153668593)
                  ·
                    refine ⟨5353584905102709115251445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7138113206803612153668593 5353584905102709115251445)
                    ·
                      refine ⟨501898584853378979554823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5353584905102709115251445 501898584853378979554823)
                      ·
                        rfl

theorem cell23_977444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_977444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977444 prefixEnd_977444 := by exact prefixLift 977444
  have htrace : WordTrace (prefixWord ++ tailWord_977444) baseStart_977444 baseEnd_977444 := by
    simpa [prefixWord, tailWord_977444, baseEnd_977444] using wordTrace_append hprefix tailTrace_977444
  have hstable : (prefixWord ++ tailWord_977444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977444).length < 2 ^ (prefixWord ++ tailWord_977444).sum := by decide
  have hdescent : baseEnd_977444 < baseStart_977444 := by decide
  rcases family_descends (prefixWord ++ tailWord_977444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977497 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 5, 5, 2]
def baseStart_977497 : Nat := 118140960795 + 977497 * 2 ^ 59
def prefixEnd_977497 : Nat := 4983230072969 + 3 ^ 40 * 977497 * 2
def baseEnd_977497 : Nat := 501925799328067272192079

theorem tailTrace_977497 : CollatzResearch.WordTrace tailWord_977497 prefixEnd_977497 501925799328067272192079 := by
  unfold tailWord_977497
  simp only [CollatzResearch.WordTrace]
  refine ⟨35652244539702787041682745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23768163026468524694455163 35652244539702787041682745)
  ·
    refine ⟨26739183404777090281262059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35652244539702787041682745 26739183404777090281262059)
    ·
      refine ⟨40108775107165635421893089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26739183404777090281262059 40108775107165635421893089)
      ·
        refine ⟨30081581330374226566419817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40108775107165635421893089 30081581330374226566419817)
        ·
          refine ⟨22561185997780669924814863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30081581330374226566419817 22561185997780669924814863)
          ·
            refine ⟨33841778996671004887222295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22561185997780669924814863 33841778996671004887222295)
            ·
              refine ⟨50762668495006507330833443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33841778996671004887222295 50762668495006507330833443)
              ·
                refine ⟨76144002742509760996250165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50762668495006507330833443 76144002742509760996250165)
                ·
                  refine ⟨7138500257110290093398453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76144002742509760996250165 7138500257110290093398453)
                  ·
                    refine ⟨669234399104089696256105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7138500257110290093398453 669234399104089696256105)
                    ·
                      refine ⟨501925799328067272192079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669234399104089696256105 501925799328067272192079)
                      ·
                        rfl

theorem cell23_977497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 5, 2].length) (baseStart_977497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977497 prefixEnd_977497 := by exact prefixLift 977497
  have htrace : WordTrace (prefixWord ++ tailWord_977497) baseStart_977497 baseEnd_977497 := by
    simpa [prefixWord, tailWord_977497, baseEnd_977497] using wordTrace_append hprefix tailTrace_977497
  have hstable : (prefixWord ++ tailWord_977497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977497).length < 2 ^ (prefixWord ++ tailWord_977497).sum := by decide
  have hdescent : baseEnd_977497 < baseStart_977497 := by decide
  rcases family_descends (prefixWord ++ tailWord_977497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977514 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_977514 : Nat := 118140960795 + 977514 * 2 ^ 59
def prefixEnd_977514 : Nat := 4983230072969 + 3 ^ 40 * 977514 * 2
def baseEnd_977514 : Nat := 501934528499193705679501

theorem tailTrace_977514 : CollatzResearch.WordTrace tailWord_977514 prefixEnd_977514 501934528499193705679501 := by
  unfold tailWord_977514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8913216145160299736262899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23768576387094132630034397 8913216145160299736262899)
  ·
    refine ⟨13369824217740449604394349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8913216145160299736262899 13369824217740449604394349)
    ·
      refine ⟨5013684081652668601647881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13369824217740449604394349 5013684081652668601647881)
      ·
        refine ⟨3760263061239501451235911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5013684081652668601647881 3760263061239501451235911)
        ·
          refine ⟨5640394591859252176853867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760263061239501451235911 5640394591859252176853867)
          ·
            refine ⟨8460591887788878265280801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640394591859252176853867 8460591887788878265280801)
            ·
              refine ⟨6345443915841658698960601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8460591887788878265280801 6345443915841658698960601)
              ·
                refine ⟨4759082936881244024220451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6345443915841658698960601 4759082936881244024220451)
                ·
                  refine ⟨7138624405321866036330677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4759082936881244024220451 7138624405321866036330677)
                  ·
                    refine ⟨669246037998924940906001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7138624405321866036330677 669246037998924940906001)
                    ·
                      refine ⟨501934528499193705679501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669246037998924940906001 501934528499193705679501)
                      ·
                        rfl

theorem cell23_977514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_977514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977514 prefixEnd_977514 := by exact prefixLift 977514
  have htrace : WordTrace (prefixWord ++ tailWord_977514) baseStart_977514 baseEnd_977514 := by
    simpa [prefixWord, tailWord_977514, baseEnd_977514] using wordTrace_append hprefix tailTrace_977514
  have hstable : (prefixWord ++ tailWord_977514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977514).length < 2 ^ (prefixWord ++ tailWord_977514).sum := by decide
  have hdescent : baseEnd_977514 < baseStart_977514 := by decide
  rcases family_descends (prefixWord ++ tailWord_977514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977527 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 4]
def baseStart_977527 : Nat := 118140960795 + 977527 * 2 ^ 59
def prefixEnd_977527 : Nat := 4983230072969 + 3 ^ 40 * 977527 * 2
def baseEnd_977527 : Nat := 501941203747702154816941

theorem tailTrace_977527 : CollatzResearch.WordTrace tailWord_977527 prefixEnd_977527 501941203747702154816941 := by
  unfold tailWord_977527
  simp only [CollatzResearch.WordTrace]
  refine ⟨35653338729594102165274835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23768892486396068110183223 35653338729594102165274835)
  ·
    refine ⟨53480008094391153247912253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35653338729594102165274835 53480008094391153247912253)
    ·
      refine ⟨20055003035396682467967095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53480008094391153247912253 20055003035396682467967095)
      ·
        refine ⟨30082504553095023701950643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20055003035396682467967095 30082504553095023701950643)
        ·
          refine ⟨45123756829642535552925965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30082504553095023701950643 45123756829642535552925965)
          ·
            refine ⟨16921408811115950832347237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45123756829642535552925965 16921408811115950832347237)
            ·
              refine ⟨3172764152084240781065107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16921408811115950832347237 3172764152084240781065107)
              ·
                refine ⟨4759146228126361171597661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3172764152084240781065107 4759146228126361171597661)
                ·
                  refine ⟨1784679835547385439349123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4759146228126361171597661 1784679835547385439349123)
                  ·
                    refine ⟨2677019753321078159023685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1784679835547385439349123 2677019753321078159023685)
                    ·
                      refine ⟨501941203747702154816941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2677019753321078159023685 501941203747702154816941)
                      ·
                        rfl

theorem cell23_977527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_977527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977527 prefixEnd_977527 := by exact prefixLift 977527
  have htrace : WordTrace (prefixWord ++ tailWord_977527) baseStart_977527 baseEnd_977527 := by
    simpa [prefixWord, tailWord_977527, baseEnd_977527] using wordTrace_append hprefix tailTrace_977527
  have hstable : (prefixWord ++ tailWord_977527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977527).length < 2 ^ (prefixWord ++ tailWord_977527).sum := by decide
  have hdescent : baseEnd_977527 < baseStart_977527 := by decide
  rcases family_descends (prefixWord ++ tailWord_977527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977537 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 1, 6]
def baseStart_977537 : Nat := 118140960795 + 977537 * 2 ^ 59
def prefixEnd_977537 : Nat := 4983230072969 + 3 ^ 40 * 977537 * 2
def baseEnd_977537 : Nat := 167315446184749038563965

theorem tailTrace_977537 : CollatzResearch.WordTrace tailWord_977537 prefixEnd_977537 167315446184749038563965 := by
  unfold tailWord_977537
  simp only [CollatzResearch.WordTrace]
  refine ⟨35653703459557873873138865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23769135639705249248759243 35653703459557873873138865)
  ·
    refine ⟨26740277594668405404854149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35653703459557873873138865 26740277594668405404854149)
    ·
      refine ⟨5013802049000326013410153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26740277594668405404854149 5013802049000326013410153)
      ·
        refine ⟨3760351536750244510057615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5013802049000326013410153 3760351536750244510057615)
        ·
          refine ⟨5640527305125366765086423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760351536750244510057615 5640527305125366765086423)
          ·
            refine ⟨8460790957688050147629635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640527305125366765086423 8460790957688050147629635)
            ·
              refine ⟨12691186436532075221444453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8460790957688050147629635 12691186436532075221444453)
              ·
                refine ⟨2379597456849764104020835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12691186436532075221444453 2379597456849764104020835)
                ·
                  refine ⟨3569396185274646156031253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2379597456849764104020835 3569396185274646156031253)
                  ·
                    refine ⟨167315446184749038563965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3569396185274646156031253 167315446184749038563965)
                    ·
                      rfl

theorem cell23_977537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_977537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977537 prefixEnd_977537 := by exact prefixLift 977537
  have htrace : WordTrace (prefixWord ++ tailWord_977537) baseStart_977537 baseEnd_977537 := by
    simpa [prefixWord, tailWord_977537, baseEnd_977537] using wordTrace_append hprefix tailTrace_977537
  have hstable : (prefixWord ++ tailWord_977537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977537).length < 2 ^ (prefixWord ++ tailWord_977537).sum := by decide
  have hdescent : baseEnd_977537 < baseStart_977537 := by decide
  rcases family_descends (prefixWord ++ tailWord_977537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977541 : List Nat := [1, 3, 1, 1, 4, 4, 2, 1, 1, 5]
def baseStart_977541 : Nat := 118140960795 + 977541 * 2 ^ 59
def prefixEnd_977541 : Nat := 4983230072969 + 3 ^ 40 * 977541 * 2
def baseEnd_977541 : Nat := 167316130825621700013959

theorem tailTrace_977541 : CollatzResearch.WordTrace tailWord_977541 prefixEnd_977541 167316130825621700013959 := by
  unfold tailWord_977541
  simp only [CollatzResearch.WordTrace]
  refine ⟨35653849351543382556284477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23769232901028921704189651 35653849351543382556284477)
  ·
    refine ⟨13370193506828768458606679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35653849351543382556284477 13370193506828768458606679)
    ·
      refine ⟨20055290260243152687910019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13370193506828768458606679 20055290260243152687910019)
      ·
        refine ⟨30082935390364729031865029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20055290260243152687910019 30082935390364729031865029)
        ·
          refine ⟨5640550385693386693474693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30082935390364729031865029 5640550385693386693474693)
          ·
            refine ⟨1057603197317510005026505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5640550385693386693474693 1057603197317510005026505)
            ·
              refine ⟨793202397988132503769879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1057603197317510005026505 793202397988132503769879)
              ·
                refine ⟨1189803596982198755654819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793202397988132503769879 1189803596982198755654819)
                ·
                  refine ⟨1784705395473298133482229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1189803596982198755654819 1784705395473298133482229)
                  ·
                    refine ⟨167316130825621700013959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1784705395473298133482229 167316130825621700013959)
                    ·
                      rfl

theorem cell23_977541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_977541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977541 prefixEnd_977541 := by exact prefixLift 977541
  have htrace : WordTrace (prefixWord ++ tailWord_977541) baseStart_977541 baseEnd_977541 := by
    simpa [prefixWord, tailWord_977541, baseEnd_977541] using wordTrace_append hprefix tailTrace_977541
  have hstable : (prefixWord ++ tailWord_977541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977541).length < 2 ^ (prefixWord ++ tailWord_977541).sum := by decide
  have hdescent : baseEnd_977541 < baseStart_977541 := by decide
  rcases family_descends (prefixWord ++ tailWord_977541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977547 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 3]
def baseStart_977547 : Nat := 118140960795 + 977547 * 2 ^ 59
def prefixEnd_977547 : Nat := 4983230072969 + 3 ^ 40 * 977547 * 2
def baseEnd_977547 : Nat := 501951473360792076566849

theorem tailTrace_977547 : CollatzResearch.WordTrace tailWord_977547 prefixEnd_977547 501951473360792076566849 := by
  unfold tailWord_977547
  simp only [CollatzResearch.WordTrace]
  refine ⟨35654068189521645581002895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23769378793014430387335263 35654068189521645581002895)
  ·
    refine ⟨53481102284282468371504343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35654068189521645581002895 53481102284282468371504343)
    ·
      refine ⟨80221653426423702557256515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53481102284282468371504343 80221653426423702557256515)
      ·
        refine ⟨120332480139635553835884773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80221653426423702557256515 120332480139635553835884773)
        ·
          refine ⟨22562340026181666344228395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120332480139635553835884773 22562340026181666344228395)
          ·
            refine ⟨33843510039272499516342593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22562340026181666344228395 33843510039272499516342593)
            ·
              refine ⟨25382632529454374637256945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33843510039272499516342593 25382632529454374637256945)
              ·
                refine ⟨19036974397090780977942709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25382632529454374637256945 19036974397090780977942709)
                ·
                  refine ⟨1784716349727260716682129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19036974397090780977942709 1784716349727260716682129)
                  ·
                    refine ⟨1338537262295445537511597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1784716349727260716682129 1338537262295445537511597)
                    ·
                      refine ⟨501951473360792076566849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1338537262295445537511597 501951473360792076566849)
                      ·
                        rfl

theorem cell23_977547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 3].length) (baseStart_977547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977547 prefixEnd_977547 := by exact prefixLift 977547
  have htrace : WordTrace (prefixWord ++ tailWord_977547) baseStart_977547 baseEnd_977547 := by
    simpa [prefixWord, tailWord_977547, baseEnd_977547] using wordTrace_append hprefix tailTrace_977547
  have hstable : (prefixWord ++ tailWord_977547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977547).length < 2 ^ (prefixWord ++ tailWord_977547).sum := by decide
  have hdescent : baseEnd_977547 < baseStart_977547 := by decide
  rcases family_descends (prefixWord ++ tailWord_977547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977561 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 3, 2, 2]
def baseStart_977561 : Nat := 118140960795 + 977561 * 2 ^ 59
def prefixEnd_977561 : Nat := 4983230072969 + 3 ^ 40 * 977561 * 2
def baseEnd_977561 : Nat := 501958662089955021791785

theorem tailTrace_977561 : CollatzResearch.WordTrace tailWord_977561 prefixEnd_977561 501958662089955021791785 := by
  unfold tailWord_977561
  simp only [CollatzResearch.WordTrace]
  refine ⟨35654578811470925972012537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23769719207647283981341691 35654578811470925972012537)
  ·
    refine ⟨26740934108603194479009403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35654578811470925972012537 26740934108603194479009403)
    ·
      refine ⟨40111401162904791718514105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26740934108603194479009403 40111401162904791718514105)
      ·
        refine ⟨30083550872178593788885579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40111401162904791718514105 30083550872178593788885579)
        ·
          refine ⟨45125326308267890683328369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30083550872178593788885579 45125326308267890683328369)
          ·
            refine ⟨33843994731200918012496277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45125326308267890683328369 33843994731200918012496277)
            ·
              refine ⟨1586437253025043031835763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33843994731200918012496277 1586437253025043031835763)
              ·
                refine ⟨2379655879537564547753645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1586437253025043031835763 2379655879537564547753645)
                ·
                  refine ⟨892370954826586705407617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2379655879537564547753645 892370954826586705407617)
                  ·
                    refine ⟨669278216119940029055713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 892370954826586705407617 669278216119940029055713)
                    ·
                      refine ⟨501958662089955021791785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669278216119940029055713 501958662089955021791785)
                      ·
                        rfl

theorem cell23_977561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 2, 2].length) (baseStart_977561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977561 prefixEnd_977561 := by exact prefixLift 977561
  have htrace : WordTrace (prefixWord ++ tailWord_977561) baseStart_977561 baseEnd_977561 := by
    simpa [prefixWord, tailWord_977561, baseEnd_977561] using wordTrace_append hprefix tailTrace_977561
  have hstable : (prefixWord ++ tailWord_977561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977561).length < 2 ^ (prefixWord ++ tailWord_977561).sum := by decide
  have hdescent : baseEnd_977561 < baseStart_977561 := by decide
  rcases family_descends (prefixWord ++ tailWord_977561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977564 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_977564 : Nat := 118140960795 + 977564 * 2 ^ 59
def prefixEnd_977564 : Nat := 4983230072969 + 3 ^ 40 * 977564 * 2
def baseEnd_977564 : Nat := 501960202531918510054271

theorem tailTrace_977564 : CollatzResearch.WordTrace tailWord_977564 prefixEnd_977564 501960202531918510054271 := by
  unfold tailWord_977564
  simp only [CollatzResearch.WordTrace]
  refine ⟨17827344115230028742185873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23769792153640038322914497 17827344115230028742185873)
  ·
    refine ⟨13370508086422521556639405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17827344115230028742185873 13370508086422521556639405)
    ·
      refine ⟨5013940532408445583739777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13370508086422521556639405 5013940532408445583739777)
      ·
        refine ⟨3760455399306334187804833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5013940532408445583739777 3760455399306334187804833)
        ·
          refine ⟨2820341549479750640853625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3760455399306334187804833 2820341549479750640853625)
          ·
            refine ⟨2115256162109812980640219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2820341549479750640853625 2115256162109812980640219)
            ·
              refine ⟨3172884243164719470960329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2115256162109812980640219 3172884243164719470960329)
              ·
                refine ⟨2379663182373539603220247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3172884243164719470960329 2379663182373539603220247)
                ·
                  refine ⟨3569494773560309404830371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2379663182373539603220247 3569494773560309404830371)
                  ·
                    refine ⟨5354242160340464107245557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3569494773560309404830371 5354242160340464107245557)
                    ·
                      refine ⟨501960202531918510054271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5354242160340464107245557 501960202531918510054271)
                      ·
                        rfl

theorem cell23_977564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_977564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977564 prefixEnd_977564 := by exact prefixLift 977564
  have htrace : WordTrace (prefixWord ++ tailWord_977564) baseStart_977564 baseEnd_977564 := by
    simpa [prefixWord, tailWord_977564, baseEnd_977564] using wordTrace_append hprefix tailTrace_977564
  have hstable : (prefixWord ++ tailWord_977564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977564).length < 2 ^ (prefixWord ++ tailWord_977564).sum := by decide
  have hdescent : baseEnd_977564 < baseStart_977564 := by decide
  rcases family_descends (prefixWord ++ tailWord_977564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977581 : List Nat := [1, 5, 2, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_977581 : Nat := 118140960795 + 977581 * 2 ^ 59
def prefixEnd_977581 : Nat := 4983230072969 + 3 ^ 40 * 977581 * 2
def baseEnd_977581 : Nat := 501968931703044943541693

theorem tailTrace_977581 : CollatzResearch.WordTrace tailWord_977581 prefixEnd_977581 501968931703044943541693 := by
  unfold tailWord_977581
  simp only [CollatzResearch.WordTrace]
  refine ⟨35655308271398469387740597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23770205514265646258493731 35655308271398469387740597)
  ·
    refine ⟨3342685150443606505100681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35655308271398469387740597 3342685150443606505100681)
    ·
      refine ⟨2507013862832704878825511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3342685150443606505100681 2507013862832704878825511)
      ·
        refine ⟨3760520794249057318238267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2507013862832704878825511 3760520794249057318238267)
        ·
          refine ⟨5640781191373585977357401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760520794249057318238267 5640781191373585977357401)
          ·
            refine ⟨4230585893530189483018051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5640781191373585977357401 4230585893530189483018051)
            ·
              refine ⟨6345878840295284224527077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4230585893530189483018051 6345878840295284224527077)
              ·
                refine ⟨1189852282555365792098827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6345878840295284224527077 1189852282555365792098827)
                ·
                  refine ⟨1784778423833048688148241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1189852282555365792098827 1784778423833048688148241)
                  ·
                    refine ⟨1338583817874786516111181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1784778423833048688148241 1338583817874786516111181)
                    ·
                      refine ⟨501968931703044943541693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1338583817874786516111181 501968931703044943541693)
                      ·
                        rfl

theorem cell23_977581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_977581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977581 prefixEnd_977581 := by exact prefixLift 977581
  have htrace : WordTrace (prefixWord ++ tailWord_977581) baseStart_977581 baseEnd_977581 := by
    simpa [prefixWord, tailWord_977581, baseEnd_977581] using wordTrace_append hprefix tailTrace_977581
  have hstable : (prefixWord ++ tailWord_977581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977581).length < 2 ^ (prefixWord ++ tailWord_977581).sum := by decide
  have hdescent : baseEnd_977581 < baseStart_977581 := by decide
  rcases family_descends (prefixWord ++ tailWord_977581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977594 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3]
def baseStart_977594 : Nat := 118140960795 + 977594 * 2 ^ 59
def prefixEnd_977594 : Nat := 4983230072969 + 3 ^ 40 * 977594 * 2
def baseEnd_977594 : Nat := 501975606951553392679133

theorem tailTrace_977594 : CollatzResearch.WordTrace tailWord_977594 prefixEnd_977594 501975606951553392679133 := by
  unfold tailWord_977594
  simp only [CollatzResearch.WordTrace]
  refine ⟨8913945605087843151990959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23770521613567581738642557 8913945605087843151990959)
  ·
    refine ⟨13370918407631764727986439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8913945605087843151990959 13370918407631764727986439)
    ·
      refine ⟨20056377611447647091979659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13370918407631764727986439 20056377611447647091979659)
      ·
        refine ⟨30084566417171470637969489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20056377611447647091979659 30084566417171470637969489)
        ·
          refine ⟨22563424812878602978477117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30084566417171470637969489 22563424812878602978477117)
          ·
            refine ⟨8461284304829476116928919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22563424812878602978477117 8461284304829476116928919)
            ·
              refine ⟨12691926457244214175393379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8461284304829476116928919 12691926457244214175393379)
              ·
                refine ⟨19037889685866321263090069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12691926457244214175393379 19037889685866321263090069)
                ·
                  refine ⟨892401079024983809207347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19037889685866321263090069 892401079024983809207347)
                  ·
                    refine ⟨1338601618537475713811021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 892401079024983809207347 1338601618537475713811021)
                    ·
                      refine ⟨501975606951553392679133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1338601618537475713811021 501975606951553392679133)
                      ·
                        rfl

theorem cell23_977594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_977594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977594 prefixEnd_977594 := by exact prefixLift 977594
  have htrace : WordTrace (prefixWord ++ tailWord_977594) baseStart_977594 baseEnd_977594 := by
    simpa [prefixWord, tailWord_977594, baseEnd_977594] using wordTrace_append hprefix tailTrace_977594
  have hstable : (prefixWord ++ tailWord_977594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977594).length < 2 ^ (prefixWord ++ tailWord_977594).sum := by decide
  have hdescent : baseEnd_977594 < baseStart_977594 := by decide
  rcases family_descends (prefixWord ++ tailWord_977594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977601 : List Nat := [1, 2, 6, 2, 1, 2, 9]
def baseStart_977601 : Nat := 118140960795 + 977601 * 2 ^ 59
def prefixEnd_977601 : Nat := 4983230072969 + 3 ^ 40 * 977601 * 2
def baseEnd_977601 : Nat := 6197274090322652657921

theorem tailTrace_977601 : CollatzResearch.WordTrace tailWord_977601 prefixEnd_977601 6197274090322652657921 := by
  unfold tailWord_977601
  simp only [CollatzResearch.WordTrace]
  refine ⟨35656037731326012803468657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23770691820884008535645771 35656037731326012803468657)
  ·
    refine ⟨26742028298494509602601493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35656037731326012803468657 26742028298494509602601493)
    ·
      refine ⟨1253532576491930137621945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26742028298494509602601493 1253532576491930137621945)
      ·
        refine ⟨940149432368947603216459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1253532576491930137621945 940149432368947603216459)
        ·
          refine ⟨1410224148553421404824689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940149432368947603216459 1410224148553421404824689)
          ·
            refine ⟨1057668111415066053618517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1410224148553421404824689 1057668111415066053618517)
            ·
              refine ⟨6197274090322652657921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1057668111415066053618517 6197274090322652657921)
              ·
                rfl

theorem cell23_977601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 9].length) (baseStart_977601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977601 prefixEnd_977601 := by exact prefixLift 977601
  have htrace : WordTrace (prefixWord ++ tailWord_977601) baseStart_977601 baseEnd_977601 := by
    simpa [prefixWord, tailWord_977601, baseEnd_977601] using wordTrace_append hprefix tailTrace_977601
  have hstable : (prefixWord ++ tailWord_977601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977601).length < 2 ^ (prefixWord ++ tailWord_977601).sum := by decide
  have hdescent : baseEnd_977601 < baseStart_977601 := by decide
  rcases family_descends (prefixWord ++ tailWord_977601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977612 : List Nat := [2, 2, 1, 5, 1, 2, 3, 2, 1, 2, 2]
def baseStart_977612 : Nat := 118140960795 + 977612 * 2 ^ 59
def prefixEnd_977612 : Nat := 4983230072969 + 3 ^ 40 * 977612 * 2
def baseEnd_977612 : Nat := 501984849603334322254051

theorem tailTrace_977612 : CollatzResearch.WordTrace tailWord_977612 prefixEnd_977612 501984849603334322254051 := by
  unfold tailWord_977612
  simp only [CollatzResearch.WordTrace]
  refine ⟨17828219467143080841059545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23770959289524107788079393 17828219467143080841059545)
  ·
    refine ⟨13371164600357310630794659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17828219467143080841059545 13371164600357310630794659)
    ·
      refine ⟨20056746900535965946191989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13371164600357310630794659 20056746900535965946191989)
      ·
        refine ⟨1880320021925246807455499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20056746900535965946191989 1880320021925246807455499)
        ·
          refine ⟨2820480032887870211183249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1880320021925246807455499 2820480032887870211183249)
          ·
            refine ⟨2115360024665902658387437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2820480032887870211183249 2115360024665902658387437)
            ·
              refine ⟨793260009249713496895289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2115360024665902658387437 793260009249713496895289)
              ·
                refine ⟨594945006937285122671467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793260009249713496895289 594945006937285122671467)
                ·
                  refine ⟨892417510405927684007201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594945006937285122671467 892417510405927684007201)
                  ·
                    refine ⟨669313132804445763005401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 892417510405927684007201 669313132804445763005401)
                    ·
                      refine ⟨501984849603334322254051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669313132804445763005401 501984849603334322254051)
                      ·
                        rfl

theorem cell23_977612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_977612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977612 prefixEnd_977612 := by exact prefixLift 977612
  have htrace : WordTrace (prefixWord ++ tailWord_977612) baseStart_977612 baseEnd_977612 := by
    simpa [prefixWord, tailWord_977612, baseEnd_977612] using wordTrace_append hprefix tailTrace_977612
  have hstable : (prefixWord ++ tailWord_977612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977612).length < 2 ^ (prefixWord ++ tailWord_977612).sum := by decide
  have hdescent : baseEnd_977612 < baseStart_977612 := by decide
  rcases family_descends (prefixWord ++ tailWord_977612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977617 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_977617 : Nat := 118140960795 + 977617 * 2 ^ 59
def prefixEnd_977617 : Nat := 4983230072969 + 3 ^ 40 * 977617 * 2
def baseEnd_977617 : Nat := 501987417006606802691527

theorem tailTrace_977617 : CollatzResearch.WordTrace tailWord_977617 prefixEnd_977617 501987417006606802691527 := by
  unfold tailWord_977617
  simp only [CollatzResearch.WordTrace]
  refine ⟨35656621299268047536051105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23771080866178698357367403 35656621299268047536051105)
  ·
    refine ⟨26742465974451035652038329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35656621299268047536051105 26742465974451035652038329)
    ·
      refine ⟨20056849480838276739028747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26742465974451035652038329 20056849480838276739028747)
      ·
        refine ⟨30085274221257415108543121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20056849480838276739028747 30085274221257415108543121)
        ·
          refine ⟨22563955665943061331407341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30085274221257415108543121 22563955665943061331407341)
          ·
            refine ⟨8461483374728647999277753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22563955665943061331407341 8461483374728647999277753)
            ·
              refine ⟨6346112531046485999458315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8461483374728647999277753 6346112531046485999458315)
              ·
                refine ⟨9519168796569728999187473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6346112531046485999458315 9519168796569728999187473)
                ·
                  refine ⟨7139376597427296749390605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9519168796569728999187473 7139376597427296749390605)
                  ·
                    refine ⟨2677266224035236281021477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7139376597427296749390605 2677266224035236281021477)
                    ·
                      refine ⟨501987417006606802691527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2677266224035236281021477 501987417006606802691527)
                      ·
                        rfl

theorem cell23_977617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_977617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977617 prefixEnd_977617 := by exact prefixLift 977617
  have htrace : WordTrace (prefixWord ++ tailWord_977617) baseStart_977617 baseEnd_977617 := by
    simpa [prefixWord, tailWord_977617, baseEnd_977617] using wordTrace_append hprefix tailTrace_977617
  have hstable : (prefixWord ++ tailWord_977617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977617).length < 2 ^ (prefixWord ++ tailWord_977617).sum := by decide
  have hdescent : baseEnd_977617 < baseStart_977617 := by decide
  rcases family_descends (prefixWord ++ tailWord_977617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977654 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_977654 : Nat := 118140960795 + 977654 * 2 ^ 59
def prefixEnd_977654 : Nat := 4983230072969 + 3 ^ 40 * 977654 * 2
def baseEnd_977654 : Nat := 502006415790823157928857

theorem tailTrace_977654 : CollatzResearch.WordTrace tailWord_977654 prefixEnd_977654 502006415790823157928857 := by
  unfold tailWord_977654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2228623175008375178446751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23771980533422668570098677 2228623175008375178446751)
  ·
    refine ⟨3342934762512562767670127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2228623175008375178446751 3342934762512562767670127)
    ·
      refine ⟨5014402143768844151505191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3342934762512562767670127 5014402143768844151505191)
      ·
        refine ⟨7521603215653266227257787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5014402143768844151505191 7521603215653266227257787)
        ·
          refine ⟨11282404823479899340886681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7521603215653266227257787 11282404823479899340886681)
          ·
            refine ⟨8461803617609924505665011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11282404823479899340886681 8461803617609924505665011)
            ·
              refine ⟨12692705426414886758497517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8461803617609924505665011 12692705426414886758497517)
              ·
                refine ⟨4759764534905582534436569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12692705426414886758497517 4759764534905582534436569)
                ·
                  refine ⟨3569823401179186900827427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4759764534905582534436569 3569823401179186900827427)
                  ·
                    refine ⟨5354735101768780351241141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3569823401179186900827427 5354735101768780351241141)
                    ·
                      refine ⟨502006415790823157928857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5354735101768780351241141 502006415790823157928857)
                      ·
                        rfl

theorem cell23_977654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_977654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977654 prefixEnd_977654 := by exact prefixLift 977654
  have htrace : WordTrace (prefixWord ++ tailWord_977654) baseStart_977654 baseEnd_977654 := by
    simpa [prefixWord, tailWord_977654, baseEnd_977654] using wordTrace_append hprefix tailTrace_977654
  have hstable : (prefixWord ++ tailWord_977654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977654).length < 2 ^ (prefixWord ++ tailWord_977654).sum := by decide
  have hdescent : baseEnd_977654 < baseStart_977654 := by decide
  rcases family_descends (prefixWord ++ tailWord_977654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977704 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 1, 7]
def baseStart_977704 : Nat := 118140960795 + 977704 * 2 ^ 59
def prefixEnd_977704 : Nat := 4983230072969 + 3 ^ 40 * 977704 * 2
def baseEnd_977704 : Nat := 167344029941182654101209

theorem tailTrace_977704 : CollatzResearch.WordTrace tailWord_977704 prefixEnd_977704 167344029941182654101209 := by
  unfold tailWord_977704
  simp only [CollatzResearch.WordTrace]
  refine ⟨17829897224976430697234083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23773196299968574262978777 17829897224976430697234083)
  ·
    refine ⟨26744845837464646045851125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17829897224976430697234083 26744845837464646045851125)
    ·
      refine ⟨2507329297262310566798543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26744845837464646045851125 2507329297262310566798543)
      ·
        refine ⟨3760993945893465850197815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2507329297262310566798543 3760993945893465850197815)
        ·
          refine ⟨5641490918840198775296723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760993945893465850197815 5641490918840198775296723)
          ·
            refine ⟨8462236378260298162945085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5641490918840198775296723 8462236378260298162945085)
            ·
              refine ⟨3173338641847611811104407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8462236378260298162945085 3173338641847611811104407)
              ·
                refine ⟨4760007962771417716656611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3173338641847611811104407 4760007962771417716656611)
                ·
                  refine ⟨7140011944157126574984917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4760007962771417716656611 7140011944157126574984917)
                  ·
                    refine ⟨167344029941182654101209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7140011944157126574984917 167344029941182654101209)
                    ·
                      rfl

theorem cell23_977704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_977704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977704 prefixEnd_977704 := by exact prefixLift 977704
  have htrace : WordTrace (prefixWord ++ tailWord_977704) baseStart_977704 baseEnd_977704 := by
    simpa [prefixWord, tailWord_977704, baseEnd_977704] using wordTrace_append hprefix tailTrace_977704
  have hstable : (prefixWord ++ tailWord_977704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977704).length < 2 ^ (prefixWord ++ tailWord_977704).sum := by decide
  have hdescent : baseEnd_977704 < baseStart_977704 := by decide
  rcases family_descends (prefixWord ++ tailWord_977704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977724 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_977724 : Nat := 118140960795 + 977724 * 2 ^ 59
def prefixEnd_977724 : Nat := 4983230072969 + 3 ^ 40 * 977724 * 2
def baseEnd_977724 : Nat := 502042359436637884053535

theorem tailTrace_977724 : CollatzResearch.WordTrace tailWord_977724 prefixEnd_977724 502042359436637884053535 := by
  unfold tailWord_977724
  simp only [CollatzResearch.WordTrace]
  refine ⟨17830261954940202405098113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23773682606586936540130817 17830261954940202405098113)
  ·
    refine ⟨13372696466205151803823585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17830261954940202405098113 13372696466205151803823585)
    ·
      refine ⟨10029522349653863852867689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13372696466205151803823585 10029522349653863852867689)
      ·
        refine ⟨7522141762240397889650767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10029522349653863852867689 7522141762240397889650767)
        ·
          refine ⟨11283212643360596834476151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7522141762240397889650767 11283212643360596834476151)
          ·
            refine ⟨16924818965040895251714227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11283212643360596834476151 16924818965040895251714227)
            ·
              refine ⟨25387228447561342877571341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16924818965040895251714227 25387228447561342877571341)
              ·
                refine ⟨9520210667835503579089253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25387228447561342877571341 9520210667835503579089253)
                ·
                  refine ⟨1785039500219156921079235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9520210667835503579089253 1785039500219156921079235)
                  ·
                    refine ⟨2677559250328735381618853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1785039500219156921079235 2677559250328735381618853)
                    ·
                      refine ⟨502042359436637884053535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2677559250328735381618853 502042359436637884053535)
                      ·
                        rfl

theorem cell23_977724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_977724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977724 prefixEnd_977724 := by exact prefixLift 977724
  have htrace : WordTrace (prefixWord ++ tailWord_977724) baseStart_977724 baseEnd_977724 := by
    simpa [prefixWord, tailWord_977724, baseEnd_977724] using wordTrace_append hprefix tailTrace_977724
  have hstable : (prefixWord ++ tailWord_977724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977724).length < 2 ^ (prefixWord ++ tailWord_977724).sum := by decide
  have hdescent : baseEnd_977724 < baseStart_977724 := by decide
  rcases family_descends (prefixWord ++ tailWord_977724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977744 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 3]
def baseStart_977744 : Nat := 118140960795 + 977744 * 2 ^ 59
def prefixEnd_977744 : Nat := 4983230072969 + 3 ^ 40 * 977744 * 2
def baseEnd_977744 : Nat := 502052629049727805803443

theorem tailTrace_977744 : CollatzResearch.WordTrace tailWord_977744 prefixEnd_977744 502052629049727805803443 := by
  unfold tailWord_977744
  simp only [CollatzResearch.WordTrace]
  refine ⟨17830626684903974112962143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23774168913205298817282857 17830626684903974112962143)
  ·
    refine ⟨26745940027355961169443215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17830626684903974112962143 26745940027355961169443215)
    ·
      refine ⟨40118910041033941754164823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26745940027355961169443215 40118910041033941754164823)
      ·
        refine ⟨60178365061550912631247235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40118910041033941754164823 60178365061550912631247235)
        ·
          refine ⟨90267547592326368946870853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60178365061550912631247235 90267547592326368946870853)
          ·
            refine ⟨16925165173561194177538285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90267547592326368946870853 16925165173561194177538285)
            ·
              refine ⟨6346936940085447816576857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16925165173561194177538285 6346936940085447816576857)
              ·
                refine ⟨4760202705064085862432643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6346936940085447816576857 4760202705064085862432643)
                ·
                  refine ⟨7140304057596128793648965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4760202705064085862432643 7140304057596128793648965)
                  ·
                    refine ⟨1338807010799274148809181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7140304057596128793648965 1338807010799274148809181)
                    ·
                      refine ⟨502052629049727805803443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1338807010799274148809181 502052629049727805803443)
                      ·
                        rfl

theorem cell23_977744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 3].length) (baseStart_977744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977744 prefixEnd_977744 := by exact prefixLift 977744
  have htrace : WordTrace (prefixWord ++ tailWord_977744) baseStart_977744 baseEnd_977744 := by
    simpa [prefixWord, tailWord_977744, baseEnd_977744] using wordTrace_append hprefix tailTrace_977744
  have hstable : (prefixWord ++ tailWord_977744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977744).length < 2 ^ (prefixWord ++ tailWord_977744).sum := by decide
  have hdescent : baseEnd_977744 < baseStart_977744 := by decide
  rcases family_descends (prefixWord ++ tailWord_977744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977751 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 3, 4]
def baseStart_977751 : Nat := 118140960795 + 977751 * 2 ^ 59
def prefixEnd_977751 : Nat := 4983230072969 + 3 ^ 40 * 977751 * 2
def baseEnd_977751 : Nat := 167352074471436426138637

theorem tailTrace_977751 : CollatzResearch.WordTrace tailWord_977751 prefixEnd_977751 167352074471436426138637 := by
  unfold tailWord_977751
  simp only [CollatzResearch.WordTrace]
  refine ⟨35661508680782588421429107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23774339120521725614286071 35661508680782588421429107)
  ·
    refine ⟨53492263021173882632143661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35661508680782588421429107 53492263021173882632143661)
    ·
      refine ⟨20059598632940205987053873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53492263021173882632143661 20059598632940205987053873)
      ·
        refine ⟨15044698974705154490290405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20059598632940205987053873 15044698974705154490290405)
        ·
          refine ⟨2820881057757216466929451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15044698974705154490290405 2820881057757216466929451)
          ·
            refine ⟨4231321586635824700394177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820881057757216466929451 4231321586635824700394177)
            ·
              refine ⟨3173491189976868525295633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4231321586635824700394177 3173491189976868525295633)
              ·
                refine ⟨2380118392482651393971725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3173491189976868525295633 2380118392482651393971725)
                ·
                  refine ⟨892544397180994272739397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2380118392482651393971725 892544397180994272739397)
                  ·
                    refine ⟨167352074471436426138637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 892544397180994272739397 167352074471436426138637)
                    ·
                      rfl

theorem cell23_977751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_977751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977751 prefixEnd_977751 := by exact prefixLift 977751
  have htrace : WordTrace (prefixWord ++ tailWord_977751) baseStart_977751 baseEnd_977751 := by
    simpa [prefixWord, tailWord_977751, baseEnd_977751] using wordTrace_append hprefix tailTrace_977751
  have hstable : (prefixWord ++ tailWord_977751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977751).length < 2 ^ (prefixWord ++ tailWord_977751).sum := by decide
  have hdescent : baseEnd_977751 < baseStart_977751 := by decide
  rcases family_descends (prefixWord ++ tailWord_977751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977764 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 8]
def baseStart_977764 : Nat := 118140960795 + 977764 * 2 ^ 59
def prefixEnd_977764 : Nat := 4983230072969 + 3 ^ 40 * 977764 * 2
def baseEnd_977764 : Nat := 55784766518090858617039

theorem tailTrace_977764 : CollatzResearch.WordTrace tailWord_977764 prefixEnd_977764 55784766518090858617039 := by
  unfold tailWord_977764
  simp only [CollatzResearch.WordTrace]
  refine ⟨17830991414867745820826173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23774655219823661094434897 17830991414867745820826173)
  ·
    refine ⟨6686621780575404682809815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17830991414867745820826173 6686621780575404682809815)
    ·
      refine ⟨10029932670863107024214723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6686621780575404682809815 10029932670863107024214723)
      ·
        refine ⟨15044899006294660536322085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10029932670863107024214723 15044899006294660536322085)
        ·
          refine ⟨2820918563680248850560391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15044899006294660536322085 2820918563680248850560391)
          ·
            refine ⟨4231377845520373275840587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820918563680248850560391 4231377845520373275840587)
            ·
              refine ⟨6347066768280559913760881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231377845520373275840587 6347066768280559913760881)
              ·
                refine ⟨4760300076210419935320661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6347066768280559913760881 4760300076210419935320661)
                ·
                  refine ⟨55784766518090858617039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4760300076210419935320661 55784766518090858617039)
                  ·
                    rfl

theorem cell23_977764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_977764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977764 prefixEnd_977764 := by exact prefixLift 977764
  have htrace : WordTrace (prefixWord ++ tailWord_977764) baseStart_977764 baseEnd_977764 := by
    simpa [prefixWord, tailWord_977764, baseEnd_977764] using wordTrace_append hprefix tailTrace_977764
  have hstable : (prefixWord ++ tailWord_977764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977764).length < 2 ^ (prefixWord ++ tailWord_977764).sum := by decide
  have hdescent : baseEnd_977764 < baseStart_977764 := by decide
  rcases family_descends (prefixWord ++ tailWord_977764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977785 : List Nat := [1, 2, 1, 3, 2, 4, 3, 2, 1, 4]
def baseStart_977785 : Nat := 118140960795 + 977785 * 2 ^ 59
def prefixEnd_977785 : Nat := 4983230072969 + 3 ^ 40 * 977785 * 2
def baseEnd_977785 : Nat := 167357893918854048463585

theorem tailTrace_977785 : CollatzResearch.WordTrace tailWord_977785 prefixEnd_977785 167357893918854048463585 := by
  unfold tailWord_977785
  simp only [CollatzResearch.WordTrace]
  refine ⟨35662748762659412228166809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23775165841772941485444539 35662748762659412228166809)
  ·
    refine ⟨26747061571994559171125107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35662748762659412228166809 26747061571994559171125107)
    ·
      refine ⟨40120592357991838756687661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26747061571994559171125107 40120592357991838756687661)
      ·
        refine ⟨15045222134246939533757873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40120592357991838756687661 15045222134246939533757873)
        ·
          refine ⟨11283916600685204650318405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15045222134246939533757873 11283916600685204650318405)
          ·
            refine ⟨2115734362628475871934701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11283916600685204650318405 2115734362628475871934701)
            ·
              refine ⟨793400385985678451975513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2115734362628475871934701 793400385985678451975513)
              ·
                refine ⟨595050289489258838981635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793400385985678451975513 595050289489258838981635)
                ·
                  refine ⟨892575434233888258472453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595050289489258838981635 892575434233888258472453)
                  ·
                    refine ⟨167357893918854048463585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 892575434233888258472453 167357893918854048463585)
                    ·
                      rfl

theorem cell23_977785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 1, 4].length) (baseStart_977785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977785 prefixEnd_977785 := by exact prefixLift 977785
  have htrace : WordTrace (prefixWord ++ tailWord_977785) baseStart_977785 baseEnd_977785 := by
    simpa [prefixWord, tailWord_977785, baseEnd_977785] using wordTrace_append hprefix tailTrace_977785
  have hstable : (prefixWord ++ tailWord_977785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977785).length < 2 ^ (prefixWord ++ tailWord_977785).sum := by decide
  have hdescent : baseEnd_977785 < baseStart_977785 := by decide
  rcases family_descends (prefixWord ++ tailWord_977785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977824 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 3, 6]
def baseStart_977824 : Nat := 118140960795 + 977824 * 2 ^ 59
def prefixEnd_977824 : Nat := 4983230072969 + 3 ^ 40 * 977824 * 2
def baseEnd_977824 : Nat := 167364569167362497601025

theorem tailTrace_977824 : CollatzResearch.WordTrace tailWord_977824 prefixEnd_977824 167364569167362497601025 := by
  unfold tailWord_977824
  simp only [CollatzResearch.WordTrace]
  refine ⟨17832085604759060944418263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23776114139678747925891017 17832085604759060944418263)
  ·
    refine ⟨26748128407138591416627395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17832085604759060944418263 26748128407138591416627395)
    ·
      refine ⟨40122192610707887124941093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26748128407138591416627395 40122192610707887124941093)
      ·
        refine ⟨7522911114507728835926455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40122192610707887124941093 7522911114507728835926455)
        ·
          refine ⟨11284366671761593253889683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7522911114507728835926455 11284366671761593253889683)
          ·
            refine ⟨16926550007642389880834525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11284366671761593253889683 16926550007642389880834525)
            ·
              refine ⟨6347456252865896205312947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16926550007642389880834525 6347456252865896205312947)
              ·
                refine ⟨9521184379298844307969421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6347456252865896205312947 9521184379298844307969421)
                ·
                  refine ⟨3570444142237066615488533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9521184379298844307969421 3570444142237066615488533)
                  ·
                    refine ⟨167364569167362497601025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3570444142237066615488533 167364569167362497601025)
                    ·
                      rfl

theorem cell23_977824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3, 6].length) (baseStart_977824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977824 prefixEnd_977824 := by exact prefixLift 977824
  have htrace : WordTrace (prefixWord ++ tailWord_977824) baseStart_977824 baseEnd_977824 := by
    simpa [prefixWord, tailWord_977824, baseEnd_977824] using wordTrace_append hprefix tailTrace_977824
  have hstable : (prefixWord ++ tailWord_977824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977824).length < 2 ^ (prefixWord ++ tailWord_977824).sum := by decide
  have hdescent : baseEnd_977824 < baseStart_977824 := by decide
  rcases family_descends (prefixWord ++ tailWord_977824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977828 : List Nat := [2, 3, 1, 2, 1, 2, 5, 1, 1, 5]
def baseStart_977828 : Nat := 118140960795 + 977828 * 2 ^ 59
def prefixEnd_977828 : Nat := 4983230072969 + 3 ^ 40 * 977828 * 2
def baseEnd_977828 : Nat := 167365253808235159051019

theorem tailTrace_977828 : CollatzResearch.WordTrace tailWord_977828 prefixEnd_977828 167365253808235159051019 := by
  unfold tailWord_977828
  simp only [CollatzResearch.WordTrace]
  refine ⟨17832158550751815285991069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23776211401002420381321425 17832158550751815285991069)
  ·
    refine ⟨6687059456531930732246651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17832158550751815285991069 6687059456531930732246651)
    ·
      refine ⟨10030589184797896098369977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6687059456531930732246651 10030589184797896098369977)
      ·
        refine ⟨7522941888598422073777483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10030589184797896098369977 7522941888598422073777483)
        ·
          refine ⟨11284412832897633110666225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7522941888598422073777483 11284412832897633110666225)
          ·
            refine ⟨8463309624673224832999669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11284412832897633110666225 8463309624673224832999669)
            ·
              refine ⟨793435277313114828093719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8463309624673224832999669 793435277313114828093719)
              ·
                refine ⟨1190152915969672242140579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793435277313114828093719 1190152915969672242140579)
                ·
                  refine ⟨1785229373954508363210869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190152915969672242140579 1785229373954508363210869)
                  ·
                    refine ⟨167365253808235159051019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1785229373954508363210869 167365253808235159051019)
                    ·
                      rfl

theorem cell23_977828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_977828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977828 prefixEnd_977828 := by exact prefixLift 977828
  have htrace : WordTrace (prefixWord ++ tailWord_977828) baseStart_977828 baseEnd_977828 := by
    simpa [prefixWord, tailWord_977828, baseEnd_977828] using wordTrace_append hprefix tailTrace_977828
  have hstable : (prefixWord ++ tailWord_977828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977828).length < 2 ^ (prefixWord ++ tailWord_977828).sum := by decide
  have hdescent : baseEnd_977828 < baseStart_977828 := by decide
  rcases family_descends (prefixWord ++ tailWord_977828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977868 : List Nat := [2, 2, 1, 4, 1, 1, 2, 4, 1, 2, 3]
def baseStart_977868 : Nat := 118140960795 + 977868 * 2 ^ 59
def prefixEnd_977868 : Nat := 4983230072969 + 3 ^ 40 * 977868 * 2
def baseEnd_977868 : Nat := 502116300650885320652873

theorem tailTrace_977868 : CollatzResearch.WordTrace tailWord_977868 prefixEnd_977868 502116300650885320652873 := by
  unfold tailWord_977868
  simp only [CollatzResearch.WordTrace]
  refine ⟨17832888010679358701719129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23777184014239144935625505 17832888010679358701719129)
  ·
    refine ⟨13374666008009519026289347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17832888010679358701719129 13374666008009519026289347)
    ·
      refine ⟨20061999012014278539434021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13374666008009519026289347 20061999012014278539434021)
      ·
        refine ⟨3761624814752677226143879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20061999012014278539434021 3761624814752677226143879)
        ·
          refine ⟨5642437222129015839215819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3761624814752677226143879 5642437222129015839215819)
          ·
            refine ⟨8463655833193523758823729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642437222129015839215819 8463655833193523758823729)
            ·
              refine ⟨6347741874895142819117797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8463655833193523758823729 6347741874895142819117797)
              ·
                refine ⟨1190201601542839278584587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6347741874895142819117797 1190201601542839278584587)
                ·
                  refine ⟨1785302402314258917876881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190201601542839278584587 1785302402314258917876881)
                  ·
                    refine ⟨1338976801735694188407661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1785302402314258917876881 1338976801735694188407661)
                    ·
                      refine ⟨502116300650885320652873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1338976801735694188407661 502116300650885320652873)
                      ·
                        rfl

theorem cell23_977868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_977868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977868 prefixEnd_977868 := by exact prefixLift 977868
  have htrace : WordTrace (prefixWord ++ tailWord_977868) baseStart_977868 baseEnd_977868 := by
    simpa [prefixWord, tailWord_977868, baseEnd_977868] using wordTrace_append hprefix tailTrace_977868
  have hstable : (prefixWord ++ tailWord_977868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977868).length < 2 ^ (prefixWord ++ tailWord_977868).sum := by decide
  have hdescent : baseEnd_977868 < baseStart_977868 := by decide
  rcases family_descends (prefixWord ++ tailWord_977868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977869 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_977869 : Nat := 118140960795 + 977869 * 2 ^ 59
def prefixEnd_977869 : Nat := 4983230072969 + 3 ^ 40 * 977869 * 2
def baseEnd_977869 : Nat := 502116814131539816740369

theorem tailTrace_977869 : CollatzResearch.WordTrace tailWord_977869 prefixEnd_977869 502116814131539816740369 := by
  unfold tailWord_977869
  simp only [CollatzResearch.WordTrace]
  refine ⟨35665812494355094574224661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23777208329570063049483107 35665812494355094574224661)
  ·
    refine ⟨1671834960672895058166781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35665812494355094574224661 1671834960672895058166781)
    ·
      refine ⟨626938110252335646812543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1671834960672895058166781 626938110252335646812543)
      ·
        refine ⟨940407165378503470218815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626938110252335646812543 940407165378503470218815)
        ·
          refine ⟨1410610748067755205328223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940407165378503470218815 1410610748067755205328223)
          ·
            refine ⟨2115916122101632807992335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410610748067755205328223 2115916122101632807992335)
            ·
              refine ⟨3173874183152449211988503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2115916122101632807992335 3173874183152449211988503)
              ·
                refine ⟨4760811274728673817982755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3173874183152449211988503 4760811274728673817982755)
                ·
                  refine ⟨7141216912093010726974133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4760811274728673817982755 7141216912093010726974133)
                  ·
                    refine ⟨669489085508719755653825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7141216912093010726974133 669489085508719755653825)
                    ·
                      refine ⟨502116814131539816740369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669489085508719755653825 502116814131539816740369)
                      ·
                        rfl

theorem cell23_977869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_977869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977869 prefixEnd_977869 := by exact prefixLift 977869
  have htrace : WordTrace (prefixWord ++ tailWord_977869) baseStart_977869 baseEnd_977869 := by
    simpa [prefixWord, tailWord_977869, baseEnd_977869] using wordTrace_append hprefix tailTrace_977869
  have hstable : (prefixWord ++ tailWord_977869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977869).length < 2 ^ (prefixWord ++ tailWord_977869).sum := by decide
  have hdescent : baseEnd_977869 < baseStart_977869 := by decide
  rcases family_descends (prefixWord ++ tailWord_977869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977871 : List Nat := [1, 1, 2, 1, 1, 7, 3, 7]
def baseStart_977871 : Nat := 118140960795 + 977871 * 2 ^ 59
def prefixEnd_977871 : Nat := 4983230072969 + 3 ^ 40 * 977871 * 2
def baseEnd_977871 : Nat := 18596957077512918848717

theorem tailTrace_977871 : CollatzResearch.WordTrace tailWord_977871 prefixEnd_977871 18596957077512918848717 := by
  unfold tailWord_977871
  simp only [CollatzResearch.WordTrace]
  refine ⟨35665885440347848915797467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23777256960231899277198311 35665885440347848915797467)
  ·
    refine ⟨53498828160521773373696201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35665885440347848915797467 53498828160521773373696201)
    ·
      refine ⟨40124121120391330030272151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53498828160521773373696201 40124121120391330030272151)
      ·
        refine ⟨60186181680586995045408227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40124121120391330030272151 60186181680586995045408227)
        ·
          refine ⟨90279272520880492568112341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60186181680586995045408227 90279272520880492568112341)
          ·
            refine ⟨2115920449708136544565133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 90279272520880492568112341 2115920449708136544565133)
            ·
              refine ⟨793470168640551204211925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2115920449708136544565133 793470168640551204211925)
              ·
                refine ⟨18596957077512918848717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 793470168640551204211925 18596957077512918848717)
                ·
                  rfl

theorem cell23_977871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 7].length) (baseStart_977871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977871 prefixEnd_977871 := by exact prefixLift 977871
  have htrace : WordTrace (prefixWord ++ tailWord_977871) baseStart_977871 baseEnd_977871 := by
    simpa [prefixWord, tailWord_977871, baseEnd_977871] using wordTrace_append hprefix tailTrace_977871
  have hstable : (prefixWord ++ tailWord_977871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977871).length < 2 ^ (prefixWord ++ tailWord_977871).sum := by decide
  have hdescent : baseEnd_977871 < baseStart_977871 := by decide
  rcases family_descends (prefixWord ++ tailWord_977871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977882 : List Nat := [3, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2]
def baseStart_977882 : Nat := 118140960795 + 977882 * 2 ^ 59
def prefixEnd_977882 : Nat := 4983230072969 + 3 ^ 40 * 977882 * 2
def baseEnd_977882 : Nat := 502123489380048265877809

theorem tailTrace_977882 : CollatzResearch.WordTrace tailWord_977882 prefixEnd_977882 502123489380048265877809 := by
  unfold tailWord_977882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8916571660826999448611975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23777524428871998529631933 8916571660826999448611975)
  ·
    refine ⟨13374857491240499172917963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8916571660826999448611975 13374857491240499172917963)
    ·
      refine ⟨20062286236860748759376945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13374857491240499172917963 20062286236860748759376945)
      ·
        refine ⟨15046714677645561569532709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20062286236860748759376945 15046714677645561569532709)
        ·
          refine ⟨2821259002058542794287383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15046714677645561569532709 2821259002058542794287383)
          ·
            refine ⟨4231888503087814191431075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821259002058542794287383 4231888503087814191431075)
            ·
              refine ⟨6347832754631721287146613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231888503087814191431075 6347832754631721287146613)
              ·
                refine ⟨595109320746723870669995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6347832754631721287146613 595109320746723870669995)
                ·
                  refine ⟨892663981120085806004993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595109320746723870669995 892663981120085806004993)
                  ·
                    refine ⟨669497985840064354503745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 892663981120085806004993 669497985840064354503745)
                    ·
                      refine ⟨502123489380048265877809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669497985840064354503745 502123489380048265877809)
                      ·
                        rfl

theorem cell23_977882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_977882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977882 prefixEnd_977882 := by exact prefixLift 977882
  have htrace : WordTrace (prefixWord ++ tailWord_977882) baseStart_977882 baseEnd_977882 := by
    simpa [prefixWord, tailWord_977882, baseEnd_977882] using wordTrace_append hprefix tailTrace_977882
  have hstable : (prefixWord ++ tailWord_977882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977882).length < 2 ^ (prefixWord ++ tailWord_977882).sum := by decide
  have hdescent : baseEnd_977882 < baseStart_977882 := by decide
  rcases family_descends (prefixWord ++ tailWord_977882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977885 : List Nat := [1, 4, 3, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_977885 : Nat := 118140960795 + 977885 * 2 ^ 59
def prefixEnd_977885 : Nat := 4983230072969 + 3 ^ 40 * 977885 * 2
def baseEnd_977885 : Nat := 502125029822011754140295

theorem tailTrace_977885 : CollatzResearch.WordTrace tailWord_977885 prefixEnd_977885 502125029822011754140295 := by
  unfold tailWord_977885
  simp only [CollatzResearch.WordTrace]
  refine ⟨35666396062297129306807109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23777597374864752871204739 35666396062297129306807109)
  ·
    refine ⟨6687449261680711745026333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35666396062297129306807109 6687449261680711745026333)
    ·
      refine ⟨2507793473130266904384875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6687449261680711745026333 2507793473130266904384875)
      ·
        refine ⟨3761690209695400356577313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2507793473130266904384875 3761690209695400356577313)
        ·
          refine ⟨2821267657271550267432985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3761690209695400356577313 2821267657271550267432985)
          ·
            refine ⟨2115950742953662700574739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2821267657271550267432985 2115950742953662700574739)
            ·
              refine ⟨3173926114430494050862109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2115950742953662700574739 3173926114430494050862109)
              ·
                refine ⟨1190222292911435269073291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3173926114430494050862109 1190222292911435269073291)
                ·
                  refine ⟨1785333439367152903609937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190222292911435269073291 1785333439367152903609937)
                  ·
                    refine ⟨1339000079525364677707453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1785333439367152903609937 1339000079525364677707453)
                    ·
                      refine ⟨502125029822011754140295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1339000079525364677707453 502125029822011754140295)
                      ·
                        rfl

theorem cell23_977885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_977885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977885 prefixEnd_977885 := by exact prefixLift 977885
  have htrace : WordTrace (prefixWord ++ tailWord_977885) baseStart_977885 baseEnd_977885 := by
    simpa [prefixWord, tailWord_977885, baseEnd_977885] using wordTrace_append hprefix tailTrace_977885
  have hstable : (prefixWord ++ tailWord_977885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977885).length < 2 ^ (prefixWord ++ tailWord_977885).sum := by decide
  have hdescent : baseEnd_977885 < baseStart_977885 := by decide
  rcases family_descends (prefixWord ++ tailWord_977885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977909 : List Nat := [1, 3, 5, 2, 1, 1, 3, 1, 2, 4]
def baseStart_977909 : Nat := 118140960795 + 977909 * 2 ^ 59
def prefixEnd_977909 : Nat := 4983230072969 + 3 ^ 40 * 977909 * 2
def baseEnd_977909 : Nat := 167379117785906553413395

theorem tailTrace_977909 : CollatzResearch.WordTrace tailWord_977909 prefixEnd_977909 167379117785906553413395 := by
  unfold tailWord_977909
  simp only [CollatzResearch.WordTrace]
  refine ⟨35667271414210181405680781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23778180942806787603787187 35667271414210181405680781)
  ·
    refine ⟨13375226780328818027130293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35667271414210181405680781 13375226780328818027130293)
    ·
      refine ⟨1253927510655826690043465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13375226780328818027130293 1253927510655826690043465)
      ·
        refine ⟨940445632991870017532599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1253927510655826690043465 940445632991870017532599)
        ·
          refine ⟨1410668449487805026298899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940445632991870017532599 1410668449487805026298899)
          ·
            refine ⟨2116002674231707539448349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410668449487805026298899 2116002674231707539448349)
            ·
              refine ⟨793501002836890327293131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2116002674231707539448349 793501002836890327293131)
              ·
                refine ⟨1190251504255335490939697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793501002836890327293131 1190251504255335490939697)
                ·
                  refine ⟨892688628191501618204773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1190251504255335490939697 892688628191501618204773)
                  ·
                    refine ⟨167379117785906553413395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 892688628191501618204773 167379117785906553413395)
                    ·
                      rfl

theorem cell23_977909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_977909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977909 prefixEnd_977909 := by exact prefixLift 977909
  have htrace : WordTrace (prefixWord ++ tailWord_977909) baseStart_977909 baseEnd_977909 := by
    simpa [prefixWord, tailWord_977909, baseEnd_977909] using wordTrace_append hprefix tailTrace_977909
  have hstable : (prefixWord ++ tailWord_977909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977909).length < 2 ^ (prefixWord ++ tailWord_977909).sum := by decide
  have hdescent : baseEnd_977909 < baseStart_977909 := by decide
  rcases family_descends (prefixWord ++ tailWord_977909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977922 : List Nat := [3, 4, 1, 3, 1, 2, 2, 7]
def baseStart_977922 : Nat := 118140960795 + 977922 * 2 ^ 59
def prefixEnd_977922 : Nat := 4983230072969 + 3 ^ 40 * 977922 * 2
def baseEnd_977922 : Nat := 18597926985415855902875

theorem tailTrace_977922 : CollatzResearch.WordTrace tailWord_977922 prefixEnd_977922 18597926985415855902875 := by
  unfold tailWord_977922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8916936390790771156476005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23778497042108723083936013 8916936390790771156476005)
  ·
    refine ⟨1671925573273269591839251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8916936390790771156476005 1671925573273269591839251)
    ·
      refine ⟨2507888359909904387758877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1671925573273269591839251 2507888359909904387758877)
      ·
        refine ⟨940458134966214145409579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2507888359909904387758877 940458134966214145409579)
        ·
          refine ⟨1410687202449321218114369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940458134966214145409579 1410687202449321218114369)
          ·
            refine ⟨1058015401836990913585777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1410687202449321218114369 1058015401836990913585777)
            ·
              refine ⟨793511551377743185189333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1058015401836990913585777 793511551377743185189333)
              ·
                refine ⟨18597926985415855902875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 793511551377743185189333 18597926985415855902875)
                ·
                  rfl

theorem cell23_977922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 7].length) (baseStart_977922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977922 prefixEnd_977922 := by exact prefixLift 977922
  have htrace : WordTrace (prefixWord ++ tailWord_977922) baseStart_977922 baseEnd_977922 := by
    simpa [prefixWord, tailWord_977922, baseEnd_977922] using wordTrace_append hprefix tailTrace_977922
  have hstable : (prefixWord ++ tailWord_977922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977922).length < 2 ^ (prefixWord ++ tailWord_977922).sum := by decide
  have hdescent : baseEnd_977922 < baseStart_977922 := by decide
  rcases family_descends (prefixWord ++ tailWord_977922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977925 : List Nat := [1, 3, 1, 1, 2, 3, 4, 2, 1, 3, 2]
def baseStart_977925 : Nat := 118140960795 + 977925 * 2 ^ 59
def prefixEnd_977925 : Nat := 4983230072969 + 3 ^ 40 * 977925 * 2
def baseEnd_977925 : Nat := 502145569048191597640111

theorem tailTrace_977925 : CollatzResearch.WordTrace tailWord_977925 prefixEnd_977925 502145569048191597640111 := by
  unfold tailWord_977925
  simp only [CollatzResearch.WordTrace]
  refine ⟨35667854982152216138263229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23778569988101477425508819 35667854982152216138263229)
  ·
    refine ⟨13375445618307081051848711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35667854982152216138263229 13375445618307081051848711)
    ·
      refine ⟨20063168427460621577773067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13375445618307081051848711 20063168427460621577773067)
      ·
        refine ⟨30094752641190932366659601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20063168427460621577773067 30094752641190932366659601)
        ·
          refine ⟨22571064480893199274994701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30094752641190932366659601 22571064480893199274994701)
          ·
            refine ⟨8464149180334949728123013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22571064480893199274994701 8464149180334949728123013)
            ·
              refine ⟨1587027971312803074023065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8464149180334949728123013 1587027971312803074023065)
              ·
                refine ⟨1190270978484602305517299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587027971312803074023065 1190270978484602305517299)
                ·
                  refine ⟨1785406467726903458275949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190270978484602305517299 1785406467726903458275949)
                  ·
                    refine ⟨669527425397588796853481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1785406467726903458275949 669527425397588796853481)
                    ·
                      refine ⟨502145569048191597640111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669527425397588796853481 502145569048191597640111)
                      ·
                        rfl

theorem cell23_977925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 3, 2].length) (baseStart_977925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977925 prefixEnd_977925 := by exact prefixLift 977925
  have htrace : WordTrace (prefixWord ++ tailWord_977925) baseStart_977925 baseEnd_977925 := by
    simpa [prefixWord, tailWord_977925, baseEnd_977925] using wordTrace_append hprefix tailTrace_977925
  have hstable : (prefixWord ++ tailWord_977925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977925).length < 2 ^ (prefixWord ++ tailWord_977925).sum := by decide
  have hdescent : baseEnd_977925 < baseStart_977925 := by decide
  rcases family_descends (prefixWord ++ tailWord_977925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977941 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_977941 : Nat := 118140960795 + 977941 * 2 ^ 59
def prefixEnd_977941 : Nat := 4983230072969 + 3 ^ 40 * 977941 * 2
def baseEnd_977941 : Nat := 502153784738663535040037

theorem tailTrace_977941 : CollatzResearch.WordTrace tailWord_977941 prefixEnd_977941 502153784738663535040037 := by
  unfold tailWord_977941
  simp only [CollatzResearch.WordTrace]
  refine ⟨35668438550094250870845677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23778959033396167247230451 35668438550094250870845677)
  ·
    refine ⟨13375664456285344076567129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35668438550094250870845677 13375664456285344076567129)
    ·
      refine ⟨10031748342214008057425347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13375664456285344076567129 10031748342214008057425347)
      ·
        refine ⟨15047622513321012086138021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10031748342214008057425347 15047622513321012086138021)
        ·
          refine ⟨2821429221247689766150879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15047622513321012086138021 2821429221247689766150879)
          ·
            refine ⟨4232143831871534649226319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821429221247689766150879 4232143831871534649226319)
            ·
              refine ⟨6348215747807301973839479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4232143831871534649226319 6348215747807301973839479)
              ·
                refine ⟨9522323621710952960759219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6348215747807301973839479 9522323621710952960759219)
                ·
                  refine ⟨14283485432566429441138829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9522323621710952960759219 14283485432566429441138829)
                  ·
                    refine ⟨5356307037212411040427061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14283485432566429441138829 5356307037212411040427061)
                    ·
                      refine ⟨502153784738663535040037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5356307037212411040427061 502153784738663535040037)
                      ·
                        rfl

theorem cell23_977941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_977941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977941 prefixEnd_977941 := by exact prefixLift 977941
  have htrace : WordTrace (prefixWord ++ tailWord_977941) baseStart_977941 baseEnd_977941 := by
    simpa [prefixWord, tailWord_977941, baseEnd_977941] using wordTrace_append hprefix tailTrace_977941
  have hstable : (prefixWord ++ tailWord_977941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977941).length < 2 ^ (prefixWord ++ tailWord_977941).sum := by decide
  have hdescent : baseEnd_977941 < baseStart_977941 := by decide
  rcases family_descends (prefixWord ++ tailWord_977941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977955 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 4, 2, 2]
def baseStart_977955 : Nat := 118140960795 + 977955 * 2 ^ 59
def prefixEnd_977955 : Nat := 4983230072969 + 3 ^ 40 * 977955 * 2
def baseEnd_977955 : Nat := 502160973467826480264973

theorem tailTrace_977955 : CollatzResearch.WordTrace tailWord_977955 prefixEnd_977955 502160973467826480264973 := by
  unfold tailWord_977955
  simp only [CollatzResearch.WordTrace]
  refine ⟨35668949172043531261855319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23779299448029020841236879 35668949172043531261855319)
  ·
    refine ⟨53503423758065296892782979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35668949172043531261855319 53503423758065296892782979)
    ·
      refine ⟨80255135637097945339174469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53503423758065296892782979 80255135637097945339174469)
      ·
        refine ⟨15047837931955864751095213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80255135637097945339174469 15047837931955864751095213)
        ·
          refine ⟨5642939224483449281660705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15047837931955864751095213 5642939224483449281660705)
          ·
            refine ⟨4232204418362586961245529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5642939224483449281660705 4232204418362586961245529)
            ·
              refine ⟨3174153313771940220934147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4232204418362586961245529 3174153313771940220934147)
              ·
                refine ⟨4761229970657910331401221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174153313771940220934147 4761229970657910331401221)
                ·
                  refine ⟨892730619498358187137729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4761229970657910331401221 892730619498358187137729)
                  ·
                    refine ⟨669547964623768640353297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 892730619498358187137729 669547964623768640353297)
                    ·
                      refine ⟨502160973467826480264973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669547964623768640353297 502160973467826480264973)
                      ·
                        rfl

theorem cell23_977955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_977955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977955 prefixEnd_977955 := by exact prefixLift 977955
  have htrace : WordTrace (prefixWord ++ tailWord_977955) baseStart_977955 baseEnd_977955 := by
    simpa [prefixWord, tailWord_977955, baseEnd_977955] using wordTrace_append hprefix tailTrace_977955
  have hstable : (prefixWord ++ tailWord_977955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977955).length < 2 ^ (prefixWord ++ tailWord_977955).sum := by decide
  have hdescent : baseEnd_977955 < baseStart_977955 := by decide
  rcases family_descends (prefixWord ++ tailWord_977955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977971 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 3]
def baseStart_977971 : Nat := 118140960795 + 977971 * 2 ^ 59
def prefixEnd_977971 : Nat := 4983230072969 + 3 ^ 40 * 977971 * 2
def baseEnd_977971 : Nat := 502169189158298417664899

theorem tailTrace_977971 : CollatzResearch.WordTrace tailWord_977971 prefixEnd_977971 502169189158298417664899 := by
  unfold tailWord_977971
  simp only [CollatzResearch.WordTrace]
  refine ⟨35669532739985565994437767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23779688493323710662958511 35669532739985565994437767)
  ·
    refine ⟨53504299109978348991656651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35669532739985565994437767 53504299109978348991656651)
    ·
      refine ⟨80256448664967523487484977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53504299109978348991656651 80256448664967523487484977)
      ·
        refine ⟨60192336498725642615613733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80256448664967523487484977 60192336498725642615613733)
        ·
          refine ⟨11286063093511057990427575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60192336498725642615613733 11286063093511057990427575)
          ·
            refine ⟨16929094640266586985641363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11286063093511057990427575 16929094640266586985641363)
            ·
              refine ⟨25393641960399880478462045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16929094640266586985641363 25393641960399880478462045)
              ·
                refine ⟨9522615735149955179423267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25393641960399880478462045 9522615735149955179423267)
                ·
                  refine ⟨14283923602724932769134901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9522615735149955179423267 14283923602724932769134901)
                  ·
                    refine ⟨1339117837755462447106397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14283923602724932769134901 1339117837755462447106397)
                    ·
                      refine ⟨502169189158298417664899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1339117837755462447106397 502169189158298417664899)
                      ·
                        rfl

theorem cell23_977971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 5, 3].length) (baseStart_977971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_977971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_977971 prefixEnd_977971 := by exact prefixLift 977971
  have htrace : WordTrace (prefixWord ++ tailWord_977971) baseStart_977971 baseEnd_977971 := by
    simpa [prefixWord, tailWord_977971, baseEnd_977971] using wordTrace_append hprefix tailTrace_977971
  have hstable : (prefixWord ++ tailWord_977971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977971).length < 2 ^ (prefixWord ++ tailWord_977971).sum := by decide
  have hdescent : baseEnd_977971 < baseStart_977971 := by decide
  rcases family_descends (prefixWord ++ tailWord_977971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978001 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_978001 : Nat := 118140960795 + 978001 * 2 ^ 59
def prefixEnd_978001 : Nat := 4983230072969 + 3 ^ 40 * 978001 * 2
def baseEnd_978001 : Nat := 502184593577933300289761

theorem tailTrace_978001 : CollatzResearch.WordTrace tailWord_978001 prefixEnd_978001 502184593577933300289761 := by
  unfold tailWord_978001
  simp only [CollatzResearch.WordTrace]
  refine ⟨35670626929876881118029857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23780417953251254078686571 35670626929876881118029857)
  ·
    refine ⟨26752970197407660838522393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35670626929876881118029857 26752970197407660838522393)
    ·
      refine ⟨20064727648055745628891795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26752970197407660838522393 20064727648055745628891795)
      ·
        refine ⟨30097091472083618443337693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20064727648055745628891795 30097091472083618443337693)
        ·
          refine ⟨11286409302031356916251635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30097091472083618443337693 11286409302031356916251635)
          ·
            refine ⟨16929613953047035374377453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11286409302031356916251635 16929613953047035374377453)
            ·
              refine ⟨6348605232392638265391545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16929613953047035374377453 6348605232392638265391545)
              ·
                refine ⟨4761453924294478699043659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6348605232392638265391545 4761453924294478699043659)
                ·
                  refine ⟨7142180886441718048565489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761453924294478699043659 7142180886441718048565489)
                  ·
                    refine ⟨5356635664831288536424117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7142180886441718048565489 5356635664831288536424117)
                    ·
                      refine ⟨502184593577933300289761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5356635664831288536424117 502184593577933300289761)
                      ·
                        rfl

theorem cell23_978001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_978001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978001 prefixEnd_978001 := by exact prefixLift 978001
  have htrace : WordTrace (prefixWord ++ tailWord_978001) baseStart_978001 baseEnd_978001 := by
    simpa [prefixWord, tailWord_978001, baseEnd_978001] using wordTrace_append hprefix tailTrace_978001
  have hstable : (prefixWord ++ tailWord_978001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978001).length < 2 ^ (prefixWord ++ tailWord_978001).sum := by decide
  have hdescent : baseEnd_978001 < baseStart_978001 := by decide
  rcases family_descends (prefixWord ++ tailWord_978001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978046 : List Nat := [4, 2, 4, 1, 1, 1, 2, 3, 5]
def baseStart_978046 : Nat := 118140960795 + 978046 * 2 ^ 59
def prefixEnd_978046 : Nat := 4983230072969 + 3 ^ 40 * 978046 * 2
def baseEnd_978046 : Nat := 55800855578598402691895

theorem tailTrace_978046 : CollatzResearch.WordTrace tailWord_978046 prefixEnd_978046 55800855578598402691895 := by
  unfold tailWord_978046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459033526839231725427249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23781512143142569202278661 4459033526839231725427249)
  ·
    refine ⟨3344275145129423794070437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4459033526839231725427249 3344275145129423794070437)
    ·
      refine ⟨627051589711766961388207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3344275145129423794070437 627051589711766961388207)
      ·
        refine ⟨940577384567650442082311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627051589711766961388207 940577384567650442082311)
        ·
          refine ⟨1410866076851475663123467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940577384567650442082311 1410866076851475663123467)
          ·
            refine ⟨2116299115277213494685201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410866076851475663123467 2116299115277213494685201)
            ·
              refine ⟨1587224336457910121013901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116299115277213494685201 1587224336457910121013901)
              ·
                refine ⟨595209126171716295380213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1587224336457910121013901 595209126171716295380213)
                ·
                  refine ⟨55800855578598402691895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 595209126171716295380213 55800855578598402691895)
                  ·
                    rfl

theorem cell23_978046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_978046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978046 prefixEnd_978046 := by exact prefixLift 978046
  have htrace : WordTrace (prefixWord ++ tailWord_978046) baseStart_978046 baseEnd_978046 := by
    simpa [prefixWord, tailWord_978046, baseEnd_978046] using wordTrace_append hprefix tailTrace_978046
  have hstable : (prefixWord ++ tailWord_978046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978046).length < 2 ^ (prefixWord ++ tailWord_978046).sum := by decide
  have hdescent : baseEnd_978046 < baseStart_978046 := by decide
  rcases family_descends (prefixWord ++ tailWord_978046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978051 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 8]
def baseStart_978051 : Nat := 118140960795 + 978051 * 2 ^ 59
def prefixEnd_978051 : Nat := 4983230072969 + 3 ^ 40 * 978051 * 2
def baseEnd_978051 : Nat := 55801140845628678296059

theorem tailTrace_978051 : CollatzResearch.WordTrace tailWord_978051 prefixEnd_978051 55801140845628678296059 := by
  unfold tailWord_978051
  simp only [CollatzResearch.WordTrace]
  refine ⟨35672450579695739657350007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23781633719797159771566671 35672450579695739657350007)
  ·
    refine ⟨53508675869543609486025011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35672450579695739657350007 53508675869543609486025011)
    ·
      refine ⟨80263013804315414229037517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53508675869543609486025011 80263013804315414229037517)
      ·
        refine ⟨30098630176618280335889069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80263013804315414229037517 30098630176618280335889069)
        ·
          refine ⟨11286986316231855125958401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30098630176618280335889069 11286986316231855125958401)
          ·
            refine ⟨8465239737173891344468801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11286986316231855125958401 8465239737173891344468801)
            ·
              refine ⟨6348929802880418508351601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8465239737173891344468801 6348929802880418508351601)
              ·
                refine ⟨4761697352160313881263701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6348929802880418508351601 4761697352160313881263701)
                ·
                  refine ⟨55801140845628678296059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4761697352160313881263701 55801140845628678296059)
                  ·
                    rfl

theorem cell23_978051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 8].length) (baseStart_978051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978051 prefixEnd_978051 := by exact prefixLift 978051
  have htrace : WordTrace (prefixWord ++ tailWord_978051) baseStart_978051 baseEnd_978051 := by
    simpa [prefixWord, tailWord_978051, baseEnd_978051] using wordTrace_append hprefix tailTrace_978051
  have hstable : (prefixWord ++ tailWord_978051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978051).length < 2 ^ (prefixWord ++ tailWord_978051).sum := by decide
  have hdescent : baseEnd_978051 < baseStart_978051 := by decide
  rcases family_descends (prefixWord ++ tailWord_978051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978072 : List Nat := [2, 1, 2, 4, 2, 1, 2, 4, 1, 4]
def baseStart_978072 : Nat := 118140960795 + 978072 * 2 ^ 59
def prefixEnd_978072 : Nat := 4983230072969 + 3 ^ 40 * 978072 * 2
def baseEnd_978072 : Nat := 167407016901467507500645

theorem tailTrace_978072 : CollatzResearch.WordTrace tailWord_978072 prefixEnd_978072 167407016901467507500645 := by
  unfold tailWord_978072
  simp only [CollatzResearch.WordTrace]
  refine ⟨17836608256309830121932235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23782144341746440162576313 17836608256309830121932235)
  ·
    refine ⟨26754912384464745182898353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17836608256309830121932235 26754912384464745182898353)
    ·
      refine ⟨20066184288348558887173765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26754912384464745182898353 20066184288348558887173765)
      ·
        refine ⟨3762409554065354791345081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20066184288348558887173765 3762409554065354791345081)
        ·
          refine ⟨2821807165549016093508811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3762409554065354791345081 2821807165549016093508811)
          ·
            refine ⟨4232710748323524140263217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821807165549016093508811 4232710748323524140263217)
            ·
              refine ⟨3174533061242643105197413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4232710748323524140263217 3174533061242643105197413)
              ·
                refine ⟨595224948982995582224515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3174533061242643105197413 595224948982995582224515)
                ·
                  refine ⟨892837423474493373336773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595224948982995582224515 892837423474493373336773)
                  ·
                    refine ⟨167407016901467507500645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 892837423474493373336773 167407016901467507500645)
                    ·
                      rfl

theorem cell23_978072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_978072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978072 prefixEnd_978072 := by exact prefixLift 978072
  have htrace : WordTrace (prefixWord ++ tailWord_978072) baseStart_978072 baseEnd_978072 := by
    simpa [prefixWord, tailWord_978072, baseEnd_978072] using wordTrace_append hprefix tailTrace_978072
  have hstable : (prefixWord ++ tailWord_978072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978072).length < 2 ^ (prefixWord ++ tailWord_978072).sum := by decide
  have hdescent : baseEnd_978072 < baseStart_978072 := by decide
  rcases family_descends (prefixWord ++ tailWord_978072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978085 : List Nat := [1, 3, 1, 2, 1, 5, 3, 1, 6]
def baseStart_978085 : Nat := 118140960795 + 978085 * 2 ^ 59
def prefixEnd_978085 : Nat := 4983230072969 + 3 ^ 40 * 978085 * 2
def baseEnd_978085 : Nat := 55803080661434552404375

theorem tailTrace_978085 : CollatzResearch.WordTrace tailWord_978085 prefixEnd_978085 55803080661434552404375 := by
  unfold tailWord_978085
  simp only [CollatzResearch.WordTrace]
  refine ⟨35673690661572563464087709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23782460441048375642725139 35673690661572563464087709)
  ·
    refine ⟨13377633998089711299032891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35673690661572563464087709 13377633998089711299032891)
    ·
      refine ⟨20066450997134566948549337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13377633998089711299032891 20066450997134566948549337)
      ·
        refine ⟨15049838247850925211412003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20066450997134566948549337 15049838247850925211412003)
        ·
          refine ⟨22574757371776387817118005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15049838247850925211412003 22574757371776387817118005)
          ·
            refine ⟨2116383503604036357854813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22574757371776387817118005 2116383503604036357854813)
            ·
              refine ⟨793643813851513634195555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2116383503604036357854813 793643813851513634195555)
              ·
                refine ⟨1190465720777270451293333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793643813851513634195555 1190465720777270451293333)
                ·
                  refine ⟨55803080661434552404375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1190465720777270451293333 55803080661434552404375)
                  ·
                    rfl

theorem cell23_978085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 6].length) (baseStart_978085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978085 prefixEnd_978085 := by exact prefixLift 978085
  have htrace : WordTrace (prefixWord ++ tailWord_978085) baseStart_978085 baseEnd_978085 := by
    simpa [prefixWord, tailWord_978085, baseEnd_978085] using wordTrace_append hprefix tailTrace_978085
  have hstable : (prefixWord ++ tailWord_978085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978085).length < 2 ^ (prefixWord ++ tailWord_978085).sum := by decide
  have hdescent : baseEnd_978085 < baseStart_978085 := by decide
  rcases family_descends (prefixWord ++ tailWord_978085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978095 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 3, 1, 3]
def baseStart_978095 : Nat := 118140960795 + 978095 * 2 ^ 59
def prefixEnd_978095 : Nat := 4983230072969 + 3 ^ 40 * 978095 * 2
def baseEnd_978095 : Nat := 502232860759455932514329

theorem tailTrace_978095 : CollatzResearch.WordTrace tailWord_978095 prefixEnd_978095 502232860759455932514329 := by
  unfold tailWord_978095
  simp only [CollatzResearch.WordTrace]
  refine ⟨35674055391536335171951739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23782703594357556781301159 35674055391536335171951739)
  ·
    refine ⟨53511083087304502757927609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35674055391536335171951739 53511083087304502757927609)
    ·
      refine ⟨40133312315478377068445707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53511083087304502757927609 40133312315478377068445707)
      ·
        refine ⟨60199968473217565602668561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40133312315478377068445707 60199968473217565602668561)
        ·
          refine ⟨45149976354913174202001421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60199968473217565602668561 45149976354913174202001421)
          ·
            refine ⟨16931241133092440325750533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45149976354913174202001421 16931241133092440325750533)
            ·
              refine ⟨3174607712454832561078225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16931241133092440325750533 3174607712454832561078225)
              ·
                refine ⟨2380955784341124420808669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3174607712454832561078225 2380955784341124420808669)
                ·
                  refine ⟨892858419127921657803251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2380955784341124420808669 892858419127921657803251)
                  ·
                    refine ⟨1339287628691882486704877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 892858419127921657803251 1339287628691882486704877)
                    ·
                      refine ⟨502232860759455932514329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1339287628691882486704877 502232860759455932514329)
                      ·
                        rfl

theorem cell23_978095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 1, 3].length) (baseStart_978095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978095 prefixEnd_978095 := by exact prefixLift 978095
  have htrace : WordTrace (prefixWord ++ tailWord_978095) baseStart_978095 baseEnd_978095 := by
    simpa [prefixWord, tailWord_978095, baseEnd_978095] using wordTrace_append hprefix tailTrace_978095
  have hstable : (prefixWord ++ tailWord_978095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978095).length < 2 ^ (prefixWord ++ tailWord_978095).sum := by decide
  have hdescent : baseEnd_978095 < baseStart_978095 := by decide
  rcases family_descends (prefixWord ++ tailWord_978095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978105 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 1, 5, 2]
def baseStart_978105 : Nat := 118140960795 + 978105 * 2 ^ 59
def prefixEnd_978105 : Nat := 4983230072969 + 3 ^ 40 * 978105 * 2
def baseEnd_978105 : Nat := 502237995566000893389283

theorem tailTrace_978105 : CollatzResearch.WordTrace tailWord_978105 prefixEnd_978105 502237995566000893389283 := by
  unfold tailWord_978105
  simp only [CollatzResearch.WordTrace]
  refine ⟨35674420121500106879815769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23782946747666737919877179 35674420121500106879815769)
  ·
    refine ⟨26755815091125080159861827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35674420121500106879815769 26755815091125080159861827)
    ·
      refine ⟨40133722636687620239792741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26755815091125080159861827 40133722636687620239792741)
      ·
        refine ⟨7525072994378928794961139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40133722636687620239792741 7525072994378928794961139)
        ·
          refine ⟨11287609491568393192441709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7525072994378928794961139 11287609491568393192441709)
          ·
            refine ⟨4232853559338147447165641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11287609491568393192441709 4232853559338147447165641)
            ·
              refine ⟨3174640169503610585374231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4232853559338147447165641 3174640169503610585374231)
              ·
                refine ⟨4761960254255415878061347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174640169503610585374231 4761960254255415878061347)
                ·
                  refine ⟨7142940381383123817092021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761960254255415878061347 7142940381383123817092021)
                  ·
                    refine ⟨669650660754667857852377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7142940381383123817092021 669650660754667857852377)
                    ·
                      refine ⟨502237995566000893389283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669650660754667857852377 502237995566000893389283)
                      ·
                        rfl

theorem cell23_978105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_978105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978105 prefixEnd_978105 := by exact prefixLift 978105
  have htrace : WordTrace (prefixWord ++ tailWord_978105) baseStart_978105 baseEnd_978105 := by
    simpa [prefixWord, tailWord_978105, baseEnd_978105] using wordTrace_append hprefix tailTrace_978105
  have hstable : (prefixWord ++ tailWord_978105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978105).length < 2 ^ (prefixWord ++ tailWord_978105).sum := by decide
  have hdescent : baseEnd_978105 < baseStart_978105 := by decide
  rcases family_descends (prefixWord ++ tailWord_978105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978122 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 2, 3, 2]
def baseStart_978122 : Nat := 118140960795 + 978122 * 2 ^ 59
def prefixEnd_978122 : Nat := 4983230072969 + 3 ^ 40 * 978122 * 2
def baseEnd_978122 : Nat := 502246724737127326876705

theorem tailTrace_978122 : CollatzResearch.WordTrace tailWord_978122 prefixEnd_978122 502246724737127326876705 := by
  unfold tailWord_978122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8918760040609629695796155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23783360108292345855456413 8918760040609629695796155)
  ·
    refine ⟨13378140060914444543694233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8918760040609629695796155 13378140060914444543694233)
    ·
      refine ⟨10033605045685833407770675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13378140060914444543694233 10033605045685833407770675)
      ·
        refine ⟨15050407568528750111656013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10033605045685833407770675 15050407568528750111656013)
        ·
          refine ⟨5643902838198281291871005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15050407568528750111656013 5643902838198281291871005)
          ·
            refine ⟨2116463564324355484451627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5643902838198281291871005 2116463564324355484451627)
            ·
              refine ⟨3174695346486533226677441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116463564324355484451627 3174695346486533226677441)
              ·
                refine ⟨2381021509864899920008081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3174695346486533226677441 2381021509864899920008081)
                ·
                  refine ⟨1785766132398674940006061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2381021509864899920008081 1785766132398674940006061)
                  ·
                    refine ⟨669662299649503102502273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1785766132398674940006061 669662299649503102502273)
                    ·
                      refine ⟨502246724737127326876705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669662299649503102502273 502246724737127326876705)
                      ·
                        rfl

theorem cell23_978122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_978122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978122 prefixEnd_978122 := by exact prefixLift 978122
  have htrace : WordTrace (prefixWord ++ tailWord_978122) baseStart_978122 baseEnd_978122 := by
    simpa [prefixWord, tailWord_978122, baseEnd_978122] using wordTrace_append hprefix tailTrace_978122
  have hstable : (prefixWord ++ tailWord_978122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978122).length < 2 ^ (prefixWord ++ tailWord_978122).sum := by decide
  have hdescent : baseEnd_978122 < baseStart_978122 := by decide
  rcases family_descends (prefixWord ++ tailWord_978122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978138 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3]
def baseStart_978138 : Nat := 118140960795 + 978138 * 2 ^ 59
def prefixEnd_978138 : Nat := 4983230072969 + 3 ^ 40 * 978138 * 2
def baseEnd_978138 : Nat := 502254940427599264276631

theorem tailTrace_978138 : CollatzResearch.WordTrace tailWord_978138 prefixEnd_978138 502254940427599264276631 := by
  unfold tailWord_978138
  simp only [CollatzResearch.WordTrace]
  refine ⟨8918905932595138378941767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23783749153587035677178045 8918905932595138378941767)
  ·
    refine ⟨13378358898892707568412651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8918905932595138378941767 13378358898892707568412651)
    ·
      refine ⟨20067538348339061352618977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13378358898892707568412651 20067538348339061352618977)
      ·
        refine ⟨15050653761254296014464233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20067538348339061352618977 15050653761254296014464233)
        ·
          refine ⟨11287990320940722010848175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15050653761254296014464233 11287990320940722010848175)
          ·
            refine ⟨16931985481411083016272263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11287990320940722010848175 16931985481411083016272263)
            ·
              refine ⟨25397978222116624524408395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16931985481411083016272263 25397978222116624524408395)
              ·
                refine ⟨38096967333174936786612593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25397978222116624524408395 38096967333174936786612593)
                ·
                  refine ⟨28572725499881202589959445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38096967333174936786612593 28572725499881202589959445)
                  ·
                    refine ⟨1339346507806931371404349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28572725499881202589959445 1339346507806931371404349)
                    ·
                      refine ⟨502254940427599264276631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1339346507806931371404349 502254940427599264276631)
                      ·
                        rfl

theorem cell23_978138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_978138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978138 prefixEnd_978138 := by exact prefixLift 978138
  have htrace : WordTrace (prefixWord ++ tailWord_978138) baseStart_978138 baseEnd_978138 := by
    simpa [prefixWord, tailWord_978138, baseEnd_978138] using wordTrace_append hprefix tailTrace_978138
  have hstable : (prefixWord ++ tailWord_978138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978138).length < 2 ^ (prefixWord ++ tailWord_978138).sum := by decide
  have hdescent : baseEnd_978138 < baseStart_978138 := by decide
  rcases family_descends (prefixWord ++ tailWord_978138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978148 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_978148 : Nat := 118140960795 + 978148 * 2 ^ 59
def prefixEnd_978148 : Nat := 4983230072969 + 3 ^ 40 * 978148 * 2
def baseEnd_978148 : Nat := 502260075234144225151585

theorem tailTrace_978148 : CollatzResearch.WordTrace tailWord_978148 prefixEnd_978148 502260075234144225151585 := by
  unfold tailWord_978148
  simp only [CollatzResearch.WordTrace]
  refine ⟨17837994230172162611815549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23783992306896216815754065 17837994230172162611815549)
  ·
    refine ⟨6689247836314560979430831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17837994230172162611815549 6689247836314560979430831)
    ·
      refine ⟨10033871754471841469146247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6689247836314560979430831 10033871754471841469146247)
      ·
        refine ⟨15050807631707762203719371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10033871754471841469146247 15050807631707762203719371)
        ·
          refine ⟨22576211447561643305579057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15050807631707762203719371 22576211447561643305579057)
          ·
            refine ⟨16932158585671232479184293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22576211447561643305579057 16932158585671232479184293)
            ·
              refine ⟨3174779734813356089847055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16932158585671232479184293 3174779734813356089847055)
              ·
                refine ⟨4762169602220034134770583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174779734813356089847055 4762169602220034134770583)
                ·
                  refine ⟨7143254403330051202155875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4762169602220034134770583 7143254403330051202155875)
                  ·
                    refine ⟨10714881604995076803233813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7143254403330051202155875 10714881604995076803233813)
                    ·
                      refine ⟨502260075234144225151585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10714881604995076803233813 502260075234144225151585)
                      ·
                        rfl

theorem cell23_978148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_978148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978148 prefixEnd_978148 := by exact prefixLift 978148
  have htrace : WordTrace (prefixWord ++ tailWord_978148) baseStart_978148 baseEnd_978148 := by
    simpa [prefixWord, tailWord_978148, baseEnd_978148] using wordTrace_append hprefix tailTrace_978148
  have hstable : (prefixWord ++ tailWord_978148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978148).length < 2 ^ (prefixWord ++ tailWord_978148).sum := by decide
  have hdescent : baseEnd_978148 < baseStart_978148 := by decide
  rcases family_descends (prefixWord ++ tailWord_978148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978149 : List Nat := [1, 3, 1, 4, 4, 1, 1, 2, 1, 5]
def baseStart_978149 : Nat := 118140960795 + 978149 * 2 ^ 59
def prefixEnd_978149 : Nat := 4983230072969 + 3 ^ 40 * 978149 * 2
def baseEnd_978149 : Nat := 167420196238266240413027

theorem tailTrace_978149 : CollatzResearch.WordTrace tailWord_978149 prefixEnd_978149 167420196238266240413027 := by
  unfold tailWord_978149
  simp only [CollatzResearch.WordTrace]
  refine ⟨35676024933340702394417501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23784016622227134929611667 35676024933340702394417501)
  ·
    refine ⟨13378509350002763397906563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35676024933340702394417501 13378509350002763397906563)
    ·
      refine ⟨20067764025004145096859845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13378509350002763397906563 20067764025004145096859845)
      ·
        refine ⟨3762705754688277205661221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20067764025004145096859845 3762705754688277205661221)
        ·
          refine ⟨705507329004051976061479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3762705754688277205661221 705507329004051976061479)
          ·
            refine ⟨1058260993506077964092219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705507329004051976061479 1058260993506077964092219)
            ·
              refine ⟨1587391490259116946138329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058260993506077964092219 1587391490259116946138329)
              ·
                refine ⟨1190543617694337709603747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587391490259116946138329 1190543617694337709603747)
                ·
                  refine ⟨1785815426541506564405621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190543617694337709603747 1785815426541506564405621)
                  ·
                    refine ⟨167420196238266240413027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1785815426541506564405621 167420196238266240413027)
                    ·
                      rfl

theorem cell23_978149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_978149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978149 prefixEnd_978149 := by exact prefixLift 978149
  have htrace : WordTrace (prefixWord ++ tailWord_978149) baseStart_978149 baseEnd_978149 := by
    simpa [prefixWord, tailWord_978149, baseEnd_978149] using wordTrace_append hprefix tailTrace_978149
  have hstable : (prefixWord ++ tailWord_978149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978149).length < 2 ^ (prefixWord ++ tailWord_978149).sum := by decide
  have hdescent : baseEnd_978149 < baseStart_978149 := by decide
  rcases family_descends (prefixWord ++ tailWord_978149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978152 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_978152 : Nat := 118140960795 + 978152 * 2 ^ 59
def prefixEnd_978152 : Nat := 4983230072969 + 3 ^ 40 * 978152 * 2
def baseEnd_978152 : Nat := 502262129156762209501567

theorem tailTrace_978152 : CollatzResearch.WordTrace tailWord_978152 prefixEnd_978152 502262129156762209501567 := by
  unfold tailWord_978152
  simp only [CollatzResearch.WordTrace]
  refine ⟨17838067176164916953388355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23784089568219889271184473 17838067176164916953388355)
  ·
    refine ⟨26757100764247375430082533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17838067176164916953388355 26757100764247375430082533)
    ·
      refine ⟨5016956393296382893140475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26757100764247375430082533 5016956393296382893140475)
      ·
        refine ⟨7525434589944574339710713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5016956393296382893140475 7525434589944574339710713)
        ·
          refine ⟨5644075942458430754783035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7525434589944574339710713 5644075942458430754783035)
          ·
            refine ⟨8466113913687646132174553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5644075942458430754783035 8466113913687646132174553)
            ·
              refine ⟨6349585435265734599130915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8466113913687646132174553 6349585435265734599130915)
              ·
                refine ⟨9524378152898601898696373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6349585435265734599130915 9524378152898601898696373)
                ·
                  refine ⟨892910451834243928002785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9524378152898601898696373 892910451834243928002785)
                  ·
                    refine ⟨669682838875682946002089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 892910451834243928002785 669682838875682946002089)
                    ·
                      refine ⟨502262129156762209501567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669682838875682946002089 502262129156762209501567)
                      ·
                        rfl

theorem cell23_978152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_978152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978152 prefixEnd_978152 := by exact prefixLift 978152
  have htrace : WordTrace (prefixWord ++ tailWord_978152) baseStart_978152 baseEnd_978152 := by
    simpa [prefixWord, tailWord_978152, baseEnd_978152] using wordTrace_append hprefix tailTrace_978152
  have hstable : (prefixWord ++ tailWord_978152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978152).length < 2 ^ (prefixWord ++ tailWord_978152).sum := by decide
  have hdescent : baseEnd_978152 < baseStart_978152 := by decide
  rcases family_descends (prefixWord ++ tailWord_978152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978155 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 3]
def baseStart_978155 : Nat := 118140960795 + 978155 * 2 ^ 59
def prefixEnd_978155 : Nat := 4983230072969 + 3 ^ 40 * 978155 * 2
def baseEnd_978155 : Nat := 502263669598725697764053

theorem tailTrace_978155 : CollatzResearch.WordTrace tailWord_978155 prefixEnd_978155 502263669598725697764053 := by
  unfold tailWord_978155
  simp only [CollatzResearch.WordTrace]
  refine ⟨35676243771318965419135919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23784162514212643612757279 35676243771318965419135919)
  ·
    refine ⟨53514365656978448128703879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35676243771318965419135919 53514365656978448128703879)
    ·
      refine ⟨80271548485467672193055819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53514365656978448128703879 80271548485467672193055819)
      ·
        refine ⟨120407322728201508289583729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80271548485467672193055819 120407322728201508289583729)
        ·
          refine ⟨90305492046151131217187797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120407322728201508289583729 90305492046151131217187797)
          ·
            refine ⟨2116534969831667137902839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 90305492046151131217187797 2116534969831667137902839)
            ·
              refine ⟨3174802454747500706854259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116534969831667137902839 3174802454747500706854259)
              ·
                refine ⟨4762203682121251060281389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174802454747500706854259 4762203682121251060281389)
                ·
                  refine ⟨1785826380795469147605521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4762203682121251060281389 1785826380795469147605521)
                  ·
                    refine ⟨1339369785596601860704141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1785826380795469147605521 1339369785596601860704141)
                    ·
                      refine ⟨502263669598725697764053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1339369785596601860704141 502263669598725697764053)
                      ·
                        rfl

theorem cell23_978155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 2, 3].length) (baseStart_978155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978155 prefixEnd_978155 := by exact prefixLift 978155
  have htrace : WordTrace (prefixWord ++ tailWord_978155) baseStart_978155 baseEnd_978155 := by
    simpa [prefixWord, tailWord_978155, baseEnd_978155] using wordTrace_append hprefix tailTrace_978155
  have hstable : (prefixWord ++ tailWord_978155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978155).length < 2 ^ (prefixWord ++ tailWord_978155).sum := by decide
  have hdescent : baseEnd_978155 < baseStart_978155 := by decide
  rcases family_descends (prefixWord ++ tailWord_978155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978158 : List Nat := [4, 1, 2, 1, 1, 1, 4, 9]
def baseStart_978158 : Nat := 118140960795 + 978158 * 2 ^ 59
def prefixEnd_978158 : Nat := 4983230072969 + 3 ^ 40 * 978158 * 2
def baseEnd_978158 : Nat := 18602415186692192075057

theorem tailTrace_978158 : CollatzResearch.WordTrace tailWord_978158 prefixEnd_978158 18602415186692192075057 := by
  unfold tailWord_978158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459544148788512116436891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23784235460205397954330085 4459544148788512116436891)
  ·
    refine ⟨6689316223182768174655337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4459544148788512116436891 6689316223182768174655337)
    ·
      refine ⟨5016987167387076130991503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6689316223182768174655337 5016987167387076130991503)
      ·
        refine ⟨7525480751080614196487255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5016987167387076130991503 7525480751080614196487255)
        ·
          refine ⟨11288221126620921294730883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7525480751080614196487255 11288221126620921294730883)
          ·
            refine ⟨16932331689931381942096325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11288221126620921294730883 16932331689931381942096325)
            ·
              refine ⟨3174812191862134114143061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16932331689931381942096325 3174812191862134114143061)
              ·
                refine ⟨18602415186692192075057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3174812191862134114143061 18602415186692192075057)
                ·
                  rfl

theorem cell23_978158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_978158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978158 prefixEnd_978158 := by exact prefixLift 978158
  have htrace : WordTrace (prefixWord ++ tailWord_978158) baseStart_978158 baseEnd_978158 := by
    simpa [prefixWord, tailWord_978158, baseEnd_978158] using wordTrace_append hprefix tailTrace_978158
  have hstable : (prefixWord ++ tailWord_978158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978158).length < 2 ^ (prefixWord ++ tailWord_978158).sum := by decide
  have hdescent : baseEnd_978158 < baseStart_978158 := by decide
  rcases family_descends (prefixWord ++ tailWord_978158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978169 : List Nat := [1, 2, 1, 3, 1, 1, 4, 5, 1, 2, 2]
def baseStart_978169 : Nat := 118140960795 + 978169 * 2 ^ 59
def prefixEnd_978169 : Nat := 4983230072969 + 3 ^ 40 * 978169 * 2
def baseEnd_978169 : Nat := 502270858327888642988989

theorem tailTrace_978169 : CollatzResearch.WordTrace tailWord_978169 prefixEnd_978169 502270858327888642988989 := by
  unfold tailWord_978169
  simp only [CollatzResearch.WordTrace]
  refine ⟨35676754393268245810145561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23784502928845497206763707 35676754393268245810145561)
  ·
    refine ⟨26757565794951184357609171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35676754393268245810145561 26757565794951184357609171)
    ·
      refine ⟨40136348692426776536413757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26757565794951184357609171 40136348692426776536413757)
      ·
        refine ⟨15051130759660041201155159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40136348692426776536413757 15051130759660041201155159)
        ·
          refine ⟨22576696139490061801732739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15051130759660041201155159 22576696139490061801732739)
          ·
            refine ⟨33865044209235092702599109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22576696139490061801732739 33865044209235092702599109)
            ·
              refine ⟨6349695789231579881737333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33865044209235092702599109 6349695789231579881737333)
              ·
                refine ⟨595283980240460613912875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6349695789231579881737333 595283980240460613912875)
                ·
                  refine ⟨892925970360690920869313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595283980240460613912875 892925970360690920869313)
                  ·
                    refine ⟨669694477770518190651985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 892925970360690920869313 669694477770518190651985)
                    ·
                      refine ⟨502270858327888642988989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669694477770518190651985 502270858327888642988989)
                      ·
                        rfl

theorem cell23_978169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_978169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978169 prefixEnd_978169 := by exact prefixLift 978169
  have htrace : WordTrace (prefixWord ++ tailWord_978169) baseStart_978169 baseEnd_978169 := by
    simpa [prefixWord, tailWord_978169, baseEnd_978169] using wordTrace_append hprefix tailTrace_978169
  have hstable : (prefixWord ++ tailWord_978169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978169).length < 2 ^ (prefixWord ++ tailWord_978169).sum := by decide
  have hdescent : baseEnd_978169 < baseStart_978169 := by decide
  rcases family_descends (prefixWord ++ tailWord_978169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978172 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 1, 1, 5]
def baseStart_978172 : Nat := 118140960795 + 978172 * 2 ^ 59
def prefixEnd_978172 : Nat := 4983230072969 + 3 ^ 40 * 978172 * 2
def baseEnd_978172 : Nat := 502272398769852131251475

theorem tailTrace_978172 : CollatzResearch.WordTrace tailWord_978172 prefixEnd_978172 502272398769852131251475 := by
  unfold tailWord_978172
  simp only [CollatzResearch.WordTrace]
  refine ⟨17838431906128688661252385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23784575874838251548336513 17838431906128688661252385)
  ·
    refine ⟨13378823929596516495939289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17838431906128688661252385 13378823929596516495939289)
    ·
      refine ⟨10034117947197387371954467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13378823929596516495939289 10034117947197387371954467)
      ·
        refine ⟨15051176920796081057931701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10034117947197387371954467 15051176920796081057931701)
        ·
          refine ⟨1411047836324632599181097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15051176920796081057931701 1411047836324632599181097)
          ·
            refine ⟨1058285877243474449385823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411047836324632599181097 1058285877243474449385823)
            ·
              refine ⟨1587428815865211674078735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058285877243474449385823 1587428815865211674078735)
              ·
                refine ⟨2381143223797817511118103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587428815865211674078735 2381143223797817511118103)
                ·
                  refine ⟨3571714835696726266677155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381143223797817511118103 3571714835696726266677155)
                  ·
                    refine ⟨5357572253545089400015733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3571714835696726266677155 5357572253545089400015733)
                    ·
                      refine ⟨502272398769852131251475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5357572253545089400015733 502272398769852131251475)
                      ·
                        rfl

theorem cell23_978172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_978172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978172 prefixEnd_978172 := by exact prefixLift 978172
  have htrace : WordTrace (prefixWord ++ tailWord_978172) baseStart_978172 baseEnd_978172 := by
    simpa [prefixWord, tailWord_978172, baseEnd_978172] using wordTrace_append hprefix tailTrace_978172
  have hstable : (prefixWord ++ tailWord_978172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978172).length < 2 ^ (prefixWord ++ tailWord_978172).sum := by decide
  have hdescent : baseEnd_978172 < baseStart_978172 := by decide
  rcases family_descends (prefixWord ++ tailWord_978172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978188 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 2, 7]
def baseStart_978188 : Nat := 118140960795 + 978188 * 2 ^ 59
def prefixEnd_978188 : Nat := 4983230072969 + 3 ^ 40 * 978188 * 2
def baseEnd_978188 : Nat := 167426871486774689550467

theorem tailTrace_978188 : CollatzResearch.WordTrace tailWord_978188 prefixEnd_978188 167426871486774689550467 := by
  unfold tailWord_978188
  simp only [CollatzResearch.WordTrace]
  refine ⟨17838723690099706027543609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23784964920132941370058145 17838723690099706027543609)
  ·
    refine ⟨13379042767574779520657707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17838723690099706027543609 13379042767574779520657707)
    ·
      refine ⟨20068564151362169280986561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13379042767574779520657707 20068564151362169280986561)
      ·
        refine ⟨15051423113521626960739921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20068564151362169280986561 15051423113521626960739921)
        ·
          refine ⟨11288567335141220220554941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15051423113521626960739921 11288567335141220220554941)
          ·
            refine ⟨4233212750677957582708103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11288567335141220220554941 4233212750677957582708103)
            ·
              refine ⟨6349819126016936374062155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233212750677957582708103 6349819126016936374062155)
              ·
                refine ⟨9524728689025404561093233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6349819126016936374062155 9524728689025404561093233)
                ·
                  refine ⟨7143546516769053420819925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9524728689025404561093233 7143546516769053420819925)
                  ·
                    refine ⟨167426871486774689550467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7143546516769053420819925 167426871486774689550467)
                    ·
                      rfl

theorem cell23_978188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_978188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978188 prefixEnd_978188 := by exact prefixLift 978188
  have htrace : WordTrace (prefixWord ++ tailWord_978188) baseStart_978188 baseEnd_978188 := by
    simpa [prefixWord, tailWord_978188, baseEnd_978188] using wordTrace_append hprefix tailTrace_978188
  have hstable : (prefixWord ++ tailWord_978188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978188).length < 2 ^ (prefixWord ++ tailWord_978188).sum := by decide
  have hdescent : baseEnd_978188 < baseStart_978188 := by decide
  rcases family_descends (prefixWord ++ tailWord_978188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978202 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3]
def baseStart_978202 : Nat := 118140960795 + 978202 * 2 ^ 59
def prefixEnd_978202 : Nat := 4983230072969 + 3 ^ 40 * 978202 * 2
def baseEnd_978202 : Nat := 502287803189487013876337

theorem tailTrace_978202 : CollatzResearch.WordTrace tailWord_978202 prefixEnd_978202 502287803189487013876337 := by
  unfold tailWord_978202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8919489500537173111524215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23785305334765794964064573 8919489500537173111524215)
  ·
    refine ⟨13379234250805759667286323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8919489500537173111524215 13379234250805759667286323)
    ·
      refine ⟨20068851376208639500929485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13379234250805759667286323 20068851376208639500929485)
      ·
        refine ⟨7525819266078239812848557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20068851376208639500929485 7525819266078239812848557)
        ·
          refine ⟨2822182224779339929818209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7525819266078239812848557 2822182224779339929818209)
          ·
            refine ⟨2116636668584504947363657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2822182224779339929818209 2116636668584504947363657)
            ·
              refine ⟨1587477501438378710522743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116636668584504947363657 1587477501438378710522743)
              ·
                refine ⟨2381216252157568065784115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587477501438378710522743 2381216252157568065784115)
                ·
                  refine ⟨3571824378236352098676173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381216252157568065784115 3571824378236352098676173)
                  ·
                    refine ⟨1339434141838632037003565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3571824378236352098676173 1339434141838632037003565)
                    ·
                      refine ⟨502287803189487013876337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1339434141838632037003565 502287803189487013876337)
                      ·
                        rfl

theorem cell23_978202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_978202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978202 prefixEnd_978202 := by exact prefixLift 978202
  have htrace : WordTrace (prefixWord ++ tailWord_978202) baseStart_978202 baseEnd_978202 := by
    simpa [prefixWord, tailWord_978202, baseEnd_978202] using wordTrace_append hprefix tailTrace_978202
  have hstable : (prefixWord ++ tailWord_978202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978202).length < 2 ^ (prefixWord ++ tailWord_978202).sum := by decide
  have hdescent : baseEnd_978202 < baseStart_978202 := by decide
  rcases family_descends (prefixWord ++ tailWord_978202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978212 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 3, 3, 2]
def baseStart_978212 : Nat := 118140960795 + 978212 * 2 ^ 59
def prefixEnd_978212 : Nat := 4983230072969 + 3 ^ 40 * 978212 * 2
def baseEnd_978212 : Nat := 502292937996031974751291

theorem tailTrace_978212 : CollatzResearch.WordTrace tailWord_978212 prefixEnd_978212 502292937996031974751291 := by
  unfold tailWord_978212
  simp only [CollatzResearch.WordTrace]
  refine ⟨17839161366056232076980445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23785548488074976102640593 17839161366056232076980445)
  ·
    refine ⟨6689685512271087028867667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17839161366056232076980445 6689685512271087028867667)
    ·
      refine ⟨10034528268406630543301501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6689685512271087028867667 10034528268406630543301501)
      ·
        refine ⟨3762948100652486453738063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10034528268406630543301501 3762948100652486453738063)
        ·
          refine ⟨5644422150978729680607095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3762948100652486453738063 5644422150978729680607095)
          ·
            refine ⟨8466633226468094520910643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5644422150978729680607095 8466633226468094520910643)
            ·
              refine ⟨12699949839702141781365965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8466633226468094520910643 12699949839702141781365965)
              ·
                refine ⟨4762481189888303168012237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12699949839702141781365965 4762481189888303168012237)
                ·
                  refine ⟨1785930446208113688004589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4762481189888303168012237 1785930446208113688004589)
                  ·
                    refine ⟨669723917328042633001721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1785930446208113688004589 669723917328042633001721)
                    ·
                      refine ⟨502292937996031974751291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669723917328042633001721 502292937996031974751291)
                      ·
                        rfl

theorem cell23_978212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_978212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978212 prefixEnd_978212 := by exact prefixLift 978212
  have htrace : WordTrace (prefixWord ++ tailWord_978212) baseStart_978212 baseEnd_978212 := by
    simpa [prefixWord, tailWord_978212, baseEnd_978212] using wordTrace_append hprefix tailTrace_978212
  have hstable : (prefixWord ++ tailWord_978212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978212).length < 2 ^ (prefixWord ++ tailWord_978212).sum := by decide
  have hdescent : baseEnd_978212 < baseStart_978212 := by decide
  rcases family_descends (prefixWord ++ tailWord_978212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978229 : List Nat := [1, 3, 3, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_978229 : Nat := 118140960795 + 978229 * 2 ^ 59
def prefixEnd_978229 : Nat := 4983230072969 + 3 ^ 40 * 978229 * 2
def baseEnd_978229 : Nat := 502301667167158408238713

theorem tailTrace_978229 : CollatzResearch.WordTrace tailWord_978229 prefixEnd_978229 502301667167158408238713 := by
  unfold tailWord_978229
  simp only [CollatzResearch.WordTrace]
  refine ⟨35678942773050876057329741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23785961848700584038219827 35678942773050876057329741)
  ·
    refine ⟨13379603539894078521498653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35678942773050876057329741 13379603539894078521498653)
    ·
      refine ⟨5017351327460279445561995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13379603539894078521498653 5017351327460279445561995)
      ·
        refine ⟨7526026991190419168342993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5017351327460279445561995 7526026991190419168342993)
        ·
          refine ⟨5644520243392814376257245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7526026991190419168342993 5644520243392814376257245)
          ·
            refine ⟨2116695091272305391096467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5644520243392814376257245 2116695091272305391096467)
            ·
              refine ⟨3175042636908458086644701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116695091272305391096467 3175042636908458086644701)
              ·
                refine ⟨1190640988840671782491763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3175042636908458086644701 1190640988840671782491763)
                ·
                  refine ⟨1785961483261007673737645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190640988840671782491763 1785961483261007673737645)
                  ·
                    refine ⟨669735556222877877651617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1785961483261007673737645 669735556222877877651617)
                    ·
                      refine ⟨502301667167158408238713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669735556222877877651617 502301667167158408238713)
                      ·
                        rfl

theorem cell23_978229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_978229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978229 prefixEnd_978229 := by exact prefixLift 978229
  have htrace : WordTrace (prefixWord ++ tailWord_978229) baseStart_978229 baseEnd_978229 := by
    simpa [prefixWord, tailWord_978229, baseEnd_978229] using wordTrace_append hprefix tailTrace_978229
  have hstable : (prefixWord ++ tailWord_978229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978229).length < 2 ^ (prefixWord ++ tailWord_978229).sum := by decide
  have hdescent : baseEnd_978229 < baseStart_978229 := by decide
  rcases family_descends (prefixWord ++ tailWord_978229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978253 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_978253 : Nat := 118140960795 + 978253 * 2 ^ 59
def prefixEnd_978253 : Nat := 4983230072969 + 3 ^ 40 * 978253 * 2
def baseEnd_978253 : Nat := 502313990702866314338603

theorem tailTrace_978253 : CollatzResearch.WordTrace tailWord_978253 prefixEnd_978253 502313990702866314338603 := by
  unfold tailWord_978253
  simp only [CollatzResearch.WordTrace]
  refine ⟨35679818124963928156203413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23786545416642618770802275 35679818124963928156203413)
  ·
    refine ⟨1672491474607684132322035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35679818124963928156203413 1672491474607684132322035)
    ·
      refine ⟨2508737211911526198483053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1672491474607684132322035 2508737211911526198483053)
      ·
        refine ⟨940776454466822324431145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2508737211911526198483053 940776454466822324431145)
        ·
          refine ⟨705582340850116743323359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 940776454466822324431145 705582340850116743323359)
          ·
            refine ⟨1058373511275175114985039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705582340850116743323359 1058373511275175114985039)
            ·
              refine ⟨1587560266912762672477559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058373511275175114985039 1587560266912762672477559)
              ·
                refine ⟨2381340400369144008716339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587560266912762672477559 2381340400369144008716339)
                ·
                  refine ⟨3572010600553716013074509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381340400369144008716339 3572010600553716013074509)
                  ·
                    refine ⟨1339503975207643504902941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3572010600553716013074509 1339503975207643504902941)
                    ·
                      refine ⟨502313990702866314338603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1339503975207643504902941 502313990702866314338603)
                      ·
                        rfl

theorem cell23_978253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_978253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978253 prefixEnd_978253 := by exact prefixLift 978253
  have htrace : WordTrace (prefixWord ++ tailWord_978253) baseStart_978253 baseEnd_978253 := by
    simpa [prefixWord, tailWord_978253, baseEnd_978253] using wordTrace_append hprefix tailTrace_978253
  have hstable : (prefixWord ++ tailWord_978253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978253).length < 2 ^ (prefixWord ++ tailWord_978253).sum := by decide
  have hdescent : baseEnd_978253 < baseStart_978253 := by decide
  rcases family_descends (prefixWord ++ tailWord_978253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978295 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 2, 5]
def baseStart_978295 : Nat := 118140960795 + 978295 * 2 ^ 59
def prefixEnd_978295 : Nat := 4983230072969 + 3 ^ 40 * 978295 * 2
def baseEnd_978295 : Nat := 167445185630118383337803

theorem tailTrace_978295 : CollatzResearch.WordTrace tailWord_978295 prefixEnd_978295 167445185630118383337803 := by
  unfold tailWord_978295
  simp only [CollatzResearch.WordTrace]
  refine ⟨35681349990811769329232339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23787566660541179552821559 35681349990811769329232339)
  ·
    refine ⟨53522024986217653993848509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35681349990811769329232339 53522024986217653993848509)
    ·
      refine ⟨20070759369831620247693191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53522024986217653993848509 20070759369831620247693191)
      ·
        refine ⟨30106139054747430371539787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20070759369831620247693191 30106139054747430371539787)
        ·
          refine ⟨45159208582121145557309681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30106139054747430371539787 45159208582121145557309681)
          ·
            refine ⟨33869406436590859167982261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45159208582121145557309681 33869406436590859167982261)
            ·
              refine ⟨3175256853430393046998337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33869406436590859167982261 3175256853430393046998337)
              ·
                refine ⟨2381442640072794785248753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3175256853430393046998337 2381442640072794785248753)
                ·
                  refine ⟨1786081980054596088936565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2381442640072794785248753 1786081980054596088936565)
                  ·
                    refine ⟨167445185630118383337803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1786081980054596088936565 167445185630118383337803)
                    ·
                      rfl

theorem cell23_978295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_978295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978295 prefixEnd_978295 := by exact prefixLift 978295
  have htrace : WordTrace (prefixWord ++ tailWord_978295) baseStart_978295 baseEnd_978295 := by
    simpa [prefixWord, tailWord_978295, baseEnd_978295] using wordTrace_append hprefix tailTrace_978295
  have hstable : (prefixWord ++ tailWord_978295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978295).length < 2 ^ (prefixWord ++ tailWord_978295).sum := by decide
  have hdescent : baseEnd_978295 < baseStart_978295 := by decide
  rcases family_descends (prefixWord ++ tailWord_978295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978315 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 4]
def baseStart_978315 : Nat := 118140960795 + 978315 * 2 ^ 59
def prefixEnd_978315 : Nat := 4983230072969 + 3 ^ 40 * 978315 * 2
def baseEnd_978315 : Nat := 502345826503445071763317

theorem tailTrace_978315 : CollatzResearch.WordTrace tailWord_978315 prefixEnd_978315 502345826503445071763317 := by
  unfold tailWord_978315
  simp only [CollatzResearch.WordTrace]
  refine ⟨35682079450739312744960399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23788052967159541829973599 35682079450739312744960399)
  ·
    refine ⟨53523119176108969117440599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35682079450739312744960399 53523119176108969117440599)
    ·
      refine ⟨80284678764163453676160899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53523119176108969117440599 80284678764163453676160899)
      ·
        refine ⟨120427018146245180514241349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80284678764163453676160899 120427018146245180514241349)
        ·
          refine ⟨22580065902420971346420253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120427018146245180514241349 22580065902420971346420253)
          ·
            refine ⟨8467524713407864254907595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22580065902420971346420253 8467524713407864254907595)
            ·
              refine ⟨12701287070111796382361393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8467524713407864254907595 12701287070111796382361393)
              ·
                refine ⟨9525965302583847286771045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12701287070111796382361393 9525965302583847286771045)
                ·
                  refine ⟨1786118494234471366269571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9525965302583847286771045 1786118494234471366269571)
                  ·
                    refine ⟨2679177741351707049404357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1786118494234471366269571 2679177741351707049404357)
                    ·
                      refine ⟨502345826503445071763317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2679177741351707049404357 502345826503445071763317)
                      ·
                        rfl

theorem cell23_978315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 4].length) (baseStart_978315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978315 prefixEnd_978315 := by exact prefixLift 978315
  have htrace : WordTrace (prefixWord ++ tailWord_978315) baseStart_978315 baseEnd_978315 := by
    simpa [prefixWord, tailWord_978315, baseEnd_978315] using wordTrace_append hprefix tailTrace_978315
  have hstable : (prefixWord ++ tailWord_978315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978315).length < 2 ^ (prefixWord ++ tailWord_978315).sum := by decide
  have hdescent : baseEnd_978315 < baseStart_978315 := by decide
  rcases family_descends (prefixWord ++ tailWord_978315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978349 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_978349 : Nat := 118140960795 + 978349 * 2 ^ 59
def prefixEnd_978349 : Nat := 4983230072969 + 3 ^ 40 * 978349 * 2
def baseEnd_978349 : Nat := 502363284845697938738161

theorem tailTrace_978349 : CollatzResearch.WordTrace tailWord_978349 prefixEnd_978349 502363284845697938738161 := by
  unfold tailWord_978349
  simp only [CollatzResearch.WordTrace]
  refine ⟨35683319532616136551698101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23788879688410757701132067 35683319532616136551698101)
  ·
    refine ⟨3345311206182762801721697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35683319532616136551698101 3345311206182762801721697)
    ·
      refine ⟨2508983404637072101291273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3345311206182762801721697 2508983404637072101291273)
      ·
        refine ⟨1881737553477804075968455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2508983404637072101291273 1881737553477804075968455)
        ·
          refine ⟨2822606330216706113952683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881737553477804075968455 2822606330216706113952683)
          ·
            refine ⟨4233909495325059170929025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822606330216706113952683 4233909495325059170929025)
            ·
              refine ⟨3175432121493794378196769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4233909495325059170929025 3175432121493794378196769)
              ·
                refine ⟨2381574091120345783647577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3175432121493794378196769 2381574091120345783647577)
                ·
                  refine ⟨1786180568340259337735683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2381574091120345783647577 1786180568340259337735683)
                  ·
                    refine ⟨2679270852510389006603525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1786180568340259337735683 2679270852510389006603525)
                    ·
                      refine ⟨502363284845697938738161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2679270852510389006603525 502363284845697938738161)
                      ·
                        rfl

theorem cell23_978349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_978349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978349 prefixEnd_978349 := by exact prefixLift 978349
  have htrace : WordTrace (prefixWord ++ tailWord_978349) baseStart_978349 baseEnd_978349 := by
    simpa [prefixWord, tailWord_978349, baseEnd_978349] using wordTrace_append hprefix tailTrace_978349
  have hstable : (prefixWord ++ tailWord_978349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978349).length < 2 ^ (prefixWord ++ tailWord_978349).sum := by decide
  have hdescent : baseEnd_978349 < baseStart_978349 := by decide
  rcases family_descends (prefixWord ++ tailWord_978349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978359 : List Nat := [1, 1, 3, 1, 3, 2, 3, 4, 1, 4]
def baseStart_978359 : Nat := 118140960795 + 978359 * 2 ^ 59
def prefixEnd_978359 : Nat := 4983230072969 + 3 ^ 40 * 978359 * 2
def baseEnd_978359 : Nat := 167456139884080966537705

theorem tailTrace_978359 : CollatzResearch.WordTrace tailWord_978359 prefixEnd_978359 167456139884080966537705 := by
  unfold tailWord_978359
  simp only [CollatzResearch.WordTrace]
  refine ⟨35683684262579908259562131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23789122841719938839708087 35683684262579908259562131)
  ·
    refine ⟨53525526393869862389343197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35683684262579908259562131 53525526393869862389343197)
    ·
      refine ⟨20072072397701198396003699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53525526393869862389343197 20072072397701198396003699)
      ·
        refine ⟨30108108596551797594005549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20072072397701198396003699 30108108596551797594005549)
        ·
          refine ⟨11290540723706924097752081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30108108596551797594005549 11290540723706924097752081)
          ·
            refine ⟨8467905542780193073314061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11290540723706924097752081 8467905542780193073314061)
            ·
              refine ⟨3175464578542572402492773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8467905542780193073314061 3175464578542572402492773)
              ·
                refine ⟨595399608476732325467395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3175464578542572402492773 595399608476732325467395)
                ·
                  refine ⟨893099412715098488201093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595399608476732325467395 893099412715098488201093)
                  ·
                    refine ⟨167456139884080966537705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 893099412715098488201093 167456139884080966537705)
                    ·
                      rfl

theorem cell23_978359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_978359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978359 prefixEnd_978359 := by exact prefixLift 978359
  have htrace : WordTrace (prefixWord ++ tailWord_978359) baseStart_978359 baseEnd_978359 := by
    simpa [prefixWord, tailWord_978359, baseEnd_978359] using wordTrace_append hprefix tailTrace_978359
  have hstable : (prefixWord ++ tailWord_978359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978359).length < 2 ^ (prefixWord ++ tailWord_978359).sum := by decide
  have hdescent : baseEnd_978359 < baseStart_978359 := by decide
  rcases family_descends (prefixWord ++ tailWord_978359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978415 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 3, 6]
def baseStart_978415 : Nat := 118140960795 + 978415 * 2 ^ 59
def prefixEnd_978415 : Nat := 4983230072969 + 3 ^ 40 * 978415 * 2
def baseEnd_978415 : Nat := 167465724856298226837619

theorem tailTrace_978415 : CollatzResearch.WordTrace tailWord_978415 prefixEnd_978415 167465724856298226837619 := by
  unfold tailWord_978415
  simp only [CollatzResearch.WordTrace]
  refine ⟨35685726750377029823600699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23790484500251353215733799 35685726750377029823600699)
  ·
    refine ⟨53528590125565544735401049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35685726750377029823600699 53528590125565544735401049)
    ·
      refine ⟨40146442594174158551550787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53528590125565544735401049 40146442594174158551550787)
      ·
        refine ⟨60219663891261237827326181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40146442594174158551550787 60219663891261237827326181)
        ·
          refine ⟨11291186979611482092623659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60219663891261237827326181 11291186979611482092623659)
          ·
            refine ⟨16936780469417223138935489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11291186979611482092623659 16936780469417223138935489)
            ·
              refine ⟨12702585352062917354201617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16936780469417223138935489 12702585352062917354201617)
              ·
                refine ⟨9526939014047188015651213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12702585352062917354201617 9526939014047188015651213)
                ·
                  refine ⟨3572602130267695505869205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9526939014047188015651213 3572602130267695505869205)
                  ·
                    refine ⟨167465724856298226837619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3572602130267695505869205 167465724856298226837619)
                    ·
                      rfl

theorem cell23_978415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 6].length) (baseStart_978415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978415 prefixEnd_978415 := by exact prefixLift 978415
  have htrace : WordTrace (prefixWord ++ tailWord_978415) baseStart_978415 baseEnd_978415 := by
    simpa [prefixWord, tailWord_978415, baseEnd_978415] using wordTrace_append hprefix tailTrace_978415
  have hstable : (prefixWord ++ tailWord_978415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978415).length < 2 ^ (prefixWord ++ tailWord_978415).sum := by decide
  have hdescent : baseEnd_978415 < baseStart_978415 := by decide
  rcases family_descends (prefixWord ++ tailWord_978415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978416 : List Nat := [2, 1, 1, 1, 3, 4, 2, 4, 1, 1, 3]
def baseStart_978416 : Nat := 118140960795 + 978416 * 2 ^ 59
def prefixEnd_978416 : Nat := 4983230072969 + 3 ^ 40 * 978416 * 2
def baseEnd_978416 : Nat := 502397688049549176600353

theorem tailTrace_978416 : CollatzResearch.WordTrace tailWord_978416 prefixEnd_978416 502397688049549176600353 := by
  unfold tailWord_978416
  simp only [CollatzResearch.WordTrace]
  refine ⟨17842881611686703497193551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23790508815582271329591401 17842881611686703497193551)
  ·
    refine ⟨26764322417530055245790327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17842881611686703497193551 26764322417530055245790327)
    ·
      refine ⟨40146483626295082868685491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26764322417530055245790327 40146483626295082868685491)
      ·
        refine ⟨60219725439442624303028237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40146483626295082868685491 60219725439442624303028237)
        ·
          refine ⟨22582397039790984113635589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60219725439442624303028237 22582397039790984113635589)
          ·
            refine ⟨4234199444960809521306673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22582397039790984113635589 4234199444960809521306673)
            ·
              refine ⟨3175649583720607140980005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4234199444960809521306673 3175649583720607140980005)
              ·
                refine ⟨595434296947613838933751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3175649583720607140980005 595434296947613838933751)
                ·
                  refine ⟨893151445421420758400627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595434296947613838933751 893151445421420758400627)
                  ·
                    refine ⟨1339727168132131137600941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 893151445421420758400627 1339727168132131137600941)
                    ·
                      refine ⟨502397688049549176600353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1339727168132131137600941 502397688049549176600353)
                      ·
                        rfl

theorem cell23_978416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 1, 1, 3].length) (baseStart_978416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978416 prefixEnd_978416 := by exact prefixLift 978416
  have htrace : WordTrace (prefixWord ++ tailWord_978416) baseStart_978416 baseEnd_978416 := by
    simpa [prefixWord, tailWord_978416, baseEnd_978416] using wordTrace_append hprefix tailTrace_978416
  have hstable : (prefixWord ++ tailWord_978416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978416).length < 2 ^ (prefixWord ++ tailWord_978416).sum := by decide
  have hdescent : baseEnd_978416 < baseStart_978416 := by decide
  rcases family_descends (prefixWord ++ tailWord_978416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978436 : List Nat := [2, 3, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_978436 : Nat := 118140960795 + 978436 * 2 ^ 59
def prefixEnd_978436 : Nat := 4983230072969 + 3 ^ 40 * 978436 * 2
def baseEnd_978436 : Nat := 167469319220879699450087

theorem tailTrace_978436 : CollatzResearch.WordTrace tailWord_978436 prefixEnd_978436 167469319220879699450087 := by
  unfold tailWord_978436
  simp only [CollatzResearch.WordTrace]
  refine ⟨17843246341650475205057581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23790995122200633606743441 17843246341650475205057581)
  ·
    refine ⟨6691217378118928201896593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17843246341650475205057581 6691217378118928201896593)
    ·
      refine ⟨5018413033589196151422445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6691217378118928201896593 5018413033589196151422445)
      ·
        refine ⟨1881904887595948556783417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5018413033589196151422445 1881904887595948556783417)
        ·
          refine ⟨1411428665696961417587563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1881904887595948556783417 1411428665696961417587563)
          ·
            refine ⟨2117142998545442126381345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411428665696961417587563 2117142998545442126381345)
            ·
              refine ⟨1587857248909081594786009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117142998545442126381345 1587857248909081594786009)
              ·
                refine ⟨1190892936681811196089507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587857248909081594786009 1190892936681811196089507)
                ·
                  refine ⟨1786339405022716794134261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190892936681811196089507 1786339405022716794134261)
                  ·
                    refine ⟨167469319220879699450087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1786339405022716794134261 167469319220879699450087)
                    ·
                      rfl

theorem cell23_978436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_978436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978436 prefixEnd_978436 := by exact prefixLift 978436
  have htrace : WordTrace (prefixWord ++ tailWord_978436) baseStart_978436 baseEnd_978436 := by
    simpa [prefixWord, tailWord_978436, baseEnd_978436] using wordTrace_append hprefix tailTrace_978436
  have hstable : (prefixWord ++ tailWord_978436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978436).length < 2 ^ (prefixWord ++ tailWord_978436).sum := by decide
  have hdescent : baseEnd_978436 < baseStart_978436 := by decide
  rcases family_descends (prefixWord ++ tailWord_978436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978439 : List Nat := [1, 1, 4, 3, 2, 1, 1, 4, 1, 1, 4]
def baseStart_978439 : Nat := 118140960795 + 978439 * 2 ^ 59
def prefixEnd_978439 : Nat := 4983230072969 + 3 ^ 40 * 978439 * 2
def baseEnd_978439 : Nat := 502409498104602586612747

theorem tailTrace_978439 : CollatzResearch.WordTrace tailWord_978439 prefixEnd_978439 502409498104602586612747 := by
  unfold tailWord_978439
  simp only [CollatzResearch.WordTrace]
  refine ⟨35686602102290081922474371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23791068068193387948316247 35686602102290081922474371)
  ·
    refine ⟨53529903153435122883711557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35686602102290081922474371 53529903153435122883711557)
    ·
      refine ⟨10036856841269085540695917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53529903153435122883711557 10036856841269085540695917)
      ·
        refine ⟨3763821315475907077760969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10036856841269085540695917 3763821315475907077760969)
        ·
          refine ⟨2822865986606930308320727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3763821315475907077760969 2822865986606930308320727)
          ·
            refine ⟨4234298979910395462481091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822865986606930308320727 4234298979910395462481091)
            ·
              refine ⟨6351448469865593193721637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234298979910395462481091 6351448469865593193721637)
              ·
                refine ⟨1190896588099798723822807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6351448469865593193721637 1190896588099798723822807)
                ·
                  refine ⟨1786344882149698085734211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190896588099798723822807 1786344882149698085734211)
                  ·
                    refine ⟨2679517323224547128601317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1786344882149698085734211 2679517323224547128601317)
                    ·
                      refine ⟨502409498104602586612747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2679517323224547128601317 502409498104602586612747)
                      ·
                        rfl

theorem cell23_978439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_978439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978439 prefixEnd_978439 := by exact prefixLift 978439
  have htrace : WordTrace (prefixWord ++ tailWord_978439) baseStart_978439 baseEnd_978439 := by
    simpa [prefixWord, tailWord_978439, baseEnd_978439] using wordTrace_append hprefix tailTrace_978439
  have hstable : (prefixWord ++ tailWord_978439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978439).length < 2 ^ (prefixWord ++ tailWord_978439).sum := by decide
  have hdescent : baseEnd_978439 < baseStart_978439 := by decide
  rcases family_descends (prefixWord ++ tailWord_978439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978493 : List Nat := [1, 4, 1, 3, 3, 2, 1, 2, 1, 2, 3]
def baseStart_978493 : Nat := 118140960795 + 978493 * 2 ^ 59
def prefixEnd_978493 : Nat := 4983230072969 + 3 ^ 40 * 978493 * 2
def baseEnd_978493 : Nat := 502437226059945375337499

theorem tailTrace_978493 : CollatzResearch.WordTrace tailWord_978493 prefixEnd_978493 502437226059945375337499 := by
  unfold tailWord_978493
  simp only [CollatzResearch.WordTrace]
  refine ⟨35688571644094449144940133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23792381096062966096626755 35688571644094449144940133)
  ·
    refine ⟨6691607183267709214676275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35688571644094449144940133 6691607183267709214676275)
    ·
      refine ⟨10037410774901563822014413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6691607183267709214676275 10037410774901563822014413)
      ·
        refine ⟨3764029040588086433255405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10037410774901563822014413 3764029040588086433255405)
        ·
          refine ⟨1411510890220532412470777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3764029040588086433255405 1411510890220532412470777)
          ·
            refine ⟨1058633167665399309353083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411510890220532412470777 1058633167665399309353083)
            ·
              refine ⟨1587949751498098964029625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058633167665399309353083 1587949751498098964029625)
              ·
                refine ⟨1190962313623574223022219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587949751498098964029625 1190962313623574223022219)
                ·
                  refine ⟨1786443470435361334533329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190962313623574223022219 1786443470435361334533329)
                  ·
                    refine ⟨1339832602826521000899997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1786443470435361334533329 1339832602826521000899997)
                    ·
                      refine ⟨502437226059945375337499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1339832602826521000899997 502437226059945375337499)
                      ·
                        rfl

theorem cell23_978493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_978493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978493 prefixEnd_978493 := by exact prefixLift 978493
  have htrace : WordTrace (prefixWord ++ tailWord_978493) baseStart_978493 baseEnd_978493 := by
    simpa [prefixWord, tailWord_978493, baseEnd_978493] using wordTrace_append hprefix tailTrace_978493
  have hstable : (prefixWord ++ tailWord_978493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978493).length < 2 ^ (prefixWord ++ tailWord_978493).sum := by decide
  have hdescent : baseEnd_978493 < baseStart_978493 := by decide
  rcases family_descends (prefixWord ++ tailWord_978493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978529 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 3, 4, 2]
def baseStart_978529 : Nat := 118140960795 + 978529 * 2 ^ 59
def prefixEnd_978529 : Nat := 4983230072969 + 3 ^ 40 * 978529 * 2
def baseEnd_978529 : Nat := 502455711363507234487333

theorem tailTrace_978529 : CollatzResearch.WordTrace tailWord_978529 prefixEnd_978529 502455711363507234487333 := by
  unfold tailWord_978529
  simp only [CollatzResearch.WordTrace]
  refine ⟨35689884671964027293250641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23793256447976018195500427 35689884671964027293250641)
  ·
    refine ⟨26767413503973020469937981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35689884671964027293250641 26767413503973020469937981)
    ·
      refine ⟨10037780063989882676226743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26767413503973020469937981 10037780063989882676226743)
      ·
        refine ⟨15056670095984824014340115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10037780063989882676226743 15056670095984824014340115)
        ·
          refine ⟨22585005143977236021510173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15056670095984824014340115 22585005143977236021510173)
          ·
            refine ⟨8469376928991463508066315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22585005143977236021510173 8469376928991463508066315)
            ·
              refine ⟨12704065393487195262099473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8469376928991463508066315 12704065393487195262099473)
              ·
                refine ⟨9528049045115396446574605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12704065393487195262099473 9528049045115396446574605)
                ·
                  refine ⟨3573018391918273667465477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9528049045115396446574605 3573018391918273667465477)
                  ·
                    refine ⟨669940948484676312649777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3573018391918273667465477 669940948484676312649777)
                    ·
                      refine ⟨502455711363507234487333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669940948484676312649777 502455711363507234487333)
                      ·
                        rfl

theorem cell23_978529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_978529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978529 prefixEnd_978529 := by exact prefixLift 978529
  have htrace : WordTrace (prefixWord ++ tailWord_978529) baseStart_978529 baseEnd_978529 := by
    simpa [prefixWord, tailWord_978529, baseEnd_978529] using wordTrace_append hprefix tailTrace_978529
  have hstable : (prefixWord ++ tailWord_978529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978529).length < 2 ^ (prefixWord ++ tailWord_978529).sum := by decide
  have hdescent : baseEnd_978529 < baseStart_978529 := by decide
  rcases family_descends (prefixWord ++ tailWord_978529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978546 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 1, 4, 2]
def baseStart_978546 : Nat := 118140960795 + 978546 * 2 ^ 59
def prefixEnd_978546 : Nat := 4983230072969 + 3 ^ 40 * 978546 * 2
def baseEnd_978546 : Nat := 502464440534633667974755

theorem tailTrace_978546 : CollatzResearch.WordTrace tailWord_978546 prefixEnd_978546 502464440534633667974755 := by
  unfold tailWord_978546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8922626178225609799154873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23793669808601626131079661 8922626178225609799154873)
  ·
    refine ⟨6691969633669207349366155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8922626178225609799154873 6691969633669207349366155)
    ·
      refine ⟨10037954450503811024049233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6691969633669207349366155 10037954450503811024049233)
      ·
        refine ⟨7528465837877858268036925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10037954450503811024049233 7528465837877858268036925)
        ·
          refine ⟨2823174689204196850513847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7528465837877858268036925 2823174689204196850513847)
          ·
            refine ⟨4234762033806295275770771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2823174689204196850513847 4234762033806295275770771)
            ·
              refine ⟨6352143050709442913656157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234762033806295275770771 6352143050709442913656157)
              ·
                refine ⟨2382053644016041092621059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6352143050709442913656157 2382053644016041092621059)
                ·
                  refine ⟨3573080466024061638931589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382053644016041092621059 3573080466024061638931589)
                  ·
                    refine ⟨669952587379511557299673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3573080466024061638931589 669952587379511557299673)
                    ·
                      refine ⟨502464440534633667974755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669952587379511557299673 502464440534633667974755)
                      ·
                        rfl

theorem cell23_978546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_978546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978546 prefixEnd_978546 := by exact prefixLift 978546
  have htrace : WordTrace (prefixWord ++ tailWord_978546) baseStart_978546 baseEnd_978546 := by
    simpa [prefixWord, tailWord_978546, baseEnd_978546] using wordTrace_append hprefix tailTrace_978546
  have hstable : (prefixWord ++ tailWord_978546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978546).length < 2 ^ (prefixWord ++ tailWord_978546).sum := by decide
  have hdescent : baseEnd_978546 < baseStart_978546 := by decide
  rcases family_descends (prefixWord ++ tailWord_978546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978569 : List Nat := [1, 2, 1, 1, 4, 1, 3, 5, 5]
def baseStart_978569 : Nat := 118140960795 + 978569 * 2 ^ 59
def prefixEnd_978569 : Nat := 4983230072969 + 3 ^ 40 * 978569 * 2
def baseEnd_978569 : Nat := 55830694509965230887461

theorem tailTrace_978569 : CollatzResearch.WordTrace tailWord_978569 prefixEnd_978569 55830694509965230887461 := by
  unfold tailWord_978569
  simp only [CollatzResearch.WordTrace]
  refine ⟨35691343591819114124706761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23794229061212742749804507 35691343591819114124706761)
  ·
    refine ⟨26768507693864335593530071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35691343591819114124706761 26768507693864335593530071)
    ·
      refine ⟨40152761540796503390295107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26768507693864335593530071 40152761540796503390295107)
      ·
        refine ⟨60229142311194755085442661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40152761540796503390295107 60229142311194755085442661)
        ·
          refine ⟨11292964183349016578520499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60229142311194755085442661 11292964183349016578520499)
          ·
            refine ⟨16939446275023524867780749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11292964183349016578520499 16939446275023524867780749)
            ·
              refine ⟨6352292353133821825417781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16939446275023524867780749 6352292353133821825417781)
              ·
                refine ⟨595527408106295796132917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6352292353133821825417781 595527408106295796132917)
                ·
                  refine ⟨55830694509965230887461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 595527408106295796132917 55830694509965230887461)
                  ·
                    rfl

theorem cell23_978569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 5].length) (baseStart_978569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978569 prefixEnd_978569 := by exact prefixLift 978569
  have htrace : WordTrace (prefixWord ++ tailWord_978569) baseStart_978569 baseEnd_978569 := by
    simpa [prefixWord, tailWord_978569, baseEnd_978569] using wordTrace_append hprefix tailTrace_978569
  have hstable : (prefixWord ++ tailWord_978569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978569).length < 2 ^ (prefixWord ++ tailWord_978569).sum := by decide
  have hdescent : baseEnd_978569 < baseStart_978569 := by decide
  rcases family_descends (prefixWord ++ tailWord_978569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978580 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_978580 : Nat := 118140960795 + 978580 * 2 ^ 59
def prefixEnd_978580 : Nat := 4983230072969 + 3 ^ 40 * 978580 * 2
def baseEnd_978580 : Nat := 502481898876886534949599

theorem tailTrace_978580 : CollatzResearch.WordTrace tailWord_978580 prefixEnd_978580 502481898876886534949599 := by
  unfold tailWord_978580
  simp only [CollatzResearch.WordTrace]
  refine ⟨17845872397389631501678597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23794496529852842002238129 17845872397389631501678597)
  ·
    refine ⟨3346101074510555906564737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17845872397389631501678597 3346101074510555906564737)
    ·
      refine ⟨2509575805882916929923553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3346101074510555906564737 2509575805882916929923553)
      ·
        refine ⟨1882181854412187697442665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2509575805882916929923553 1882181854412187697442665)
        ·
          refine ⟨1411636390809140773081999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1882181854412187697442665 1411636390809140773081999)
          ·
            refine ⟨2117454586213711159622999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411636390809140773081999 2117454586213711159622999)
            ·
              refine ⟨3176181879320566739434499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117454586213711159622999 3176181879320566739434499)
              ·
                refine ⟨4764272818980850109151749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3176181879320566739434499 4764272818980850109151749)
                ·
                  refine ⟨893301153558909395465953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4764272818980850109151749 893301153558909395465953)
                  ·
                    refine ⟨669975865169182046599465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 893301153558909395465953 669975865169182046599465)
                    ·
                      refine ⟨502481898876886534949599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 669975865169182046599465 502481898876886534949599)
                      ·
                        rfl

theorem cell23_978580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_978580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978580 prefixEnd_978580 := by exact prefixLift 978580
  have htrace : WordTrace (prefixWord ++ tailWord_978580) baseStart_978580 baseEnd_978580 := by
    simpa [prefixWord, tailWord_978580, baseEnd_978580] using wordTrace_append hprefix tailTrace_978580
  have hstable : (prefixWord ++ tailWord_978580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978580).length < 2 ^ (prefixWord ++ tailWord_978580).sum := by decide
  have hdescent : baseEnd_978580 < baseStart_978580 := by decide
  rcases family_descends (prefixWord ++ tailWord_978580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978619 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 1, 6, 2]
def baseStart_978619 : Nat := 118140960795 + 978619 * 2 ^ 59
def prefixEnd_978619 : Nat := 4983230072969 + 3 ^ 40 * 978619 * 2
def baseEnd_978619 : Nat := 502501924622411882361919

theorem tailTrace_978619 : CollatzResearch.WordTrace tailWord_978619 prefixEnd_978619 502501924622411882361919 := by
  unfold tailWord_978619
  simp only [CollatzResearch.WordTrace]
  refine ⟨35693167241637972664026911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23795444827758648442684607 35693167241637972664026911)
  ·
    refine ⟨53539750862456958996040367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35693167241637972664026911 53539750862456958996040367)
    ·
      refine ⟨80309626293685438494060551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53539750862456958996040367 80309626293685438494060551)
      ·
        refine ⟨120464439440528157741090827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80309626293685438494060551 120464439440528157741090827)
        ·
          refine ⟨180696659160792236611636241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120464439440528157741090827 180696659160792236611636241)
          ·
            refine ⟨135522494370594177458727181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180696659160792236611636241 135522494370594177458727181)
            ·
              refine ⟨50820935388972816547022693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135522494370594177458727181 50820935388972816547022693)
              ·
                refine ⟨9528925385432403102566755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50820935388972816547022693 9528925385432403102566755)
                ·
                  refine ⟨14293388078148604653850133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9528925385432403102566755 14293388078148604653850133)
                  ·
                    refine ⟨670002566163215843149225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14293388078148604653850133 670002566163215843149225)
                    ·
                      refine ⟨502501924622411882361919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670002566163215843149225 502501924622411882361919)
                      ·
                        rfl

theorem cell23_978619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 6, 2].length) (baseStart_978619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978619 prefixEnd_978619 := by exact prefixLift 978619
  have htrace : WordTrace (prefixWord ++ tailWord_978619) baseStart_978619 baseEnd_978619 := by
    simpa [prefixWord, tailWord_978619, baseEnd_978619] using wordTrace_append hprefix tailTrace_978619
  have hstable : (prefixWord ++ tailWord_978619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978619).length < 2 ^ (prefixWord ++ tailWord_978619).sum := by decide
  have hdescent : baseEnd_978619 < baseStart_978619 := by decide
  rcases family_descends (prefixWord ++ tailWord_978619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978740 : List Nat := [2, 5, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_978740 : Nat := 118140960795 + 978740 * 2 ^ 59
def prefixEnd_978740 : Nat := 4983230072969 + 3 ^ 40 * 978740 * 2
def baseEnd_978740 : Nat := 167521351927201969649621

theorem tailTrace_978740 : CollatzResearch.WordTrace tailWord_978740 prefixEnd_978740 167521351927201969649621 := by
  unfold tailWord_978740
  simp only [CollatzResearch.WordTrace]
  refine ⟨17848790237099805164590837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23798386982799740219454449 17848790237099805164590837)
  ·
    refine ⟨1673324084728106734180391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17848790237099805164590837 1673324084728106734180391)
    ·
      refine ⟨2509986127092160101270587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1673324084728106734180391 2509986127092160101270587)
      ·
        refine ⟨3764979190638240151905881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2509986127092160101270587 3764979190638240151905881)
        ·
          refine ⟨2823734392978680113929411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3764979190638240151905881 2823734392978680113929411)
          ·
            refine ⟨4235601589468020170894117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2823734392978680113929411 4235601589468020170894117)
            ·
              refine ⟨794175298025253782042647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4235601589468020170894117 794175298025253782042647)
              ·
                refine ⟨1191262947037880673063971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794175298025253782042647 1191262947037880673063971)
                ·
                  refine ⟨1786894420556821009595957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1191262947037880673063971 1786894420556821009595957)
                  ·
                    refine ⟨167521351927201969649621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1786894420556821009595957 167521351927201969649621)
                    ·
                      rfl

theorem cell23_978740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_978740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978740 prefixEnd_978740 := by exact prefixLift 978740
  have htrace : WordTrace (prefixWord ++ tailWord_978740) baseStart_978740 baseEnd_978740 := by
    simpa [prefixWord, tailWord_978740, baseEnd_978740] using wordTrace_append hprefix tailTrace_978740
  have hstable : (prefixWord ++ tailWord_978740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978740).length < 2 ^ (prefixWord ++ tailWord_978740).sum := by decide
  have hdescent : baseEnd_978740 < baseStart_978740 := by decide
  rcases family_descends (prefixWord ++ tailWord_978740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978760 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 3, 2, 2]
def baseStart_978760 : Nat := 118140960795 + 978760 * 2 ^ 59
def prefixEnd_978760 : Nat := 4983230072969 + 3 ^ 40 * 978760 * 2
def baseEnd_978760 : Nat := 502574325394695830698771

theorem tailTrace_978760 : CollatzResearch.WordTrace tailWord_978760 prefixEnd_978760 502574325394695830698771 := by
  unfold tailWord_978760
  simp only [CollatzResearch.WordTrace]
  refine ⟨17849154967063576872454867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23798873289418102496606489 17849154967063576872454867)
  ·
    refine ⟨26773732450595365308682301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17849154967063576872454867 26773732450595365308682301)
    ·
      refine ⟨10040149668973261990755863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26773732450595365308682301 10040149668973261990755863)
      ·
        refine ⟨15060224503459892986133795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10040149668973261990755863 15060224503459892986133795)
        ·
          refine ⟨22590336755189839479200693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15060224503459892986133795 22590336755189839479200693)
          ·
            refine ⟨2117844070799047451175065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22590336755189839479200693 2117844070799047451175065)
            ·
              refine ⟨1588383053099285588381299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2117844070799047451175065 1588383053099285588381299)
              ·
                refine ⟨2382574579648928382571949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588383053099285588381299 2382574579648928382571949)
                ·
                  refine ⟨893465467368348143464481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2382574579648928382571949 893465467368348143464481)
                  ·
                    refine ⟨670099100526261107598361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 893465467368348143464481 670099100526261107598361)
                    ·
                      refine ⟨502574325394695830698771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670099100526261107598361 502574325394695830698771)
                      ·
                        rfl

theorem cell23_978760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_978760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978760 prefixEnd_978760 := by exact prefixLift 978760
  have htrace : WordTrace (prefixWord ++ tailWord_978760) baseStart_978760 baseEnd_978760 := by
    simpa [prefixWord, tailWord_978760, baseEnd_978760] using wordTrace_append hprefix tailTrace_978760
  have hstable : (prefixWord ++ tailWord_978760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978760).length < 2 ^ (prefixWord ++ tailWord_978760).sum := by decide
  have hdescent : baseEnd_978760 < baseStart_978760 := by decide
  rcases family_descends (prefixWord ++ tailWord_978760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978770 : List Nat := [3, 2, 2, 1, 1, 4, 3, 1, 2, 4]
def baseStart_978770 : Nat := 118140960795 + 978770 * 2 ^ 59
def prefixEnd_978770 : Nat := 4983230072969 + 3 ^ 40 * 978770 * 2
def baseEnd_978770 : Nat := 167526486733746930524575

theorem tailTrace_978770 : CollatzResearch.WordTrace tailWord_978770 prefixEnd_978770 167526486733746930524575 := by
  unfold tailWord_978770
  simp only [CollatzResearch.WordTrace]
  refine ⟨8924668666022731363193441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23799116442727283635182509 8924668666022731363193441)
  ·
    refine ⟨6693501499517048522395081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8924668666022731363193441 6693501499517048522395081)
    ·
      refine ⟨5020126124637786391796311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6693501499517048522395081 5020126124637786391796311)
      ·
        refine ⟨7530189186956679587694467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5020126124637786391796311 7530189186956679587694467)
        ·
          refine ⟨11295283780435019381541701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7530189186956679587694467 11295283780435019381541701)
          ·
            refine ⟨2117865708831566134039069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11295283780435019381541701 2117865708831566134039069)
            ·
              refine ⟨794199640811837300264651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2117865708831566134039069 794199640811837300264651)
              ·
                refine ⟨1191299461217755950396977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794199640811837300264651 1191299461217755950396977)
                ·
                  refine ⟨893474595913316962797733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1191299461217755950396977 893474595913316962797733)
                  ·
                    refine ⟨167526486733746930524575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 893474595913316962797733 167526486733746930524575)
                    ·
                      rfl

theorem cell23_978770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_978770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978770 prefixEnd_978770 := by exact prefixLift 978770
  have htrace : WordTrace (prefixWord ++ tailWord_978770) baseStart_978770 baseEnd_978770 := by
    simpa [prefixWord, tailWord_978770, baseEnd_978770] using wordTrace_append hprefix tailTrace_978770
  have hstable : (prefixWord ++ tailWord_978770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978770).length < 2 ^ (prefixWord ++ tailWord_978770).sum := by decide
  have hdescent : baseEnd_978770 < baseStart_978770 := by decide
  rcases family_descends (prefixWord ++ tailWord_978770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978773 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 1, 2, 4]
def baseStart_978773 : Nat := 118140960795 + 978773 * 2 ^ 59
def prefixEnd_978773 : Nat := 4983230072969 + 3 ^ 40 * 978773 * 2
def baseEnd_978773 : Nat := 502581000643204279836211

theorem tailTrace_978773 : CollatzResearch.WordTrace tailWord_978773 prefixEnd_978773 502581000643204279836211 := by
  unfold tailWord_978773
  simp only [CollatzResearch.WordTrace]
  refine ⟨35698784083080056965132973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23799189388720037976755315 35698784083080056965132973)
  ·
    refine ⟨13387044031155021361924865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35698784083080056965132973 13387044031155021361924865)
    ·
      refine ⟨10040283023366266021443649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13387044031155021361924865 10040283023366266021443649)
      ·
        refine ⟨7530212267524699516082737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10040283023366266021443649 7530212267524699516082737)
        ·
          refine ⟨5647659200643524637062053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7530212267524699516082737 5647659200643524637062053)
          ·
            refine ⟨1058936100120660869449135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5647659200643524637062053 1058936100120660869449135)
            ·
              refine ⟨1588404150180991304173703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058936100120660869449135 1588404150180991304173703)
              ·
                refine ⟨2382606225271486956260555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588404150180991304173703 2382606225271486956260555)
                ·
                  refine ⟨3573909337907230434390833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382606225271486956260555 3573909337907230434390833)
                  ·
                    refine ⟨2680432003430422825793125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3573909337907230434390833 2680432003430422825793125)
                    ·
                      refine ⟨502581000643204279836211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2680432003430422825793125 502581000643204279836211)
                      ·
                        rfl

theorem cell23_978773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_978773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978773 prefixEnd_978773 := by exact prefixLift 978773
  have htrace : WordTrace (prefixWord ++ tailWord_978773) baseStart_978773 baseEnd_978773 := by
    simpa [prefixWord, tailWord_978773, baseEnd_978773] using wordTrace_append hprefix tailTrace_978773
  have hstable : (prefixWord ++ tailWord_978773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978773).length < 2 ^ (prefixWord ++ tailWord_978773).sum := by decide
  have hdescent : baseEnd_978773 < baseStart_978773 := by decide
  rcases family_descends (prefixWord ++ tailWord_978773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978799 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 4]
def baseStart_978799 : Nat := 118140960795 + 978799 * 2 ^ 59
def prefixEnd_978799 : Nat := 4983230072969 + 3 ^ 40 * 978799 * 2
def baseEnd_978799 : Nat := 502594351140221178111091

theorem tailTrace_978799 : CollatzResearch.WordTrace tailWord_978799 prefixEnd_978799 502594351140221178111091 := by
  unfold tailWord_978799
  simp only [CollatzResearch.WordTrace]
  refine ⟨35699732380985863405579451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23799821587323908937052967 35699732380985863405579451)
  ·
    refine ⟨53549598571478795108369177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35699732380985863405579451 53549598571478795108369177)
    ·
      refine ⟨40162198928609096331276883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53549598571478795108369177 40162198928609096331276883)
      ·
        refine ⟨60243298392913644496915325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40162198928609096331276883 60243298392913644496915325)
        ·
          refine ⟨22591236897342616686343247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60243298392913644496915325 22591236897342616686343247)
          ·
            refine ⟨33886855346013925029514871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22591236897342616686343247 33886855346013925029514871)
            ·
              refine ⟨50830283019020887544272307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33886855346013925029514871 50830283019020887544272307)
              ·
                refine ⟨76245424528531331316408461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50830283019020887544272307 76245424528531331316408461)
                ·
                  refine ⟨28592034198199249243653173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76245424528531331316408461 28592034198199249243653173)
                  ·
                    refine ⟨2680503206081179616592485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28592034198199249243653173 2680503206081179616592485)
                    ·
                      refine ⟨502594351140221178111091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2680503206081179616592485 502594351140221178111091)
                      ·
                        rfl

theorem cell23_978799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_978799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978799 prefixEnd_978799 := by exact prefixLift 978799
  have htrace : WordTrace (prefixWord ++ tailWord_978799) baseStart_978799 baseEnd_978799 := by
    simpa [prefixWord, tailWord_978799, baseEnd_978799] using wordTrace_append hprefix tailTrace_978799
  have hstable : (prefixWord ++ tailWord_978799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978799).length < 2 ^ (prefixWord ++ tailWord_978799).sum := by decide
  have hdescent : baseEnd_978799 < baseStart_978799 := by decide
  rcases family_descends (prefixWord ++ tailWord_978799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978859 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 6]
def baseStart_978859 : Nat := 118140960795 + 978859 * 2 ^ 59
def prefixEnd_978859 : Nat := 4983230072969 + 3 ^ 40 * 978859 * 2
def baseEnd_978859 : Nat := 502625159979490943360815

theorem tailTrace_978859 : CollatzResearch.WordTrace tailWord_978859 prefixEnd_978859 502625159979490943360815 := by
  unfold tailWord_978859
  simp only [CollatzResearch.WordTrace]
  refine ⟨35701920760768493652763631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23801280507178995768509087 35701920760768493652763631)
  ·
    refine ⟨53552881141152740479145447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35701920760768493652763631 53552881141152740479145447)
    ·
      refine ⟨80329321711729110718718171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53552881141152740479145447 80329321711729110718718171)
      ·
        refine ⟨120493982567593666078077257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80329321711729110718718171 120493982567593666078077257)
        ·
          refine ⟨90370486925695249558557943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120493982567593666078077257 90370486925695249558557943)
          ·
            refine ⟨135555730388542874337836915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90370486925695249558557943 135555730388542874337836915)
            ·
              refine ⟨203333595582814311506755373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135555730388542874337836915 203333595582814311506755373)
              ·
                refine ⟨76250098343555366815033265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203333595582814311506755373 76250098343555366815033265)
                ·
                  refine ⟨57187573757666525111274949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76250098343555366815033265 57187573757666525111274949)
                  ·
                    refine ⟨10722670079562473458364053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57187573757666525111274949 10722670079562473458364053)
                    ·
                      refine ⟨502625159979490943360815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10722670079562473458364053 502625159979490943360815)
                      ·
                        rfl

theorem cell23_978859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 6].length) (baseStart_978859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978859 prefixEnd_978859 := by exact prefixLift 978859
  have htrace : WordTrace (prefixWord ++ tailWord_978859) baseStart_978859 baseEnd_978859 := by
    simpa [prefixWord, tailWord_978859, baseEnd_978859] using wordTrace_append hprefix tailTrace_978859
  have hstable : (prefixWord ++ tailWord_978859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978859).length < 2 ^ (prefixWord ++ tailWord_978859).sum := by decide
  have hdescent : baseEnd_978859 < baseStart_978859 := by decide
  rcases family_descends (prefixWord ++ tailWord_978859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978862 : List Nat := [4, 1, 5, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_978862 : Nat := 118140960795 + 978862 * 2 ^ 59
def prefixEnd_978862 : Nat := 4983230072969 + 3 ^ 40 * 978862 * 2
def baseEnd_978862 : Nat := 502626700421454431623303

theorem tailTrace_978862 : CollatzResearch.WordTrace tailWord_978862 prefixEnd_978862 502626700421454431623303 := by
  unfold tailWord_978862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4462753772469703145640355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23801353453171750110081893 4462753772469703145640355)
  ·
    refine ⟨6694130658704554718460533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4462753772469703145640355 6694130658704554718460533)
    ·
      refine ⟨627574749253552004855675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6694130658704554718460533 627574749253552004855675)
      ·
        refine ⟨941362123880328007283513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627574749253552004855675 941362123880328007283513)
        ·
          refine ⟨706021592910246005462635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 941362123880328007283513 706021592910246005462635)
          ·
            refine ⟨1059032389365369008193953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706021592910246005462635 1059032389365369008193953)
            ·
              refine ⟨794274292024026756145465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059032389365369008193953 794274292024026756145465)
              ·
                refine ⟨595705719018020067109099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794274292024026756145465 595705719018020067109099)
                ·
                  refine ⟨893558578527030100663649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595705719018020067109099 893558578527030100663649)
                  ·
                    refine ⟨670168933895272575497737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 893558578527030100663649 670168933895272575497737)
                    ·
                      refine ⟨502626700421454431623303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670168933895272575497737 502626700421454431623303)
                      ·
                        rfl

theorem cell23_978862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_978862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978862 prefixEnd_978862 := by exact prefixLift 978862
  have htrace : WordTrace (prefixWord ++ tailWord_978862) baseStart_978862 baseEnd_978862 := by
    simpa [prefixWord, tailWord_978862, baseEnd_978862] using wordTrace_append hprefix tailTrace_978862
  have hstable : (prefixWord ++ tailWord_978862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978862).length < 2 ^ (prefixWord ++ tailWord_978862).sum := by decide
  have hdescent : baseEnd_978862 < baseStart_978862 := by decide
  rcases family_descends (prefixWord ++ tailWord_978862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978866 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_978866 : Nat := 118140960795 + 978866 * 2 ^ 59
def prefixEnd_978866 : Nat := 4983230072969 + 3 ^ 40 * 978866 * 2
def baseEnd_978866 : Nat := 502628754344072415973283

theorem tailTrace_978866 : CollatzResearch.WordTrace tailWord_978866 prefixEnd_978866 502628754344072415973283 := by
  unfold tailWord_978866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8925544017935783462067113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23801450714495422565512301 8925544017935783462067113)
  ·
    refine ⟨6694158013451837596550335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8925544017935783462067113 6694158013451837596550335)
    ·
      refine ⟨10041237020177756394825503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6694158013451837596550335 10041237020177756394825503)
      ·
        refine ⟨15061855530266634592238255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10041237020177756394825503 15061855530266634592238255)
        ·
          refine ⟨22592783295399951888357383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15061855530266634592238255 22592783295399951888357383)
          ·
            refine ⟨33889174943099927832536075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22592783295399951888357383 33889174943099927832536075)
            ·
              refine ⟨50833762414649891748804113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33889174943099927832536075 50833762414649891748804113)
              ·
                refine ⟨38125321810987418811603085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50833762414649891748804113 38125321810987418811603085)
                ·
                  refine ⟨14296995679120282054351157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38125321810987418811603085 14296995679120282054351157)
                  ·
                    refine ⟨1340343344917526442595421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14296995679120282054351157 1340343344917526442595421)
                    ·
                      refine ⟨502628754344072415973283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1340343344917526442595421 502628754344072415973283)
                      ·
                        rfl

theorem cell23_978866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_978866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978866 prefixEnd_978866 := by exact prefixLift 978866
  have htrace : WordTrace (prefixWord ++ tailWord_978866) baseStart_978866 baseEnd_978866 := by
    simpa [prefixWord, tailWord_978866, baseEnd_978866] using wordTrace_append hprefix tailTrace_978866
  have hstable : (prefixWord ++ tailWord_978866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978866).length < 2 ^ (prefixWord ++ tailWord_978866).sum := by decide
  have hdescent : baseEnd_978866 < baseStart_978866 := by decide
  rcases family_descends (prefixWord ++ tailWord_978866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978873 : List Nat := [1, 2, 1, 4, 2, 1, 3, 4, 5]
def baseStart_978873 : Nat := 118140960795 + 978873 * 2 ^ 59
def prefixEnd_978873 : Nat := 4983230072969 + 3 ^ 40 * 978873 * 2
def baseEnd_978873 : Nat := 55848038745405987620639

theorem tailTrace_978873 : CollatzResearch.WordTrace tailWord_978873 prefixEnd_978873 55848038745405987620639 := by
  unfold tailWord_978873
  simp only [CollatzResearch.WordTrace]
  refine ⟨35702431382717774043773273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23801620921811849362515515 35702431382717774043773273)
  ·
    refine ⟨26776823537038330532829955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35702431382717774043773273 26776823537038330532829955)
    ·
      refine ⟨40165235305557495799244933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26776823537038330532829955 40165235305557495799244933)
      ·
        refine ⟨7530981619792030462358425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40165235305557495799244933 7530981619792030462358425)
        ·
          refine ⟨5648236214844022846768819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7530981619792030462358425 5648236214844022846768819)
          ·
            refine ⟨8472354322266034270153229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5648236214844022846768819 8472354322266034270153229)
            ·
              refine ⟨3177132870849762851307461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8472354322266034270153229 3177132870849762851307461)
              ·
                refine ⟨595712413284330534620149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3177132870849762851307461 595712413284330534620149)
                ·
                  refine ⟨55848038745405987620639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 595712413284330534620149 55848038745405987620639)
                  ·
                    rfl

theorem cell23_978873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 5].length) (baseStart_978873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978873 prefixEnd_978873 := by exact prefixLift 978873
  have htrace : WordTrace (prefixWord ++ tailWord_978873) baseStart_978873 baseEnd_978873 := by
    simpa [prefixWord, tailWord_978873, baseEnd_978873] using wordTrace_append hprefix tailTrace_978873
  have hstable : (prefixWord ++ tailWord_978873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978873).length < 2 ^ (prefixWord ++ tailWord_978873).sum := by decide
  have hdescent : baseEnd_978873 < baseStart_978873 := by decide
  rcases family_descends (prefixWord ++ tailWord_978873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978984 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 3, 4]
def baseStart_978984 : Nat := 118140960795 + 978984 * 2 ^ 59
def prefixEnd_978984 : Nat := 4983230072969 + 3 ^ 40 * 978984 * 2
def baseEnd_978984 : Nat := 167563115020434318099247

theorem tailTrace_978984 : CollatzResearch.WordTrace tailWord_978984 prefixEnd_978984 167563115020434318099247 := by
  unfold tailWord_978984
  simp only [CollatzResearch.WordTrace]
  refine ⟨17853239942657820000532003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23804319923543760000709337 17853239942657820000532003)
  ·
    refine ⟨26779859913986730000798005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17853239942657820000532003 26779859913986730000798005)
    ·
      refine ⟨2510611866936255937574813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26779859913986730000798005 2510611866936255937574813)
      ·
        refine ⟨941479450101095976590555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2510611866936255937574813 941479450101095976590555)
        ·
          refine ⟨1412219175151643964885833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941479450101095976590555 1412219175151643964885833)
          ·
            refine ⟨1059164381363732973664375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1412219175151643964885833 1059164381363732973664375)
            ·
              refine ⟨1588746572045599460496563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059164381363732973664375 1588746572045599460496563)
              ·
                refine ⟨2383119858068399190744845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588746572045599460496563 2383119858068399190744845)
                ·
                  refine ⟨893669946775649696529317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2383119858068399190744845 893669946775649696529317)
                  ·
                    refine ⟨167563115020434318099247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 893669946775649696529317 167563115020434318099247)
                    ·
                      rfl

theorem cell23_978984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_978984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_978984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_978984 prefixEnd_978984 := by exact prefixLift 978984
  have htrace : WordTrace (prefixWord ++ tailWord_978984) baseStart_978984 baseEnd_978984 := by
    simpa [prefixWord, tailWord_978984, baseEnd_978984] using wordTrace_append hprefix tailTrace_978984
  have hstable : (prefixWord ++ tailWord_978984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978984).length < 2 ^ (prefixWord ++ tailWord_978984).sum := by decide
  have hdescent : baseEnd_978984 < baseStart_978984 := by decide
  rcases family_descends (prefixWord ++ tailWord_978984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979040 : List Nat := [2, 1, 1, 3, 2, 3, 1, 4, 2, 4]
def baseStart_979040 : Nat := 118140960795 + 979040 * 2 ^ 59
def prefixEnd_979040 : Nat := 4983230072969 + 3 ^ 40 * 979040 * 2
def baseEnd_979040 : Nat := 167572699992651578399161

theorem tailTrace_979040 : CollatzResearch.WordTrace tailWord_979040 prefixEnd_979040 167572699992651578399161 := by
  unfold tailWord_979040
  simp only [CollatzResearch.WordTrace]
  refine ⟨17854261186556380782551287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23805681582075174376735049 17854261186556380782551287)
  ·
    refine ⟨26781391779834571173826931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17854261186556380782551287 26781391779834571173826931)
    ·
      refine ⟨40172087669751856760740397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26781391779834571173826931 40172087669751856760740397)
      ·
        refine ⟨15064532876156946285277649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40172087669751856760740397 15064532876156946285277649)
        ·
          refine ⟨11298399657117709713958237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15064532876156946285277649 11298399657117709713958237)
          ·
            refine ⟨4236899871419141142734339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11298399657117709713958237 4236899871419141142734339)
            ·
              refine ⟨6355349807128711714101509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4236899871419141142734339 6355349807128711714101509)
              ·
                refine ⟨1191628088836633446394033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6355349807128711714101509 1191628088836633446394033)
                ·
                  refine ⟨893721066627475084795525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1191628088836633446394033 893721066627475084795525)
                  ·
                    refine ⟨167572699992651578399161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 893721066627475084795525 167572699992651578399161)
                    ·
                      rfl

theorem cell23_979040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 2, 4].length) (baseStart_979040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979040 prefixEnd_979040 := by exact prefixLift 979040
  have htrace : WordTrace (prefixWord ++ tailWord_979040) baseStart_979040 baseEnd_979040 := by
    simpa [prefixWord, tailWord_979040, baseEnd_979040] using wordTrace_append hprefix tailTrace_979040
  have hstable : (prefixWord ++ tailWord_979040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979040).length < 2 ^ (prefixWord ++ tailWord_979040).sum := by decide
  have hdescent : baseEnd_979040 < baseStart_979040 := by decide
  rcases family_descends (prefixWord ++ tailWord_979040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979047 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_979047 : Nat := 118140960795 + 979047 * 2 ^ 59
def prefixEnd_979047 : Nat := 4983230072969 + 3 ^ 40 * 979047 * 2
def baseEnd_979047 : Nat := 502721694342536207809951

theorem tailTrace_979047 : CollatzResearch.WordTrace tailWord_979047 prefixEnd_979047 502721694342536207809951 := by
  unfold tailWord_979047
  simp only [CollatzResearch.WordTrace]
  refine ⟨35708777684087401760607395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23805851789391601173738263 35708777684087401760607395)
  ·
    refine ⟨53563166526131102640911093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35708777684087401760607395 53563166526131102640911093)
    ·
      refine ⟨5021546861824790872585415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53563166526131102640911093 5021546861824790872585415)
      ·
        refine ⟨7532320292737186308878123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5021546861824790872585415 7532320292737186308878123)
        ·
          refine ⟨11298480439105779463317185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7532320292737186308878123 11298480439105779463317185)
          ·
            refine ⟨8473860329329334597487889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11298480439105779463317185 8473860329329334597487889)
            ·
              refine ⟨6355395246997000948115917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8473860329329334597487889 6355395246997000948115917)
              ·
                refine ⟨2383273217623875355543469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6355395246997000948115917 2383273217623875355543469)
                ·
                  refine ⟨893727456608953258328801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2383273217623875355543469 893727456608953258328801)
                  ·
                    refine ⟨670295592456714943746601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 893727456608953258328801 670295592456714943746601)
                    ·
                      refine ⟨502721694342536207809951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670295592456714943746601 502721694342536207809951)
                      ·
                        rfl

theorem cell23_979047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_979047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979047 prefixEnd_979047 := by exact prefixLift 979047
  have htrace : WordTrace (prefixWord ++ tailWord_979047) baseStart_979047 baseEnd_979047 := by
    simpa [prefixWord, tailWord_979047, baseEnd_979047] using wordTrace_append hprefix tailTrace_979047
  have hstable : (prefixWord ++ tailWord_979047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979047).length < 2 ^ (prefixWord ++ tailWord_979047).sum := by decide
  have hdescent : baseEnd_979047 < baseStart_979047 := by decide
  rcases family_descends (prefixWord ++ tailWord_979047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979123 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 5]
def baseStart_979123 : Nat := 118140960795 + 979123 * 2 ^ 59
def prefixEnd_979123 : Nat := 4983230072969 + 3 ^ 40 * 979123 * 2
def baseEnd_979123 : Nat := 502760718872277910459601

theorem tailTrace_979123 : CollatzResearch.WordTrace tailWord_979123 prefixEnd_979123 502760718872277910459601 := by
  unfold tailWord_979123
  simp only [CollatzResearch.WordTrace]
  refine ⟨35711549631812066740374023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23807699754541377826916015 35711549631812066740374023)
  ·
    refine ⟨53567324447718100110561035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35711549631812066740374023 53567324447718100110561035)
    ·
      refine ⟨80350986671577150165841553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53567324447718100110561035 80350986671577150165841553)
      ·
        refine ⟨60263240003682862624381165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80350986671577150165841553 60263240003682862624381165)
        ·
          refine ⟨22598715001381073484142937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60263240003682862624381165 22598715001381073484142937)
          ·
            refine ⟨16949036251035805113107203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22598715001381073484142937 16949036251035805113107203)
            ·
              refine ⟨25423554376553707669660805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16949036251035805113107203 25423554376553707669660805)
              ·
                refine ⟨4766916445603820188061401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25423554376553707669660805 4766916445603820188061401)
                ·
                  refine ⟨3575187334202865141046051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4766916445603820188061401 3575187334202865141046051)
                  ·
                    refine ⟨5362781001304297711569077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3575187334202865141046051 5362781001304297711569077)
                    ·
                      refine ⟨502760718872277910459601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5362781001304297711569077 502760718872277910459601)
                      ·
                        rfl

theorem cell23_979123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_979123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979123 prefixEnd_979123 := by exact prefixLift 979123
  have htrace : WordTrace (prefixWord ++ tailWord_979123) baseStart_979123 baseEnd_979123 := by
    simpa [prefixWord, tailWord_979123, baseEnd_979123] using wordTrace_append hprefix tailTrace_979123
  have hstable : (prefixWord ++ tailWord_979123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979123).length < 2 ^ (prefixWord ++ tailWord_979123).sum := by decide
  have hdescent : baseEnd_979123 < baseStart_979123 := by decide
  rcases family_descends (prefixWord ++ tailWord_979123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979140 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_979140 : Nat := 118140960795 + 979140 * 2 ^ 59
def prefixEnd_979140 : Nat := 4983230072969 + 3 ^ 40 * 979140 * 2
def baseEnd_979140 : Nat := 502769448043404343947023

theorem tailTrace_979140 : CollatzResearch.WordTrace tailWord_979140 prefixEnd_979140 502769448043404343947023 := by
  unfold tailWord_979140
  simp only [CollatzResearch.WordTrace]
  refine ⟨17856084836375239321871437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23808113115166985762495249 17856084836375239321871437)
  ·
    refine ⟨6696031813640714745701789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17856084836375239321871437 6696031813640714745701789)
    ·
      refine ⟨2511011930115268029638171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6696031813640714745701789 2511011930115268029638171)
      ·
        refine ⟨3766517895172902044457257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511011930115268029638171 3766517895172902044457257)
        ·
          refine ⟨2824888421379676533342943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3766517895172902044457257 2824888421379676533342943)
          ·
            refine ⟨4237332632069514800014415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824888421379676533342943 4237332632069514800014415)
            ·
              refine ⟨6355998948104272200021623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4237332632069514800014415 6355998948104272200021623)
              ·
                refine ⟨9533998422156408300032435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6355998948104272200021623 9533998422156408300032435)
                ·
                  refine ⟨14300997633234612450048653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9533998422156408300032435 14300997633234612450048653)
                  ·
                    refine ⟨5362874112462979668768245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14300997633234612450048653 5362874112462979668768245)
                    ·
                      refine ⟨502769448043404343947023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5362874112462979668768245 502769448043404343947023)
                      ·
                        rfl

theorem cell23_979140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_979140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979140 prefixEnd_979140 := by exact prefixLift 979140
  have htrace : WordTrace (prefixWord ++ tailWord_979140) baseStart_979140 baseEnd_979140 := by
    simpa [prefixWord, tailWord_979140, baseEnd_979140] using wordTrace_append hprefix tailTrace_979140
  have hstable : (prefixWord ++ tailWord_979140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979140).length < 2 ^ (prefixWord ++ tailWord_979140).sum := by decide
  have hdescent : baseEnd_979140 < baseStart_979140 := by decide
  rcases family_descends (prefixWord ++ tailWord_979140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979154 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_979154 : Nat := 118140960795 + 979154 * 2 ^ 59
def prefixEnd_979154 : Nat := 4983230072969 + 3 ^ 40 * 979154 * 2
def baseEnd_979154 : Nat := 502776636772567289171959

theorem tailTrace_979154 : CollatzResearch.WordTrace tailWord_979154 prefixEnd_979154 502776636772567289171959 := by
  unfold tailWord_979154
  simp only [CollatzResearch.WordTrace]
  refine ⟨8928170073674939758688129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23808453529799839356501677 8928170073674939758688129)
  ·
    refine ⟨6696127555256204819016097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8928170073674939758688129 6696127555256204819016097)
    ·
      refine ⟨5022095666442153614262073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6696127555256204819016097 5022095666442153614262073)
      ·
        refine ⟨3766571749831615210696555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5022095666442153614262073 3766571749831615210696555)
        ·
          refine ⟨5649857624747422816044833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3766571749831615210696555 5649857624747422816044833)
          ·
            refine ⟨4237393218560567112033625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5649857624747422816044833 4237393218560567112033625)
            ·
              refine ⟨3178044913920425334025219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4237393218560567112033625 3178044913920425334025219)
              ·
                refine ⟨4767067370880638001037829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178044913920425334025219 4767067370880638001037829)
                ·
                  refine ⟨893825132040119625194593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4767067370880638001037829 893825132040119625194593)
                  ·
                    refine ⟨670368849030089718895945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 893825132040119625194593 670368849030089718895945)
                    ·
                      refine ⟨502776636772567289171959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670368849030089718895945 502776636772567289171959)
                      ·
                        rfl

theorem cell23_979154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_979154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979154 prefixEnd_979154 := by exact prefixLift 979154
  have htrace : WordTrace (prefixWord ++ tailWord_979154) baseStart_979154 baseEnd_979154 := by
    simpa [prefixWord, tailWord_979154, baseEnd_979154] using wordTrace_append hprefix tailTrace_979154
  have hstable : (prefixWord ++ tailWord_979154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979154).length < 2 ^ (prefixWord ++ tailWord_979154).sum := by decide
  have hdescent : baseEnd_979154 < baseStart_979154 := by decide
  rcases family_descends (prefixWord ++ tailWord_979154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979160 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 7]
def baseStart_979160 : Nat := 118140960795 + 979160 * 2 ^ 59
def prefixEnd_979160 : Nat := 4983230072969 + 3 ^ 40 * 979160 * 2
def baseEnd_979160 : Nat := 55864413072943807299659

theorem tailTrace_979160 : CollatzResearch.WordTrace tailWord_979160 prefixEnd_979160 55864413072943807299659 := by
  unfold tailWord_979160
  simp only [CollatzResearch.WordTrace]
  refine ⟨17856449566339011029735467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23808599421785348039647289 17856449566339011029735467)
  ·
    refine ⟨26784674349508516544603201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17856449566339011029735467 26784674349508516544603201)
    ·
      refine ⟨20088505762131387408452401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26784674349508516544603201 20088505762131387408452401)
      ·
        refine ⟨15066379321598540556339301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20088505762131387408452401 15066379321598540556339301)
        ·
          refine ⟨2824946122799726354313619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15066379321598540556339301 2824946122799726354313619)
          ·
            refine ⟨4237419184199589531470429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824946122799726354313619 4237419184199589531470429)
            ·
              refine ⟨1589032194074846074301411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4237419184199589531470429 1589032194074846074301411)
              ·
                refine ⟨2383548291112269111452117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589032194074846074301411 2383548291112269111452117)
                ·
                  refine ⟨55864413072943807299659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2383548291112269111452117 55864413072943807299659)
                  ·
                    rfl

theorem cell23_979160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 7].length) (baseStart_979160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979160 prefixEnd_979160 := by exact prefixLift 979160
  have htrace : WordTrace (prefixWord ++ tailWord_979160) baseStart_979160 baseEnd_979160 := by
    simpa [prefixWord, tailWord_979160, baseEnd_979160] using wordTrace_append hprefix tailTrace_979160
  have hstable : (prefixWord ++ tailWord_979160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979160).length < 2 ^ (prefixWord ++ tailWord_979160).sum := by decide
  have hdescent : baseEnd_979160 < baseStart_979160 := by decide
  rcases family_descends (prefixWord ++ tailWord_979160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979190 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_979190 : Nat := 118140960795 + 979190 * 2 ^ 59
def prefixEnd_979190 : Nat := 4983230072969 + 3 ^ 40 * 979190 * 2
def baseEnd_979190 : Nat := 167598374025376382773931

theorem tailTrace_979190 : CollatzResearch.WordTrace tailWord_979190 prefixEnd_979190 167598374025376382773931 := by
  unfold tailWord_979190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2232124582660583573941439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23809328881712891455375349 2232124582660583573941439)
  ·
    refine ⟨3348186873990875360912159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2232124582660583573941439 3348186873990875360912159)
    ·
      refine ⟨5022280310986313041368239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3348186873990875360912159 5022280310986313041368239)
      ·
        refine ⟨7533420466479469562052359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5022280310986313041368239 7533420466479469562052359)
        ·
          refine ⟨11300130699719204343078539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7533420466479469562052359 11300130699719204343078539)
          ·
            refine ⟨16950196049578806514617809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11300130699719204343078539 16950196049578806514617809)
            ·
              refine ⟨12712647037184104885963357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16950196049578806514617809 12712647037184104885963357)
              ·
                refine ⟨4767242638944039332236259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12712647037184104885963357 4767242638944039332236259)
                ·
                  refine ⟨7150863958416058998354389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767242638944039332236259 7150863958416058998354389)
                  ·
                    refine ⟨167598374025376382773931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7150863958416058998354389 167598374025376382773931)
                    ·
                      rfl

theorem cell23_979190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_979190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979190 prefixEnd_979190 := by exact prefixLift 979190
  have htrace : WordTrace (prefixWord ++ tailWord_979190) baseStart_979190 baseEnd_979190 := by
    simpa [prefixWord, tailWord_979190, baseEnd_979190] using wordTrace_append hprefix tailTrace_979190
  have hstable : (prefixWord ++ tailWord_979190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979190).length < 2 ^ (prefixWord ++ tailWord_979190).sum := by decide
  have hdescent : baseEnd_979190 < baseStart_979190 := by decide
  rcases family_descends (prefixWord ++ tailWord_979190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979243 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 9]
def baseStart_979243 : Nat := 118140960795 + 979243 * 2 ^ 59
def prefixEnd_979243 : Nat := 4983230072969 + 3 ^ 40 * 979243 * 2
def baseEnd_979243 : Nat := 502822336550817440959049

theorem tailTrace_979243 : CollatzResearch.WordTrace tailWord_979243 prefixEnd_979243 502822336550817440959049 := by
  unfold tailWord_979243
  simp only [CollatzResearch.WordTrace]
  refine ⟨35715926391377327234742383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23810617594251551489828255 35715926391377327234742383)
  ·
    refine ⟨53573889587065990852113575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35715926391377327234742383 53573889587065990852113575)
    ·
      refine ⟨80360834380598986278170363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53573889587065990852113575 80360834380598986278170363)
      ·
        refine ⟨120541251570898479417255545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80360834380598986278170363 120541251570898479417255545)
        ·
          refine ⟨90405938678173859562941659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120541251570898479417255545 90405938678173859562941659)
          ·
            refine ⟨135608908017260789344412489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90405938678173859562941659 135608908017260789344412489)
            ·
              refine ⟨101706681012945592008309367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135608908017260789344412489 101706681012945592008309367)
              ·
                refine ⟨152560021519418388012464051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101706681012945592008309367 152560021519418388012464051)
                ·
                  refine ⟨228840032279127582018696077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152560021519418388012464051 228840032279127582018696077)
                  ·
                    refine ⟨85815012104672843257011029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 228840032279127582018696077 85815012104672843257011029)
                    ·
                      refine ⟨502822336550817440959049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 85815012104672843257011029 502822336550817440959049)
                      ·
                        rfl

theorem cell23_979243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_979243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979243 prefixEnd_979243 := by exact prefixLift 979243
  have htrace : WordTrace (prefixWord ++ tailWord_979243) baseStart_979243 baseEnd_979243 := by
    simpa [prefixWord, tailWord_979243, baseEnd_979243] using wordTrace_append hprefix tailTrace_979243
  have hstable : (prefixWord ++ tailWord_979243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979243).length < 2 ^ (prefixWord ++ tailWord_979243).sum := by decide
  have hdescent : baseEnd_979243 < baseStart_979243 := by decide
  rcases family_descends (prefixWord ++ tailWord_979243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979247 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 3]
def baseStart_979247 : Nat := 118140960795 + 979247 * 2 ^ 59
def prefixEnd_979247 : Nat := 4983230072969 + 3 ^ 40 * 979247 * 2
def baseEnd_979247 : Nat := 502824390473435425309031

theorem tailTrace_979247 : CollatzResearch.WordTrace tailWord_979247 prefixEnd_979247 502824390473435425309031 := by
  unfold tailWord_979247
  simp only [CollatzResearch.WordTrace]
  refine ⟨35716072283362835917887995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23810714855575223945258663 35716072283362835917887995)
  ·
    refine ⟨53574108425044253876831993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35716072283362835917887995 53574108425044253876831993)
    ·
      refine ⟨40180581318783190407623995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53574108425044253876831993 40180581318783190407623995)
      ·
        refine ⟨60270871978174785611435993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40180581318783190407623995 60270871978174785611435993)
        ·
          refine ⟨45203153983631089208576995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60270871978174785611435993 45203153983631089208576995)
          ·
            refine ⟨67804730975446633812865493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45203153983631089208576995 67804730975446633812865493)
            ·
              refine ⟨1589173382237030479989035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 67804730975446633812865493 1589173382237030479989035)
              ·
                refine ⟨2383760073355545719983553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589173382237030479989035 2383760073355545719983553)
                ·
                  refine ⟨1787820055016659289987665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2383760073355545719983553 1787820055016659289987665)
                  ·
                    refine ⟨1340865041262494467490749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1787820055016659289987665 1340865041262494467490749)
                    ·
                      refine ⟨502824390473435425309031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1340865041262494467490749 502824390473435425309031)
                      ·
                        rfl

theorem cell23_979247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 3].length) (baseStart_979247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979247 prefixEnd_979247 := by exact prefixLift 979247
  have htrace : WordTrace (prefixWord ++ tailWord_979247) baseStart_979247 baseEnd_979247 := by
    simpa [prefixWord, tailWord_979247, baseEnd_979247] using wordTrace_append hprefix tailTrace_979247
  have hstable : (prefixWord ++ tailWord_979247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979247).length < 2 ^ (prefixWord ++ tailWord_979247).sum := by decide
  have hdescent : baseEnd_979247 < baseStart_979247 := by decide
  rcases family_descends (prefixWord ++ tailWord_979247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979284 : List Nat := [2, 4, 1, 1, 2, 3, 3, 1, 6]
def baseStart_979284 : Nat := 118140960795 + 979284 * 2 ^ 59
def prefixEnd_979284 : Nat := 4983230072969 + 3 ^ 40 * 979284 * 2
def baseEnd_979284 : Nat := 55871487695294642282929

theorem tailTrace_979284 : CollatzResearch.WordTrace tailWord_979284 prefixEnd_979284 55871487695294642282929 := by
  unfold tailWord_979284
  simp only [CollatzResearch.WordTrace]
  refine ⟨17858710892114395618492453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23811614522819194157989937 17858710892114395618492453)
  ·
    refine ⟨3348508292271449178467335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17858710892114395618492453 3348508292271449178467335)
    ·
      refine ⟨5022762438407173767701003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3348508292271449178467335 5022762438407173767701003)
      ·
        refine ⟨7534143657610760651551505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5022762438407173767701003 7534143657610760651551505)
        ·
          refine ⟨5650607743208070488663629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7534143657610760651551505 5650607743208070488663629)
          ·
            refine ⟨2118977903703026433248861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5650607743208070488663629 2118977903703026433248861)
            ·
              refine ⟨794616713888634912468323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2118977903703026433248861 794616713888634912468323)
              ·
                refine ⟨1191925070832952368702485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794616713888634912468323 1191925070832952368702485)
                ·
                  refine ⟨55871487695294642282929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1191925070832952368702485 55871487695294642282929)
                  ·
                    rfl

theorem cell23_979284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_979284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979284 prefixEnd_979284 := by exact prefixLift 979284
  have htrace : WordTrace (prefixWord ++ tailWord_979284) baseStart_979284 baseEnd_979284 := by
    simpa [prefixWord, tailWord_979284, baseEnd_979284] using wordTrace_append hprefix tailTrace_979284
  have hstable : (prefixWord ++ tailWord_979284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979284).length < 2 ^ (prefixWord ++ tailWord_979284).sum := by decide
  have hdescent : baseEnd_979284 < baseStart_979284 := by decide
  rcases family_descends (prefixWord ++ tailWord_979284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979287 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 3, 5, 2]
def baseStart_979287 : Nat := 118140960795 + 979287 * 2 ^ 59
def prefixEnd_979287 : Nat := 4983230072969 + 3 ^ 40 * 979287 * 2
def baseEnd_979287 : Nat := 502844929699615268808847

theorem tailTrace_979287 : CollatzResearch.WordTrace tailWord_979287 prefixEnd_979287 502844929699615268808847 := by
  unfold tailWord_979287
  simp only [CollatzResearch.WordTrace]
  refine ⟨35717531203217922749344115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23811687468811948499562743 35717531203217922749344115)
  ·
    refine ⟨53576296804826884124016173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35717531203217922749344115 53576296804826884124016173)
    ·
      refine ⟨20091111301810081546506065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53576296804826884124016173 20091111301810081546506065)
      ·
        refine ⟨15068333476357561159879549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20091111301810081546506065 15068333476357561159879549)
        ·
          refine ⟨5650625053634085434954831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15068333476357561159879549 5650625053634085434954831)
          ·
            refine ⟨8475937580451128152432247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650625053634085434954831 8475937580451128152432247)
            ·
              refine ⟨12713906370676692228648371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8475937580451128152432247 12713906370676692228648371)
              ·
                refine ⟨19070859556015038342972557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12713906370676692228648371 19070859556015038342972557)
                ·
                  refine ⟨7151572333505639378614709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19070859556015038342972557 7151572333505639378614709)
                  ·
                    refine ⟨670459906266153691745129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7151572333505639378614709 670459906266153691745129)
                    ·
                      refine ⟨502844929699615268808847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670459906266153691745129 502844929699615268808847)
                      ·
                        rfl

theorem cell23_979287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_979287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979287 prefixEnd_979287 := by exact prefixLift 979287
  have htrace : WordTrace (prefixWord ++ tailWord_979287) baseStart_979287 baseEnd_979287 := by
    simpa [prefixWord, tailWord_979287, baseEnd_979287] using wordTrace_append hprefix tailTrace_979287
  have hstable : (prefixWord ++ tailWord_979287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979287).length < 2 ^ (prefixWord ++ tailWord_979287).sum := by decide
  have hdescent : baseEnd_979287 < baseStart_979287 := by decide
  rcases family_descends (prefixWord ++ tailWord_979287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979304 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_979304 : Nat := 118140960795 + 979304 * 2 ^ 59
def prefixEnd_979304 : Nat := 4983230072969 + 3 ^ 40 * 979304 * 2
def baseEnd_979304 : Nat := 502853658870741702296269

theorem tailTrace_979304 : CollatzResearch.WordTrace tailWord_979304 prefixEnd_979304 502853658870741702296269 := by
  unfold tailWord_979304
  simp only [CollatzResearch.WordTrace]
  refine ⟨17859075622078167326356483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23812100829437556435141977 17859075622078167326356483)
  ·
    refine ⟨26788613433117250989534725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17859075622078167326356483 26788613433117250989534725)
    ·
      refine ⟨5022865018709484560537761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26788613433117250989534725 5022865018709484560537761)
      ·
        refine ⟨3767148764032113420403321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5022865018709484560537761 3767148764032113420403321)
        ·
          refine ⟨2825361573024085065302491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3767148764032113420403321 2825361573024085065302491)
          ·
            refine ⟨4238042359536127597953737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825361573024085065302491 4238042359536127597953737)
            ·
              refine ⟨3178531769652095698465303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4238042359536127597953737 3178531769652095698465303)
              ·
                refine ⟨4767797654478143547697955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178531769652095698465303 4767797654478143547697955)
                ·
                  refine ⟨7151696481717215321546933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767797654478143547697955 7151696481717215321546933)
                  ·
                    refine ⟨670471545160988936395025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7151696481717215321546933 670471545160988936395025)
                    ·
                      refine ⟨502853658870741702296269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670471545160988936395025 502853658870741702296269)
                      ·
                        rfl

theorem cell23_979304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_979304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979304 prefixEnd_979304 := by exact prefixLift 979304
  have htrace : WordTrace (prefixWord ++ tailWord_979304) baseStart_979304 baseEnd_979304 := by
    simpa [prefixWord, tailWord_979304, baseEnd_979304] using wordTrace_append hprefix tailTrace_979304
  have hstable : (prefixWord ++ tailWord_979304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979304).length < 2 ^ (prefixWord ++ tailWord_979304).sum := by decide
  have hdescent : baseEnd_979304 < baseStart_979304 := by decide
  rcases family_descends (prefixWord ++ tailWord_979304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979337 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 1, 1, 5]
def baseStart_979337 : Nat := 118140960795 + 979337 * 2 ^ 59
def prefixEnd_979337 : Nat := 4983230072969 + 3 ^ 40 * 979337 * 2
def baseEnd_979337 : Nat := 502870603732340073183617

theorem tailTrace_979337 : CollatzResearch.WordTrace tailWord_979337 prefixEnd_979337 502870603732340073183617 := by
  unfold tailWord_979337
  simp only [CollatzResearch.WordTrace]
  refine ⟨35719354853036781288664265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23812903235357854192442843 35719354853036781288664265)
  ·
    refine ⟨26789516139777585966498199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35719354853036781288664265 26789516139777585966498199)
    ·
      refine ⟨40184274209666378949747299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26789516139777585966498199 40184274209666378949747299)
      ·
        refine ⟨60276411314499568424620949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40184274209666378949747299 60276411314499568424620949)
        ·
          refine ⟨2825456780367167269904107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60276411314499568424620949 2825456780367167269904107)
          ·
            refine ⟨4238185170550750904856161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825456780367167269904107 4238185170550750904856161)
            ·
              refine ⟨3178638877913063178642121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4238185170550750904856161 3178638877913063178642121)
              ·
                refine ⟨2383979158434797383981591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3178638877913063178642121 2383979158434797383981591)
                ·
                  refine ⟨3575968737652196075972387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383979158434797383981591 3575968737652196075972387)
                  ·
                    refine ⟨5363953106478294113958581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3575968737652196075972387 5363953106478294113958581)
                    ·
                      refine ⟨502870603732340073183617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5363953106478294113958581 502870603732340073183617)
                      ·
                        rfl

theorem cell23_979337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_979337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979337 prefixEnd_979337 := by exact prefixLift 979337
  have htrace : WordTrace (prefixWord ++ tailWord_979337) baseStart_979337 baseEnd_979337 := by
    simpa [prefixWord, tailWord_979337, baseEnd_979337] using wordTrace_append hprefix tailTrace_979337
  have hstable : (prefixWord ++ tailWord_979337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979337).length < 2 ^ (prefixWord ++ tailWord_979337).sum := by decide
  have hdescent : baseEnd_979337 < baseStart_979337 := by decide
  rcases family_descends (prefixWord ++ tailWord_979337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979340 : List Nat := [2, 2, 1, 2, 1, 4, 1, 10]
def baseStart_979340 : Nat := 118140960795 + 979340 * 2 ^ 59
def prefixEnd_979340 : Nat := 4983230072969 + 3 ^ 40 * 979340 * 2
def baseEnd_979340 : Nat := 18624894228677909683189

theorem tailTrace_979340 : CollatzResearch.WordTrace tailWord_979340 prefixEnd_979340 18624894228677909683189 := by
  unfold tailWord_979340
  simp only [CollatzResearch.WordTrace]
  refine ⟨17859732136012956400511737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23812976181350608534015649 17859732136012956400511737)
  ·
    refine ⟨13394799102009717300383803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17859732136012956400511737 13394799102009717300383803)
    ·
      refine ⟨20092198653014575950575705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13394799102009717300383803 20092198653014575950575705)
      ·
        refine ⟨15069148989760931962931779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20092198653014575950575705 15069148989760931962931779)
        ·
          refine ⟨22603723484641397944397669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15069148989760931962931779 22603723484641397944397669)
          ·
            refine ⟨4238198153370262114574563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22603723484641397944397669 4238198153370262114574563)
            ·
              refine ⟨6357297230055393171861845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4238198153370262114574563 6357297230055393171861845)
              ·
                refine ⟨18624894228677909683189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6357297230055393171861845 18624894228677909683189)
                ·
                  rfl

theorem cell23_979340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 10].length) (baseStart_979340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979340 prefixEnd_979340 := by exact prefixLift 979340
  have htrace : WordTrace (prefixWord ++ tailWord_979340) baseStart_979340 baseEnd_979340 := by
    simpa [prefixWord, tailWord_979340, baseEnd_979340] using wordTrace_append hprefix tailTrace_979340
  have hstable : (prefixWord ++ tailWord_979340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979340).length < 2 ^ (prefixWord ++ tailWord_979340).sum := by decide
  have hdescent : baseEnd_979340 < baseStart_979340 := by decide
  rcases family_descends (prefixWord ++ tailWord_979340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979348 : List Nat := [2, 4, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_979348 : Nat := 118140960795 + 979348 * 2 ^ 59
def prefixEnd_979348 : Nat := 4983230072969 + 3 ^ 40 * 979348 * 2
def baseEnd_979348 : Nat := 167625417339846510048689

theorem tailTrace_979348 : CollatzResearch.WordTrace tailWord_979348 prefixEnd_979348 167625417339846510048689 := by
  unfold tailWord_979348
  simp only [CollatzResearch.WordTrace]
  refine ⟨17859878027998465083657349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23813170703997953444876465 17859878027998465083657349)
  ·
    refine ⟨3348727130249712203185753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17859878027998465083657349 3348727130249712203185753)
    ·
      refine ⟨2511545347687284152389315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3348727130249712203185753 2511545347687284152389315)
      ·
        refine ⟨3767318021530926228583973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511545347687284152389315 3767318021530926228583973)
        ·
          refine ⟨706372129037048667859495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3767318021530926228583973 706372129037048667859495)
          ·
            refine ⟨1059558193555573001789243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706372129037048667859495 1059558193555573001789243)
            ·
              refine ⟨1589337290333359502683865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059558193555573001789243 1589337290333359502683865)
              ·
                refine ⟨1192002967750019627012899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1589337290333359502683865 1192002967750019627012899)
                ·
                  refine ⟨1788004451625029440519349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192002967750019627012899 1788004451625029440519349)
                  ·
                    refine ⟨167625417339846510048689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1788004451625029440519349 167625417339846510048689)
                    ·
                      rfl

theorem cell23_979348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_979348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979348 prefixEnd_979348 := by exact prefixLift 979348
  have htrace : WordTrace (prefixWord ++ tailWord_979348) baseStart_979348 baseEnd_979348 := by
    simpa [prefixWord, tailWord_979348, baseEnd_979348] using wordTrace_append hprefix tailTrace_979348
  have hstable : (prefixWord ++ tailWord_979348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979348).length < 2 ^ (prefixWord ++ tailWord_979348).sum := by decide
  have hdescent : baseEnd_979348 < baseStart_979348 := by decide
  rcases family_descends (prefixWord ++ tailWord_979348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979354 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3]
def baseStart_979354 : Nat := 118140960795 + 979354 * 2 ^ 59
def prefixEnd_979354 : Nat := 4983230072969 + 3 ^ 40 * 979354 * 2
def baseEnd_979354 : Nat := 502879332903466506671039

theorem tailTrace_979354 : CollatzResearch.WordTrace tailWord_979354 prefixEnd_979354 502879332903466506671039 := by
  unfold tailWord_979354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8929993723493798298008279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23813316595983462128022077 8929993723493798298008279)
  ·
    refine ⟨13394990585240697447012419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8929993723493798298008279 13394990585240697447012419)
    ·
      refine ⟨20092485877861046170518629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13394990585240697447012419 20092485877861046170518629)
      ·
        refine ⟨3767341102098946156972243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20092485877861046170518629 3767341102098946156972243)
        ·
          refine ⟨5651011653148419235458365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3767341102098946156972243 5651011653148419235458365)
          ·
            refine ⟨2119129369930657213296887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5651011653148419235458365 2119129369930657213296887)
            ·
              refine ⟨3178694054895985819945331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2119129369930657213296887 3178694054895985819945331)
              ·
                refine ⟨4768041082343978729917997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178694054895985819945331 4768041082343978729917997)
                ·
                  refine ⟨1788015405878992023719249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4768041082343978729917997 1788015405878992023719249)
                  ·
                    refine ⟨1341011554409244017789437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1788015405878992023719249 1341011554409244017789437)
                    ·
                      refine ⟨502879332903466506671039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1341011554409244017789437 502879332903466506671039)
                      ·
                        rfl

theorem cell23_979354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_979354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979354 prefixEnd_979354 := by exact prefixLift 979354
  have htrace : WordTrace (prefixWord ++ tailWord_979354) baseStart_979354 baseEnd_979354 := by
    simpa [prefixWord, tailWord_979354, baseEnd_979354] using wordTrace_append hprefix tailTrace_979354
  have hstable : (prefixWord ++ tailWord_979354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979354).length < 2 ^ (prefixWord ++ tailWord_979354).sum := by decide
  have hdescent : baseEnd_979354 < baseStart_979354 := by decide
  rcases family_descends (prefixWord ++ tailWord_979354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979368 : List Nat := [2, 1, 6, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_979368 : Nat := 118140960795 + 979368 * 2 ^ 59
def prefixEnd_979368 : Nat := 4983230072969 + 3 ^ 40 * 979368 * 2
def baseEnd_979368 : Nat := 502886521632629451895975

theorem tailTrace_979368 : CollatzResearch.WordTrace tailWord_979368 prefixEnd_979368 502886521632629451895975 := by
  unfold tailWord_979368
  simp only [CollatzResearch.WordTrace]
  refine ⟨17860242757962236791521379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23813657010616315722028505 17860242757962236791521379)
  ·
    refine ⟨26790364136943355187282069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17860242757962236791521379 26790364136943355187282069)
    ·
      refine ⟨1255798318919219774403847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26790364136943355187282069 1255798318919219774403847)
      ·
        refine ⟨1883697478378829661605771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255798318919219774403847 1883697478378829661605771)
        ·
          refine ⟨2825546217568244492408657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883697478378829661605771 2825546217568244492408657)
          ·
            refine ⟨2119159663176183369306493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2825546217568244492408657 2119159663176183369306493)
            ·
              refine ⟨794684873691068763489935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2119159663176183369306493 794684873691068763489935)
              ·
                refine ⟨1192027310536603145234903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 794684873691068763489935 1192027310536603145234903)
                ·
                  refine ⟨1788040965804904717852355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192027310536603145234903 1788040965804904717852355)
                  ·
                    refine ⟨2682061448707357076778533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1788040965804904717852355 2682061448707357076778533)
                    ·
                      refine ⟨502886521632629451895975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2682061448707357076778533 502886521632629451895975)
                      ·
                        rfl

theorem cell23_979368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_979368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979368 prefixEnd_979368 := by exact prefixLift 979368
  have htrace : WordTrace (prefixWord ++ tailWord_979368) baseStart_979368 baseEnd_979368 := by
    simpa [prefixWord, tailWord_979368, baseEnd_979368] using wordTrace_append hprefix tailTrace_979368
  have hstable : (prefixWord ++ tailWord_979368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979368).length < 2 ^ (prefixWord ++ tailWord_979368).sum := by decide
  have hdescent : baseEnd_979368 < baseStart_979368 := by decide
  rcases family_descends (prefixWord ++ tailWord_979368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979385 : List Nat := [1, 2, 1, 4, 3, 1, 4, 2, 1, 2, 2]
def baseStart_979385 : Nat := 118140960795 + 979385 * 2 ^ 59
def prefixEnd_979385 : Nat := 4983230072969 + 3 ^ 40 * 979385 * 2
def baseEnd_979385 : Nat := 502895250803755885383397

theorem tailTrace_979385 : CollatzResearch.WordTrace tailWord_979385 prefixEnd_979385 502895250803755885383397 := by
  unfold tailWord_979385
  simp only [CollatzResearch.WordTrace]
  refine ⟨35721105556862885486411609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23814070371241923657607739 35721105556862885486411609)
  ·
    refine ⟨26790829167647164114808707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35721105556862885486411609 26790829167647164114808707)
    ·
      refine ⟨40186243751470746172213061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26790829167647164114808707 40186243751470746172213061)
      ·
        refine ⟨7534920703400764907289949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40186243751470746172213061 7534920703400764907289949)
        ·
          refine ⟨2825595263775286840233731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7534920703400764907289949 2825595263775286840233731)
          ·
            refine ⟨4238392895662930260350597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825595263775286840233731 4238392895662930260350597)
            ·
              refine ⟨794698667936799423815737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4238392895662930260350597 794698667936799423815737)
              ·
                refine ⟨596024000952599567861803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794698667936799423815737 596024000952599567861803)
                ·
                  refine ⟨894036001428899351792705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596024000952599567861803 894036001428899351792705)
                  ·
                    refine ⟨670527001071674513844529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 894036001428899351792705 670527001071674513844529)
                    ·
                      refine ⟨502895250803755885383397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670527001071674513844529 502895250803755885383397)
                      ·
                        rfl

theorem cell23_979385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_979385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979385 prefixEnd_979385 := by exact prefixLift 979385
  have htrace : WordTrace (prefixWord ++ tailWord_979385) baseStart_979385 baseEnd_979385 := by
    simpa [prefixWord, tailWord_979385, baseEnd_979385] using wordTrace_append hprefix tailTrace_979385
  have hstable : (prefixWord ++ tailWord_979385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979385).length < 2 ^ (prefixWord ++ tailWord_979385).sum := by decide
  have hdescent : baseEnd_979385 < baseStart_979385 := by decide
  rcases family_descends (prefixWord ++ tailWord_979385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979414 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_979414 : Nat := 118140960795 + 979414 * 2 ^ 59
def prefixEnd_979414 : Nat := 4983230072969 + 3 ^ 40 * 979414 * 2
def baseEnd_979414 : Nat := 502910141742736271920763

theorem tailTrace_979414 : CollatzResearch.WordTrace tailWord_979414 prefixEnd_979414 502910141742736271920763 := by
  unfold tailWord_979414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2232635204609863964951081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23814775515838548959478197 2232635204609863964951081)
  ·
    refine ⟨1674476403457397973713311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2232635204609863964951081 1674476403457397973713311)
    ·
      refine ⟨2511714605186096960569967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1674476403457397973713311 2511714605186096960569967)
      ·
        refine ⟨3767571907779145440854951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511714605186096960569967 3767571907779145440854951)
        ·
          refine ⟨5651357861668718161282427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3767571907779145440854951 5651357861668718161282427)
          ·
            refine ⟨8477036792503077241923641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651357861668718161282427 8477036792503077241923641)
            ·
              refine ⟨6357777594377307931442731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8477036792503077241923641 6357777594377307931442731)
              ·
                refine ⟨9536666391565961897164097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6357777594377307931442731 9536666391565961897164097)
                ·
                  refine ⟨7152499793674471422873073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9536666391565961897164097 7152499793674471422873073)
                  ·
                    refine ⟨5364374845255853567154805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7152499793674471422873073 5364374845255853567154805)
                    ·
                      refine ⟨502910141742736271920763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5364374845255853567154805 502910141742736271920763)
                      ·
                        rfl

theorem cell23_979414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_979414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979414 prefixEnd_979414 := by exact prefixLift 979414
  have htrace : WordTrace (prefixWord ++ tailWord_979414) baseStart_979414 baseEnd_979414 := by
    simpa [prefixWord, tailWord_979414, baseEnd_979414] using wordTrace_append hprefix tailTrace_979414
  have hstable : (prefixWord ++ tailWord_979414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979414).length < 2 ^ (prefixWord ++ tailWord_979414).sum := by decide
  have hdescent : baseEnd_979414 < baseStart_979414 := by decide
  rcases family_descends (prefixWord ++ tailWord_979414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979424 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 1, 4, 2]
def baseStart_979424 : Nat := 118140960795 + 979424 * 2 ^ 59
def prefixEnd_979424 : Nat := 4983230072969 + 3 ^ 40 * 979424 * 2
def baseEnd_979424 : Nat := 502915276549281232795717

theorem tailTrace_979424 : CollatzResearch.WordTrace tailWord_979424 prefixEnd_979424 502915276549281232795717 := by
  unfold tailWord_979424
  simp only [CollatzResearch.WordTrace]
  refine ⟨17861264001860797573540663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23815018669147730098054217 17861264001860797573540663)
  ·
    refine ⟨26791896002791196360310995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17861264001860797573540663 26791896002791196360310995)
    ·
      refine ⟨40187844004186794540466493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26791896002791196360310995 40187844004186794540466493)
      ·
        refine ⟨15070441501570047952674935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40187844004186794540466493 15070441501570047952674935)
        ·
          refine ⟨22605662252355071929012403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15070441501570047952674935 22605662252355071929012403)
          ·
            refine ⟨33908493378532607893518605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22605662252355071929012403 33908493378532607893518605)
            ·
              refine ⟨12715685016949727960069477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33908493378532607893518605 12715685016949727960069477)
              ·
                refine ⟨2384190940678073992513027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12715685016949727960069477 2384190940678073992513027)
                ·
                  refine ⟨3576286411017110988769541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2384190940678073992513027 3576286411017110988769541)
                  ·
                    refine ⟨670553702065708310394289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3576286411017110988769541 670553702065708310394289)
                    ·
                      refine ⟨502915276549281232795717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670553702065708310394289 502915276549281232795717)
                      ·
                        rfl

theorem cell23_979424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_979424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979424 prefixEnd_979424 := by exact prefixLift 979424
  have htrace : WordTrace (prefixWord ++ tailWord_979424) baseStart_979424 baseEnd_979424 := by
    simpa [prefixWord, tailWord_979424, baseEnd_979424] using wordTrace_append hprefix tailTrace_979424
  have hstable : (prefixWord ++ tailWord_979424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979424).length < 2 ^ (prefixWord ++ tailWord_979424).sum := by decide
  have hdescent : baseEnd_979424 < baseStart_979424 := by decide
  rcases family_descends (prefixWord ++ tailWord_979424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979441 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 4, 2, 2]
def baseStart_979441 : Nat := 118140960795 + 979441 * 2 ^ 59
def prefixEnd_979441 : Nat := 4983230072969 + 3 ^ 40 * 979441 * 2
def baseEnd_979441 : Nat := 502924005720407666283139

theorem tailTrace_979441 : CollatzResearch.WordTrace tailWord_979441 prefixEnd_979441 502924005720407666283139 := by
  unfold tailWord_979441
  simp only [CollatzResearch.WordTrace]
  refine ⟨35723148044660007050450177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23815432029773338033633451 35723148044660007050450177)
  ·
    refine ⟨26792361033495005287837633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35723148044660007050450177 26792361033495005287837633)
    ·
      refine ⟨20094270775121253965878225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26792361033495005287837633 20094270775121253965878225)
      ·
        refine ⟨15070703081340940474408669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20094270775121253965878225 15070703081340940474408669)
        ·
          refine ⟨5651513655502852677903251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15070703081340940474408669 5651513655502852677903251)
          ·
            refine ⟨8477270483254279016854877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651513655502852677903251 8477270483254279016854877)
            ·
              refine ⟨3178976431220354631320579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8477270483254279016854877 3178976431220354631320579)
              ·
                refine ⟨4768464646830531946980869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178976431220354631320579 4768464646830531946980869)
                ·
                  refine ⟨894087121280724740058913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4768464646830531946980869 894087121280724740058913)
                  ·
                    refine ⟨670565340960543555044185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 894087121280724740058913 670565340960543555044185)
                    ·
                      refine ⟨502924005720407666283139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670565340960543555044185 502924005720407666283139)
                      ·
                        rfl

theorem cell23_979441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_979441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979441 prefixEnd_979441 := by exact prefixLift 979441
  have htrace : WordTrace (prefixWord ++ tailWord_979441) baseStart_979441 baseEnd_979441 := by
    simpa [prefixWord, tailWord_979441, baseEnd_979441] using wordTrace_append hprefix tailTrace_979441
  have hstable : (prefixWord ++ tailWord_979441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979441).length < 2 ^ (prefixWord ++ tailWord_979441).sum := by decide
  have hdescent : baseEnd_979441 < baseStart_979441 := by decide
  rcases family_descends (prefixWord ++ tailWord_979441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979462 : List Nat := [6, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_979462 : Nat := 118140960795 + 979462 * 2 ^ 59
def prefixEnd_979462 : Nat := 4983230072969 + 3 ^ 40 * 979462 * 2
def baseEnd_979462 : Nat := 502934788814152084120543

theorem tailTrace_979462 : CollatzResearch.WordTrace tailWord_979462 prefixEnd_979462 502934788814152084120543 := by
  unfold tailWord_979462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1116372311799497738655145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23815942651722618424643093 1116372311799497738655145)
  ·
    refine ⟨837279233849623303991359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1116372311799497738655145 837279233849623303991359)
    ·
      refine ⟨1255918850774434955987039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837279233849623303991359 1255918850774434955987039)
      ·
        refine ⟨1883878276161652433980559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255918850774434955987039 1883878276161652433980559)
        ·
          refine ⟨2825817414242478650970839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883878276161652433980559 2825817414242478650970839)
          ·
            refine ⟨4238726121363717976456259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825817414242478650970839 4238726121363717976456259)
            ·
              refine ⟨6358089182045576964684389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4238726121363717976456259 6358089182045576964684389)
              ·
                refine ⟨1192141721633545680878323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6358089182045576964684389 1192141721633545680878323)
                ·
                  refine ⟨1788212582450318521317485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192141721633545680878323 1788212582450318521317485)
                  ·
                    refine ⟨670579718418869445494057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1788212582450318521317485 670579718418869445494057)
                    ·
                      refine ⟨502934788814152084120543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670579718418869445494057 502934788814152084120543)
                      ·
                        rfl

theorem cell23_979462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_979462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979462 prefixEnd_979462 := by exact prefixLift 979462
  have htrace : WordTrace (prefixWord ++ tailWord_979462) baseStart_979462 baseEnd_979462 := by
    simpa [prefixWord, tailWord_979462, baseEnd_979462] using wordTrace_append hprefix tailTrace_979462
  have hstable : (prefixWord ++ tailWord_979462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979462).length < 2 ^ (prefixWord ++ tailWord_979462).sum := by decide
  have hdescent : baseEnd_979462 < baseStart_979462 := by decide
  rcases family_descends (prefixWord ++ tailWord_979462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979477 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 1, 7]
def baseStart_979477 : Nat := 118140960795 + 979477 * 2 ^ 59
def prefixEnd_979477 : Nat := 4983230072969 + 3 ^ 40 * 979477 * 2
def baseEnd_979477 : Nat := 167647497007989841810991

theorem tailTrace_979477 : CollatzResearch.WordTrace tailWord_979477 prefixEnd_979477 167647497007989841810991 := by
  unfold tailWord_979477
  simp only [CollatzResearch.WordTrace]
  refine ⟨35724461072529585198760685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23816307381686390132507123 35724461072529585198760685)
  ·
    refine ⟨13396672902198594449535257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35724461072529585198760685 13396672902198594449535257)
    ·
      refine ⟨10047504676648945837151443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13396672902198594449535257 10047504676648945837151443)
      ·
        refine ⟨15071257014973418755727165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10047504676648945837151443 15071257014973418755727165)
        ·
          refine ⟨5651721380615032033397687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15071257014973418755727165 5651721380615032033397687)
          ·
            refine ⟨8477582070922548050096531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5651721380615032033397687 8477582070922548050096531)
            ·
              refine ⟨12716373106383822075144797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8477582070922548050096531 12716373106383822075144797)
              ·
                refine ⟨4768639914893933278179299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12716373106383822075144797 4768639914893933278179299)
                ·
                  refine ⟨7152959872340899917268949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768639914893933278179299 7152959872340899917268949)
                  ·
                    refine ⟨167647497007989841810991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7152959872340899917268949 167647497007989841810991)
                    ·
                      rfl

theorem cell23_979477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_979477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979477 prefixEnd_979477 := by exact prefixLift 979477
  have htrace : WordTrace (prefixWord ++ tailWord_979477) baseStart_979477 baseEnd_979477 := by
    simpa [prefixWord, tailWord_979477, baseEnd_979477] using wordTrace_append hprefix tailTrace_979477
  have hstable : (prefixWord ++ tailWord_979477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979477).length < 2 ^ (prefixWord ++ tailWord_979477).sum := by decide
  have hdescent : baseEnd_979477 < baseStart_979477 := by decide
  rcases family_descends (prefixWord ++ tailWord_979477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979487 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 5]
def baseStart_979487 : Nat := 118140960795 + 979487 * 2 ^ 59
def prefixEnd_979487 : Nat := 4983230072969 + 3 ^ 40 * 979487 * 2
def baseEnd_979487 : Nat := 502947625830514486307927

theorem tailTrace_979487 : CollatzResearch.WordTrace tailWord_979487 prefixEnd_979487 502947625830514486307927 := by
  unfold tailWord_979487
  simp only [CollatzResearch.WordTrace]
  refine ⟨35724825802493356906624715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23816550534995571271083143 35724825802493356906624715)
  ·
    refine ⟨53587238703740035359937073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35724825802493356906624715 53587238703740035359937073)
    ·
      refine ⟨40190429027805026519952805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53587238703740035359937073 40190429027805026519952805)
      ·
        refine ⟨7535705442713442472491151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40190429027805026519952805 7535705442713442472491151)
        ·
          refine ⟨11303558164070163708736727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7535705442713442472491151 11303558164070163708736727)
          ·
            refine ⟨16955337246105245563105091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11303558164070163708736727 16955337246105245563105091)
            ·
              refine ⟨25433005869157868344657637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16955337246105245563105091 25433005869157868344657637)
              ·
                refine ⟨4768688600467100314623307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25433005869157868344657637 4768688600467100314623307)
                ·
                  refine ⟨7153032900700650471934961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768688600467100314623307 7153032900700650471934961)
                  ·
                    refine ⟨5364774675525487853951221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7153032900700650471934961 5364774675525487853951221)
                    ·
                      refine ⟨502947625830514486307927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5364774675525487853951221 502947625830514486307927)
                      ·
                        rfl

theorem cell23_979487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_979487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979487 prefixEnd_979487 := by exact prefixLift 979487
  have htrace : WordTrace (prefixWord ++ tailWord_979487) baseStart_979487 baseEnd_979487 := by
    simpa [prefixWord, tailWord_979487, baseEnd_979487] using wordTrace_append hprefix tailTrace_979487
  have hstable : (prefixWord ++ tailWord_979487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979487).length < 2 ^ (prefixWord ++ tailWord_979487).sum := by decide
  have hdescent : baseEnd_979487 < baseStart_979487 := by decide
  rcases family_descends (prefixWord ++ tailWord_979487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979498 : List Nat := [3, 1, 4, 1, 1, 3, 3, 2, 5]
def baseStart_979498 : Nat := 118140960795 + 979498 * 2 ^ 59
def prefixEnd_979498 : Nat := 4983230072969 + 3 ^ 40 * 979498 * 2
def baseEnd_979498 : Nat := 55883697124190438141153

theorem tailTrace_979498 : CollatzResearch.WordTrace tailWord_979498 prefixEnd_979498 55883697124190438141153 := by
  unfold tailWord_979498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8931306751363376446318787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23816818003635670523516765 8931306751363376446318787)
  ·
    refine ⟨13396960127045064669478181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8931306751363376446318787 13396960127045064669478181)
    ·
      refine ⟨2511930023820949625527159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13396960127045064669478181 2511930023820949625527159)
      ·
        refine ⟨3767895035731424438290739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511930023820949625527159 3767895035731424438290739)
        ·
          refine ⟨5651842553597136657436109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3767895035731424438290739 5651842553597136657436109)
          ·
            refine ⟨2119440957598926246538541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5651842553597136657436109 2119440957598926246538541)
            ·
              refine ⟨794790359099597342451953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2119440957598926246538541 794790359099597342451953)
              ·
                refine ⟨596092769324698006838965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794790359099597342451953 596092769324698006838965)
                ·
                  refine ⟨55883697124190438141153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 596092769324698006838965 55883697124190438141153)
                  ·
                    rfl

theorem cell23_979498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 5].length) (baseStart_979498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979498 prefixEnd_979498 := by exact prefixLift 979498
  have htrace : WordTrace (prefixWord ++ tailWord_979498) baseStart_979498 baseEnd_979498 := by
    simpa [prefixWord, tailWord_979498, baseEnd_979498] using wordTrace_append hprefix tailTrace_979498
  have hstable : (prefixWord ++ tailWord_979498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979498).length < 2 ^ (prefixWord ++ tailWord_979498).sum := by decide
  have hdescent : baseEnd_979498 < baseStart_979498 := by decide
  rcases family_descends (prefixWord ++ tailWord_979498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979534 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_979534 : Nat := 118140960795 + 979534 * 2 ^ 59
def prefixEnd_979534 : Nat := 4983230072969 + 3 ^ 40 * 979534 * 2
def baseEnd_979534 : Nat := 502971759421275802420211

theorem tailTrace_979534 : CollatzResearch.WordTrace tailWord_979534 prefixEnd_979534 502971759421275802420211 := by
  unfold tailWord_979534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4465817504165385491698207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23817693355548722622390437 4465817504165385491698207)
  ·
    refine ⟨6698726256248078237547311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4465817504165385491698207 6698726256248078237547311)
    ·
      refine ⟨10048089384372117356320967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6698726256248078237547311 10048089384372117356320967)
      ·
        refine ⟨15072134076558176034481451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10048089384372117356320967 15072134076558176034481451)
        ·
          refine ⟨22608201114837264051722177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15072134076558176034481451 22608201114837264051722177)
          ·
            refine ⟨16956150836127948038791633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22608201114837264051722177 16956150836127948038791633)
            ·
              refine ⟨12717113127095961029093725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16956150836127948038791633 12717113127095961029093725)
              ·
                refine ⟨4768917422660985385910147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12717113127095961029093725 4768917422660985385910147)
                ·
                  refine ⟨7153376133991478078865221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768917422660985385910147 7153376133991478078865221)
                  ·
                    refine ⟨1341258025123402139787229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7153376133991478078865221 1341258025123402139787229)
                    ·
                      refine ⟨502971759421275802420211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1341258025123402139787229 502971759421275802420211)
                      ·
                        rfl

theorem cell23_979534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_979534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979534 prefixEnd_979534 := by exact prefixLift 979534
  have htrace : WordTrace (prefixWord ++ tailWord_979534) baseStart_979534 baseEnd_979534 := by
    simpa [prefixWord, tailWord_979534, baseEnd_979534] using wordTrace_append hprefix tailTrace_979534
  have hstable : (prefixWord ++ tailWord_979534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979534).length < 2 ^ (prefixWord ++ tailWord_979534).sum := by decide
  have hdescent : baseEnd_979534 < baseStart_979534 := by decide
  rcases family_descends (prefixWord ++ tailWord_979534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979584 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 3, 5]
def baseStart_979584 : Nat := 118140960795 + 979584 * 2 ^ 59
def prefixEnd_979584 : Nat := 4983230072969 + 3 ^ 40 * 979584 * 2
def baseEnd_979584 : Nat := 167665811151333535598327

theorem tailTrace_979584 : CollatzResearch.WordTrace tailWord_979584 prefixEnd_979584 167665811151333535598327 := by
  unfold tailWord_979584
  simp only [CollatzResearch.WordTrace]
  refine ⟨17864181841570971236452903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23818909122094628315270537 17864181841570971236452903)
  ·
    refine ⟨26796272762356456854679355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17864181841570971236452903 26796272762356456854679355)
    ·
      refine ⟨40194409143534685282019033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26796272762356456854679355 40194409143534685282019033)
      ·
        refine ⟨30145806857651013961514275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40194409143534685282019033 30145806857651013961514275)
        ·
          refine ⟨45218710286476520942271413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30145806857651013961514275 45218710286476520942271413)
          ·
            refine ⟨4239254089357173838337945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45218710286476520942271413 4239254089357173838337945)
            ·
              refine ⟨3179440567017880378753459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4239254089357173838337945 3179440567017880378753459)
              ·
                refine ⟨4769160850526820568130189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3179440567017880378753459 4769160850526820568130189)
                ·
                  refine ⟨1788435318947557713048821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4769160850526820568130189 1788435318947557713048821)
                  ·
                    refine ⟨167665811151333535598327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1788435318947557713048821 167665811151333535598327)
                    ·
                      rfl

theorem cell23_979584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 3, 5].length) (baseStart_979584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979584 prefixEnd_979584 := by exact prefixLift 979584
  have htrace : WordTrace (prefixWord ++ tailWord_979584) baseStart_979584 baseEnd_979584 := by
    simpa [prefixWord, tailWord_979584, baseEnd_979584] using wordTrace_append hprefix tailTrace_979584
  have hstable : (prefixWord ++ tailWord_979584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979584).length < 2 ^ (prefixWord ++ tailWord_979584).sum := by decide
  have hdescent : baseEnd_979584 < baseStart_979584 := by decide
  rcases family_descends (prefixWord ++ tailWord_979584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979591 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 1, 5, 2]
def baseStart_979591 : Nat := 118140960795 + 979591 * 2 ^ 59
def prefixEnd_979591 : Nat := 4983230072969 + 3 ^ 40 * 979591 * 2
def baseEnd_979591 : Nat := 503001027818582079407449

theorem tailTrace_979591 : CollatzResearch.WordTrace tailWord_979591 prefixEnd_979591 503001027818582079407449 := by
  unfold tailWord_979591
  simp only [CollatzResearch.WordTrace]
  refine ⟨35728618994116582668410627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23819079329411055112273751 35728618994116582668410627)
  ·
    refine ⟨53592928491174874002615941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35728618994116582668410627 53592928491174874002615941)
    ·
      refine ⟨10048674092095288875490489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53592928491174874002615941 10048674092095288875490489)
      ·
        refine ⟨7536505569071466656617867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10048674092095288875490489 7536505569071466656617867)
        ·
          refine ⟨11304758353607199984926801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7536505569071466656617867 11304758353607199984926801)
          ·
            refine ⟨8478568765205399988695101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11304758353607199984926801 8478568765205399988695101)
            ·
              refine ⟨3179463286952024995760663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8478568765205399988695101 3179463286952024995760663)
              ·
                refine ⟨4769194930428037493640995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3179463286952024995760663 4769194930428037493640995)
                ·
                  refine ⟨7153792395642056240461493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4769194930428037493640995 7153792395642056240461493)
                  ·
                    refine ⟨670668037091442772543265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7153792395642056240461493 670668037091442772543265)
                    ·
                      refine ⟨503001027818582079407449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670668037091442772543265 503001027818582079407449)
                      ·
                        rfl

theorem cell23_979591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_979591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979591 prefixEnd_979591 := by exact prefixLift 979591
  have htrace : WordTrace (prefixWord ++ tailWord_979591) baseStart_979591 baseEnd_979591 := by
    simpa [prefixWord, tailWord_979591, baseEnd_979591] using wordTrace_append hprefix tailTrace_979591
  have hstable : (prefixWord ++ tailWord_979591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979591).length < 2 ^ (prefixWord ++ tailWord_979591).sum := by decide
  have hdescent : baseEnd_979591 < baseStart_979591 := by decide
  rcases family_descends (prefixWord ++ tailWord_979591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979631 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 1, 6]
def baseStart_979631 : Nat := 118140960795 + 979631 * 2 ^ 59
def prefixEnd_979631 : Nat := 4983230072969 + 3 ^ 40 * 979631 * 2
def baseEnd_979631 : Nat := 167673855681587307635755

theorem tailTrace_979631 : CollatzResearch.WordTrace tailWord_979631 prefixEnd_979631 167673855681587307635755 := by
  unfold tailWord_979631
  simp only [CollatzResearch.WordTrace]
  refine ⟨35730077913971669499866747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23820051942647779666577831 35730077913971669499866747)
  ·
    refine ⟨53595116870957504249800121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35730077913971669499866747 53595116870957504249800121)
    ·
      refine ⟨40196337653218128187350091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53595116870957504249800121 40196337653218128187350091)
      ·
        refine ⟨60294506479827192281025137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40196337653218128187350091 60294506479827192281025137)
        ·
          refine ⟨45220879859870394210768853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60294506479827192281025137 45220879859870394210768853)
          ·
            refine ⟨1059864371715712364314895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 45220879859870394210768853 1059864371715712364314895)
            ·
              refine ⟨1589796557573568546472343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059864371715712364314895 1589796557573568546472343)
              ·
                refine ⟨2384694836360352819708515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589796557573568546472343 2384694836360352819708515)
                ·
                  refine ⟨3577042254540529229562773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2384694836360352819708515 3577042254540529229562773)
                  ·
                    refine ⟨167673855681587307635755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3577042254540529229562773 167673855681587307635755)
                    ·
                      rfl

theorem cell23_979631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 6].length) (baseStart_979631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979631 prefixEnd_979631 := by exact prefixLift 979631
  have htrace : WordTrace (prefixWord ++ tailWord_979631) baseStart_979631 baseEnd_979631 := by
    simpa [prefixWord, tailWord_979631, baseEnd_979631] using wordTrace_append hprefix tailTrace_979631
  have hstable : (prefixWord ++ tailWord_979631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979631).length < 2 ^ (prefixWord ++ tailWord_979631).sum := by decide
  have hdescent : baseEnd_979631 < baseStart_979631 := by decide
  rcases family_descends (prefixWord ++ tailWord_979631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979644 : List Nat := [2, 2, 2, 3, 1, 1, 3, 9]
def baseStart_979644 : Nat := 118140960795 + 979644 * 2 ^ 59
def prefixEnd_979644 : Nat := 4983230072969 + 3 ^ 40 * 979644 * 2
def baseEnd_979644 : Nat := 18630675640491495260915

theorem tailTrace_979644 : CollatzResearch.WordTrace tailWord_979644 prefixEnd_979644 18630675640491495260915 := by
  unfold tailWord_979644
  simp only [CollatzResearch.WordTrace]
  refine ⟨17865276031462286360044993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23820368041949715146726657 17865276031462286360044993)
  ·
    refine ⟨13398957023596714770033745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17865276031462286360044993 13398957023596714770033745)
    ·
      refine ⟨10049217767697536077525309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13398957023596714770033745 10049217767697536077525309)
      ·
        refine ⟨3768456662886576029071991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10049217767697536077525309 3768456662886576029071991)
        ·
          refine ⟨5652684994329864043607987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768456662886576029071991 5652684994329864043607987)
          ·
            refine ⟨8479027491494796065411981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5652684994329864043607987 8479027491494796065411981)
            ·
              refine ⟨3179635309310548524529493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8479027491494796065411981 3179635309310548524529493)
              ·
                refine ⟨18630675640491495260915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3179635309310548524529493 18630675640491495260915)
                ·
                  rfl

theorem cell23_979644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 9].length) (baseStart_979644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979644 prefixEnd_979644 := by exact prefixLift 979644
  have htrace : WordTrace (prefixWord ++ tailWord_979644) baseStart_979644 baseEnd_979644 := by
    simpa [prefixWord, tailWord_979644, baseEnd_979644] using wordTrace_append hprefix tailTrace_979644
  have hstable : (prefixWord ++ tailWord_979644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979644).length < 2 ^ (prefixWord ++ tailWord_979644).sum := by decide
  have hdescent : baseEnd_979644 < baseStart_979644 := by decide
  rcases family_descends (prefixWord ++ tailWord_979644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979655 : List Nat := [1, 1, 4, 1, 1, 1, 2, 7, 1, 2, 2]
def baseStart_979655 : Nat := 118140960795 + 979655 * 2 ^ 59
def prefixEnd_979655 : Nat := 4983230072969 + 3 ^ 40 * 979655 * 2
def baseEnd_979655 : Nat := 503033890580469829007155

theorem tailTrace_979655 : CollatzResearch.WordTrace tailWord_979655 prefixEnd_979655 503033890580469829007155 := by
  unfold tailWord_979655
  simp only [CollatzResearch.WordTrace]
  refine ⟨35730953265884721598740419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23820635510589814399160279 35730953265884721598740419)
  ·
    refine ⟨53596429898827082398110629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35730953265884721598740419 53596429898827082398110629)
    ·
      refine ⟨10049330606030077949645743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53596429898827082398110629 10049330606030077949645743)
      ·
        refine ⟨15073995909045116924468615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10049330606030077949645743 15073995909045116924468615)
        ·
          refine ⟨22610993863567675386702923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15073995909045116924468615 22610993863567675386702923)
          ·
            refine ⟨33916490795351513080054385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22610993863567675386702923 33916490795351513080054385)
            ·
              refine ⟨25437368096513634810040789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33916490795351513080054385 25437368096513634810040789)
              ·
                refine ⟨596188314762038315860331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25437368096513634810040789 596188314762038315860331)
                ·
                  refine ⟨894282472143057473790497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596188314762038315860331 894282472143057473790497)
                  ·
                    refine ⟨670711854107293105342873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 894282472143057473790497 670711854107293105342873)
                    ·
                      refine ⟨503033890580469829007155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670711854107293105342873 503033890580469829007155)
                      ·
                        rfl

theorem cell23_979655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_979655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979655 prefixEnd_979655 := by exact prefixLift 979655
  have htrace : WordTrace (prefixWord ++ tailWord_979655) baseStart_979655 baseEnd_979655 := by
    simpa [prefixWord, tailWord_979655, baseEnd_979655] using wordTrace_append hprefix tailTrace_979655
  have hstable : (prefixWord ++ tailWord_979655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979655).length < 2 ^ (prefixWord ++ tailWord_979655).sum := by decide
  have hdescent : baseEnd_979655 < baseStart_979655 := by decide
  rcases family_descends (prefixWord ++ tailWord_979655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979658 : List Nat := [3, 1, 2, 1, 4, 1, 2, 3, 1, 2, 3]
def baseStart_979658 : Nat := 118140960795 + 979658 * 2 ^ 59
def prefixEnd_979658 : Nat := 4983230072969 + 3 ^ 40 * 979658 * 2
def baseEnd_979658 : Nat := 503035431022433317269641

theorem tailTrace_979658 : CollatzResearch.WordTrace tailWord_979658 prefixEnd_979658 503035431022433317269641 := by
  unfold tailWord_979658
  simp only [CollatzResearch.WordTrace]
  refine ⟨8932765671218463277774907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23820708456582568740733085 8932765671218463277774907)
  ·
    refine ⟨13399148506827694916662361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8932765671218463277774907 13399148506827694916662361)
    ·
      refine ⟨10049361380120771187496771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13399148506827694916662361 10049361380120771187496771)
      ·
        refine ⟨15074042070181156781245157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10049361380120771187496771 15074042070181156781245157)
        ·
          refine ⟨2826382888158966896483467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15074042070181156781245157 2826382888158966896483467)
          ·
            refine ⟨4239574332238450344725201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2826382888158966896483467 4239574332238450344725201)
            ·
              refine ⟨3179680749178837758543901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4239574332238450344725201 3179680749178837758543901)
              ·
                refine ⟨1192380280942064159453963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3179680749178837758543901 1192380280942064159453963)
                ·
                  refine ⟨1788570421413096239180945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192380280942064159453963 1788570421413096239180945)
                  ·
                    refine ⟨1341427816059822179385709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1788570421413096239180945 1341427816059822179385709)
                    ·
                      refine ⟨503035431022433317269641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1341427816059822179385709 503035431022433317269641)
                      ·
                        rfl

theorem cell23_979658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_979658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979658 prefixEnd_979658 := by exact prefixLift 979658
  have htrace : WordTrace (prefixWord ++ tailWord_979658) baseStart_979658 baseEnd_979658 := by
    simpa [prefixWord, tailWord_979658, baseEnd_979658] using wordTrace_append hprefix tailTrace_979658
  have hstable : (prefixWord ++ tailWord_979658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979658).length < 2 ^ (prefixWord ++ tailWord_979658).sum := by decide
  have hdescent : baseEnd_979658 < baseStart_979658 := by decide
  rcases family_descends (prefixWord ++ tailWord_979658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979674 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 2, 7]
def baseStart_979674 : Nat := 118140960795 + 979674 * 2 ^ 59
def prefixEnd_979674 : Nat := 4983230072969 + 3 ^ 40 * 979674 * 2
def baseEnd_979674 : Nat := 167681215570968418223189

theorem tailTrace_979674 : CollatzResearch.WordTrace tailWord_979674 prefixEnd_979674 167681215570968418223189 := by
  unfold tailWord_979674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8932911563203971960920519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23821097501877258562454717 8932911563203971960920519)
  ·
    refine ⟨13399367344805957941380779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8932911563203971960920519 13399367344805957941380779)
    ·
      refine ⟨20099051017208936912071169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13399367344805957941380779 20099051017208936912071169)
      ·
        refine ⟨15074288262906702684053377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20099051017208936912071169 15074288262906702684053377)
        ·
          refine ⟨11305716197180027013040033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15074288262906702684053377 11305716197180027013040033)
          ·
            refine ⟨8479287147885020259780025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11305716197180027013040033 8479287147885020259780025)
            ·
              refine ⟨6359465360913765194835019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8479287147885020259780025 6359465360913765194835019)
              ·
                refine ⟨9539198041370647792252529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6359465360913765194835019 9539198041370647792252529)
                ·
                  refine ⟨7154398531027985844189397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9539198041370647792252529 7154398531027985844189397)
                  ·
                    refine ⟨167681215570968418223189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7154398531027985844189397 167681215570968418223189)
                    ·
                      rfl

theorem cell23_979674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_979674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979674 prefixEnd_979674 := by exact prefixLift 979674
  have htrace : WordTrace (prefixWord ++ tailWord_979674) baseStart_979674 baseEnd_979674 := by
    simpa [prefixWord, tailWord_979674, baseEnd_979674] using wordTrace_append hprefix tailTrace_979674
  have hstable : (prefixWord ++ tailWord_979674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979674).length < 2 ^ (prefixWord ++ tailWord_979674).sum := by decide
  have hdescent : baseEnd_979674 < baseStart_979674 := by decide
  rcases family_descends (prefixWord ++ tailWord_979674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979724 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_979724 : Nat := 118140960795 + 979724 * 2 ^ 59
def prefixEnd_979724 : Nat := 4983230072969 + 3 ^ 40 * 979724 * 2
def baseEnd_979724 : Nat := 503069320745630059044337

theorem tailTrace_979724 : CollatzResearch.WordTrace tailWord_979724 prefixEnd_979724 503069320745630059044337 := by
  unfold tailWord_979724
  simp only [CollatzResearch.WordTrace]
  refine ⟨17866734951317373191501113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23822313268423164255334817 17866734951317373191501113)
  ·
    refine ⟨13400051213488029893625835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17866734951317373191501113 13400051213488029893625835)
    ·
      refine ⟨20100076820232044840438753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13400051213488029893625835 20100076820232044840438753)
      ·
        refine ⟨15075057615174033630329065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20100076820232044840438753 15075057615174033630329065)
        ·
          refine ⟨11306293211380525222746799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15075057615174033630329065 11306293211380525222746799)
          ·
            refine ⟨16959439817070787834120199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11306293211380525222746799 16959439817070787834120199)
            ·
              refine ⟨25439159725606181751180299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16959439817070787834120199 25439159725606181751180299)
              ·
                refine ⟨38158739588409272626770449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25439159725606181751180299 38158739588409272626770449)
                ·
                  refine ⟨28619054691306954470077837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38158739588409272626770449 28619054691306954470077837)
                  ·
                    refine ⟨10732145509240107926279189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28619054691306954470077837 10732145509240107926279189)
                    ·
                      refine ⟨503069320745630059044337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10732145509240107926279189 503069320745630059044337)
                      ·
                        rfl

theorem cell23_979724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_979724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979724 prefixEnd_979724 := by exact prefixLift 979724
  have htrace : WordTrace (prefixWord ++ tailWord_979724) baseStart_979724 baseEnd_979724 := by
    simpa [prefixWord, tailWord_979724, baseEnd_979724] using wordTrace_append hprefix tailTrace_979724
  have hstable : (prefixWord ++ tailWord_979724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979724).length < 2 ^ (prefixWord ++ tailWord_979724).sum := by decide
  have hdescent : baseEnd_979724 < baseStart_979724 := by decide
  rcases family_descends (prefixWord ++ tailWord_979724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979745 : List Nat := [1, 2, 3, 2, 1, 2, 1, 5, 2, 2, 2]
def baseStart_979745 : Nat := 118140960795 + 979745 * 2 ^ 59
def prefixEnd_979745 : Nat := 4983230072969 + 3 ^ 40 * 979745 * 2
def baseEnd_979745 : Nat := 503080103839374476881741

theorem tailTrace_979745 : CollatzResearch.WordTrace tailWord_979745 prefixEnd_979745 503080103839374476881741 := by
  unfold tailWord_979745
  simp only [CollatzResearch.WordTrace]
  refine ⟨35734235835558666969516689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23822823890372444646344459 35734235835558666969516689)
  ·
    refine ⟨26800676876669000227137517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35734235835558666969516689 26800676876669000227137517)
    ·
      refine ⟨10050253828750875085176569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26800676876669000227137517 10050253828750875085176569)
      ·
        refine ⟨7537690371563156313882427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10050253828750875085176569 7537690371563156313882427)
        ·
          refine ⟨11306535557344734470823641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7537690371563156313882427 11306535557344734470823641)
          ·
            refine ⟨8479901668008550853117731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11306535557344734470823641 8479901668008550853117731)
            ·
              refine ⟨12719852502012826279676597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8479901668008550853117731 12719852502012826279676597)
              ·
                refine ⟨1192486172063702463719681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12719852502012826279676597 1192486172063702463719681)
                ·
                  refine ⟨894364629047776847789761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1192486172063702463719681 894364629047776847789761)
                  ·
                    refine ⟨670773471785832635842321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 894364629047776847789761 670773471785832635842321)
                    ·
                      refine ⟨503080103839374476881741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670773471785832635842321 503080103839374476881741)
                      ·
                        rfl

theorem cell23_979745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_979745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979745 prefixEnd_979745 := by exact prefixLift 979745
  have htrace : WordTrace (prefixWord ++ tailWord_979745) baseStart_979745 baseEnd_979745 := by
    simpa [prefixWord, tailWord_979745, baseEnd_979745] using wordTrace_append hprefix tailTrace_979745
  have hstable : (prefixWord ++ tailWord_979745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979745).length < 2 ^ (prefixWord ++ tailWord_979745).sum := by decide
  have hdescent : baseEnd_979745 < baseStart_979745 := by decide
  rcases family_descends (prefixWord ++ tailWord_979745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979761 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 1, 5, 3]
def baseStart_979761 : Nat := 118140960795 + 979761 * 2 ^ 59
def prefixEnd_979761 : Nat := 4983230072969 + 3 ^ 40 * 979761 * 2
def baseEnd_979761 : Nat := 503088319529846414281667

theorem tailTrace_979761 : CollatzResearch.WordTrace tailWord_979761 prefixEnd_979761 503088319529846414281667 := by
  unfold tailWord_979761
  simp only [CollatzResearch.WordTrace]
  refine ⟨35734819403500701702099137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23823212935667134468066091 35734819403500701702099137)
  ·
    refine ⟨26801114552625526276574353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35734819403500701702099137 26801114552625526276574353)
    ·
      refine ⟨20100835914469144707430765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26801114552625526276574353 20100835914469144707430765)
      ·
        refine ⟨7537813467925929265286537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20100835914469144707430765 7537813467925929265286537)
        ·
          refine ⟨5653360100944446948964903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7537813467925929265286537 5653360100944446948964903)
          ·
            refine ⟨8480040151416670423447355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5653360100944446948964903 8480040151416670423447355)
            ·
              refine ⟨12720060227125005635171033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8480040151416670423447355 12720060227125005635171033)
              ·
                refine ⟨9540045170343754226378275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12720060227125005635171033 9540045170343754226378275)
                ·
                  refine ⟨14310067755515631339567413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9540045170343754226378275 14310067755515631339567413)
                  ·
                    refine ⟨1341568852079590438084445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14310067755515631339567413 1341568852079590438084445)
                    ·
                      refine ⟨503088319529846414281667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1341568852079590438084445 503088319529846414281667)
                      ·
                        rfl

theorem cell23_979761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_979761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979761 prefixEnd_979761 := by exact prefixLift 979761
  have htrace : WordTrace (prefixWord ++ tailWord_979761) baseStart_979761 baseEnd_979761 := by
    simpa [prefixWord, tailWord_979761, baseEnd_979761] using wordTrace_append hprefix tailTrace_979761
  have hstable : (prefixWord ++ tailWord_979761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979761).length < 2 ^ (prefixWord ++ tailWord_979761).sum := by decide
  have hdescent : baseEnd_979761 < baseStart_979761 := by decide
  rcases family_descends (prefixWord ++ tailWord_979761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979766 : List Nat := [5, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_979766 : Nat := 118140960795 + 979766 * 2 ^ 59
def prefixEnd_979766 : Nat := 4983230072969 + 3 ^ 40 * 979766 * 2
def baseEnd_979766 : Nat := 503090886933118894719145

theorem tailTrace_979766 : CollatzResearch.WordTrace tailWord_979766 prefixEnd_979766 503090886933118894719145 := by
  unfold tailWord_979766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2233437610530161722251947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23823334512321725037354101 2233437610530161722251947)
  ·
    refine ⟨3350156415795242583377921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2233437610530161722251947 3350156415795242583377921)
    ·
      refine ⟨2512617311846431937533441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3350156415795242583377921 2512617311846431937533441)
      ·
        refine ⟨1884462983884823953150081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2512617311846431937533441 1884462983884823953150081)
        ·
          refine ⟨1413347237913617964862561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1884462983884823953150081 1413347237913617964862561)
          ·
            refine ⟨1060010428435213473646921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1413347237913617964862561 1060010428435213473646921)
            ·
              refine ⟨795007821326410105235191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060010428435213473646921 795007821326410105235191)
              ·
                refine ⟨1192511731989615157852787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795007821326410105235191 1192511731989615157852787)
                ·
                  refine ⟨1788767597984422736779181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192511731989615157852787 1788767597984422736779181)
                  ·
                    refine ⟨670787849244158526292193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1788767597984422736779181 670787849244158526292193)
                    ·
                      refine ⟨503090886933118894719145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670787849244158526292193 503090886933118894719145)
                      ·
                        rfl

theorem cell23_979766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_979766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979766 prefixEnd_979766 := by exact prefixLift 979766
  have htrace : WordTrace (prefixWord ++ tailWord_979766) baseStart_979766 baseEnd_979766 := by
    simpa [prefixWord, tailWord_979766, baseEnd_979766] using wordTrace_append hprefix tailTrace_979766
  have hstable : (prefixWord ++ tailWord_979766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979766).length < 2 ^ (prefixWord ++ tailWord_979766).sum := by decide
  have hdescent : baseEnd_979766 < baseStart_979766 := by decide
  rcases family_descends (prefixWord ++ tailWord_979766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979768 : List Nat := [2, 1, 2, 1, 3, 2, 4, 3, 5]
def baseStart_979768 : Nat := 118140960795 + 979768 * 2 ^ 59
def prefixEnd_979768 : Nat := 4983230072969 + 3 ^ 40 * 979768 * 2
def baseEnd_979768 : Nat := 55899101543825320766015

theorem tailTrace_979768 : CollatzResearch.WordTrace tailWord_979768 prefixEnd_979768 55899101543825320766015 := by
  unfold tailWord_979768
  simp only [CollatzResearch.WordTrace]
  refine ⟨17867537357237670948801979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23823383142983561265069305 17867537357237670948801979)
  ·
    refine ⟨26801306035856506423202969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17867537357237670948801979 26801306035856506423202969)
    ·
      refine ⟨20100979526892379817402227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26801306035856506423202969 20100979526892379817402227)
      ·
        refine ⟨30151469290338569726103341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20100979526892379817402227 30151469290338569726103341)
        ·
          refine ⟨11306800983876963647288753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30151469290338569726103341 11306800983876963647288753)
          ·
            refine ⟨8480100737907722735466565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11306800983876963647288753 8480100737907722735466565)
            ·
              refine ⟨1590018888357698012899981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8480100737907722735466565 1590018888357698012899981)
              ·
                refine ⟨596257083134136754837493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1590018888357698012899981 596257083134136754837493)
                ·
                  refine ⟨55899101543825320766015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 596257083134136754837493 55899101543825320766015)
                  ·
                    rfl

theorem cell23_979768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 5].length) (baseStart_979768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979768 prefixEnd_979768 := by exact prefixLift 979768
  have htrace : WordTrace (prefixWord ++ tailWord_979768) baseStart_979768 baseEnd_979768 := by
    simpa [prefixWord, tailWord_979768, baseEnd_979768] using wordTrace_append hprefix tailTrace_979768
  have hstable : (prefixWord ++ tailWord_979768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979768).length < 2 ^ (prefixWord ++ tailWord_979768).sum := by decide
  have hdescent : baseEnd_979768 < baseStart_979768 := by decide
  rcases family_descends (prefixWord ++ tailWord_979768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979801 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 1, 3, 4]
def baseStart_979801 : Nat := 118140960795 + 979801 * 2 ^ 59
def prefixEnd_979801 : Nat := 4983230072969 + 3 ^ 40 * 979801 * 2
def baseEnd_979801 : Nat := 503108858756026257781483

theorem tailTrace_979801 : CollatzResearch.WordTrace tailWord_979801 prefixEnd_979801 503108858756026257781483 := by
  unfold tailWord_979801
  simp only [CollatzResearch.WordTrace]
  refine ⟨35736278323355788533555257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23824185548903859022370171 35736278323355788533555257)
  ·
    refine ⟨26802208742516841400166443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35736278323355788533555257 26802208742516841400166443)
    ·
      refine ⟨40203313113775262100249665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26802208742516841400166443 40203313113775262100249665)
      ·
        refine ⟨30152484835331446575187249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40203313113775262100249665 30152484835331446575187249)
        ·
          refine ⟨22614363626498584931390437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30152484835331446575187249 22614363626498584931390437)
          ·
            refine ⟨4240193179968484674635707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22614363626498584931390437 4240193179968484674635707)
            ·
              refine ⟨6360289769952727011953561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240193179968484674635707 6360289769952727011953561)
              ·
                refine ⟨4770217327464545258965171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6360289769952727011953561 4770217327464545258965171)
                ·
                  refine ⟨7155325991196817888447757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770217327464545258965171 7155325991196817888447757)
                  ·
                    refine ⟨2683247246698806708167909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7155325991196817888447757 2683247246698806708167909)
                    ·
                      refine ⟨503108858756026257781483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2683247246698806708167909 503108858756026257781483)
                      ·
                        rfl

theorem cell23_979801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_979801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979801 prefixEnd_979801 := by exact prefixLift 979801
  have htrace : WordTrace (prefixWord ++ tailWord_979801) baseStart_979801 baseEnd_979801 := by
    simpa [prefixWord, tailWord_979801, baseEnd_979801] using wordTrace_append hprefix tailTrace_979801
  have hstable : (prefixWord ++ tailWord_979801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979801).length < 2 ^ (prefixWord ++ tailWord_979801).sum := by decide
  have hdescent : baseEnd_979801 < baseStart_979801 := by decide
  rcases family_descends (prefixWord ++ tailWord_979801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979821 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_979821 : Nat := 118140960795 + 979821 * 2 ^ 59
def prefixEnd_979821 : Nat := 4983230072969 + 3 ^ 40 * 979821 * 2
def baseEnd_979821 : Nat := 503119128369116179531391

theorem tailTrace_979821 : CollatzResearch.WordTrace tailWord_979821 prefixEnd_979821 503119128369116179531391 := by
  unfold tailWord_979821
  simp only [CollatzResearch.WordTrace]
  refine ⟨35737007783283331949283317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23824671855522221299522211 35737007783283331949283317)
  ·
    refine ⟨3350344479682812370245311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35737007783283331949283317 3350344479682812370245311)
    ·
      refine ⟨5025516719524218555367967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3350344479682812370245311 5025516719524218555367967)
      ·
        refine ⟨7538275079286327833051951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5025516719524218555367967 7538275079286327833051951)
        ·
          refine ⟨11307412618929491749577927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7538275079286327833051951 11307412618929491749577927)
          ·
            refine ⟨16961118928394237624366891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11307412618929491749577927 16961118928394237624366891)
            ·
              refine ⟨25441678392591356436550337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16961118928394237624366891 25441678392591356436550337)
              ·
                refine ⟨19081258794443517327412753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25441678392591356436550337 19081258794443517327412753)
                ·
                  refine ⟨14310944095832637995559565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19081258794443517327412753 14310944095832637995559565)
                  ·
                    refine ⟨5366604035937239248334837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14310944095832637995559565 5366604035937239248334837)
                    ·
                      refine ⟨503119128369116179531391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5366604035937239248334837 503119128369116179531391)
                      ·
                        rfl

theorem cell23_979821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_979821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979821 prefixEnd_979821 := by exact prefixLift 979821
  have htrace : WordTrace (prefixWord ++ tailWord_979821) baseStart_979821 baseEnd_979821 := by
    simpa [prefixWord, tailWord_979821, baseEnd_979821] using wordTrace_append hprefix tailTrace_979821
  have hstable : (prefixWord ++ tailWord_979821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979821).length < 2 ^ (prefixWord ++ tailWord_979821).sum := by decide
  have hdescent : baseEnd_979821 < baseStart_979821 := by decide
  rcases family_descends (prefixWord ++ tailWord_979821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979842 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_979842 : Nat := 118140960795 + 979842 * 2 ^ 59
def prefixEnd_979842 : Nat := 4983230072969 + 3 ^ 40 * 979842 * 2
def baseEnd_979842 : Nat := 503129911462860597368795

theorem tailTrace_979842 : CollatzResearch.WordTrace tailWord_979842 prefixEnd_979842 503129911462860597368795 := by
  unfold tailWord_979842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8934443429051813133949445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23825182477471501690531853 8934443429051813133949445)
  ·
    refine ⟨1675208142947214962615521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8934443429051813133949445 1675208142947214962615521)
    ·
      refine ⟨1256406107210411221961641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1675208142947214962615521 1256406107210411221961641)
      ·
        refine ⟨942304580407808416471231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1256406107210411221961641 942304580407808416471231)
        ·
          refine ⟨1413456870611712624706847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942304580407808416471231 1413456870611712624706847)
          ·
            refine ⟨2120185305917568937060271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413456870611712624706847 2120185305917568937060271)
            ·
              refine ⟨3180277958876353405590407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120185305917568937060271 3180277958876353405590407)
              ·
                refine ⟨4770416938314530108385611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180277958876353405590407 4770416938314530108385611)
                ·
                  refine ⟨7155625407471795162578417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770416938314530108385611 7155625407471795162578417)
                  ·
                    refine ⟨5366719055603846371933813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7155625407471795162578417 5366719055603846371933813)
                    ·
                      refine ⟨503129911462860597368795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5366719055603846371933813 503129911462860597368795)
                      ·
                        rfl

theorem cell23_979842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_979842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979842 prefixEnd_979842 := by exact prefixLift 979842
  have htrace : WordTrace (prefixWord ++ tailWord_979842) baseStart_979842 baseEnd_979842 := by
    simpa [prefixWord, tailWord_979842, baseEnd_979842] using wordTrace_append hprefix tailTrace_979842
  have hstable : (prefixWord ++ tailWord_979842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979842).length < 2 ^ (prefixWord ++ tailWord_979842).sum := by decide
  have hdescent : baseEnd_979842 < baseStart_979842 := by decide
  rcases family_descends (prefixWord ++ tailWord_979842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979845 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 3, 4]
def baseStart_979845 : Nat := 118140960795 + 979845 * 2 ^ 59
def prefixEnd_979845 : Nat := 4983230072969 + 3 ^ 40 * 979845 * 2
def baseEnd_979845 : Nat := 167710483968274695210427

theorem tailTrace_979845 : CollatzResearch.WordTrace tailWord_979845 prefixEnd_979845 167710483968274695210427 := by
  unfold tailWord_979845
  simp only [CollatzResearch.WordTrace]
  refine ⟨35737883135196384048156989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23825255423464256032104659 35737883135196384048156989)
  ·
    refine ⟨13401706175698644018058871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35737883135196384048156989 13401706175698644018058871)
    ·
      refine ⟨20102559263547966027088307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13401706175698644018058871 20102559263547966027088307)
      ·
        refine ⟨30153838895321949040632461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20102559263547966027088307 30153838895321949040632461)
        ·
          refine ⟨11307689585745730890237173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30153838895321949040632461 11307689585745730890237173)
          ·
            refine ⟨1060095898663662270959735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11307689585745730890237173 1060095898663662270959735)
            ·
              refine ⟨1590143847995493406439603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060095898663662270959735 1590143847995493406439603)
              ·
                refine ⟨2385215771993240109659405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590143847995493406439603 2385215771993240109659405)
                ·
                  refine ⟨894455914497465041122277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2385215771993240109659405 894455914497465041122277)
                  ·
                    refine ⟨167710483968274695210427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 894455914497465041122277 167710483968274695210427)
                    ·
                      rfl

theorem cell23_979845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_979845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979845 prefixEnd_979845 := by exact prefixLift 979845
  have htrace : WordTrace (prefixWord ++ tailWord_979845) baseStart_979845 baseEnd_979845 := by
    simpa [prefixWord, tailWord_979845, baseEnd_979845] using wordTrace_append hprefix tailTrace_979845
  have hstable : (prefixWord ++ tailWord_979845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979845).length < 2 ^ (prefixWord ++ tailWord_979845).sum := by decide
  have hdescent : baseEnd_979845 < baseStart_979845 := by decide
  rcases family_descends (prefixWord ++ tailWord_979845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979892 : List Nat := [2, 5, 2, 1, 1, 2, 2, 2, 6]
def baseStart_979892 : Nat := 118140960795 + 979892 * 2 ^ 59
def prefixEnd_979892 : Nat := 4983230072969 + 3 ^ 40 * 979892 * 2
def baseEnd_979892 : Nat := 55906176166176155749285

theorem tailTrace_979892 : CollatzResearch.WordTrace tailWord_979892 prefixEnd_979892 55906176166176155749285 := by
  unfold tailWord_979892
  simp only [CollatzResearch.WordTrace]
  refine ⟨17869798683013055537558965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23826398244017407383411953 17869798683013055537558965)
  ·
    refine ⟨1675293626532473956646153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17869798683013055537558965 1675293626532473956646153)
    ·
      refine ⟨1256470219899355467484615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1675293626532473956646153 1256470219899355467484615)
      ·
        refine ⟨1884705329849033201226923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256470219899355467484615 1884705329849033201226923)
        ·
          refine ⟨2827057994773549801840385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884705329849033201226923 2827057994773549801840385)
          ·
            refine ⟨2120293496080162351380289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2827057994773549801840385 2120293496080162351380289)
            ·
              refine ⟨1590220122060121763535217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2120293496080162351380289 1590220122060121763535217)
              ·
                refine ⟨1192665091545091322651413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590220122060121763535217 1192665091545091322651413)
                ·
                  refine ⟨55906176166176155749285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1192665091545091322651413 55906176166176155749285)
                  ·
                    rfl

theorem cell23_979892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_979892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979892 prefixEnd_979892 := by exact prefixLift 979892
  have htrace : WordTrace (prefixWord ++ tailWord_979892) baseStart_979892 baseEnd_979892 := by
    simpa [prefixWord, tailWord_979892, baseEnd_979892] using wordTrace_append hprefix tailTrace_979892
  have hstable : (prefixWord ++ tailWord_979892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979892).length < 2 ^ (prefixWord ++ tailWord_979892).sum := by decide
  have hdescent : baseEnd_979892 < baseStart_979892 := by decide
  rcases family_descends (prefixWord ++ tailWord_979892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979895 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 2, 3, 2]
def baseStart_979895 : Nat := 118140960795 + 979895 * 2 ^ 59
def prefixEnd_979895 : Nat := 4983230072969 + 3 ^ 40 * 979895 * 2
def baseEnd_979895 : Nat := 503157125937548890006051

theorem tailTrace_979895 : CollatzResearch.WordTrace tailWord_979895 prefixEnd_979895 503157125937548890006051 := by
  unfold tailWord_979895
  simp only [CollatzResearch.WordTrace]
  refine ⟨35739706785015242587477139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23826471190010161724984759 35739706785015242587477139)
  ·
    refine ⟨53609560177522863881215709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35739706785015242587477139 53609560177522863881215709)
    ·
      refine ⟨20103585066571073955455891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53609560177522863881215709 20103585066571073955455891)
      ·
        refine ⟨30155377599856610933183837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20103585066571073955455891 30155377599856610933183837)
        ·
          refine ⟨11308266599946229099943939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30155377599856610933183837 11308266599946229099943939)
          ·
            refine ⟨16962399899919343649915909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11308266599946229099943939 16962399899919343649915909)
            ·
              refine ⟨3180449981234876934359233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16962399899919343649915909 3180449981234876934359233)
              ·
                refine ⟨2385337485926157700769425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3180449981234876934359233 2385337485926157700769425)
                ·
                  refine ⟨1789003114444618275577069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2385337485926157700769425 1789003114444618275577069)
                  ·
                    refine ⟨670876167916731853341401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1789003114444618275577069 670876167916731853341401)
                    ·
                      refine ⟨503157125937548890006051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670876167916731853341401 503157125937548890006051)
                      ·
                        rfl

theorem cell23_979895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 3, 2].length) (baseStart_979895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979895 prefixEnd_979895 := by exact prefixLift 979895
  have htrace : WordTrace (prefixWord ++ tailWord_979895) baseStart_979895 baseEnd_979895 := by
    simpa [prefixWord, tailWord_979895, baseEnd_979895] using wordTrace_append hprefix tailTrace_979895
  have hstable : (prefixWord ++ tailWord_979895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979895).length < 2 ^ (prefixWord ++ tailWord_979895).sum := by decide
  have hdescent : baseEnd_979895 < baseStart_979895 := by decide
  rcases family_descends (prefixWord ++ tailWord_979895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979918 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_979918 : Nat := 118140960795 + 979918 * 2 ^ 59
def prefixEnd_979918 : Nat := 4983230072969 + 3 ^ 40 * 979918 * 2
def baseEnd_979918 : Nat := 167722978664200766672815

theorem tailTrace_979918 : CollatzResearch.WordTrace tailWord_979918 prefixEnd_979918 167722978664200766672815 := by
  unfold tailWord_979918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4467568207991489689445551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23827030442621278343709605 4467568207991489689445551)
  ·
    refine ⟨6701352311987234534168327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4467568207991489689445551 6701352311987234534168327)
    ·
      refine ⟨10052028467980851801252491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6701352311987234534168327 10052028467980851801252491)
      ·
        refine ⟨15078042701971277701878737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10052028467980851801252491 15078042701971277701878737)
        ·
          refine ⟨11308532026478458276409053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15078042701971277701878737 11308532026478458276409053)
          ·
            refine ⟨4240699509929421853653395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11308532026478458276409053 4240699509929421853653395)
            ·
              refine ⟨6361049264894132780480093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240699509929421853653395 6361049264894132780480093)
              ·
                refine ⟨2385393474335299792680035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6361049264894132780480093 2385393474335299792680035)
                ·
                  refine ⟨3578090211502949689020053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385393474335299792680035 3578090211502949689020053)
                  ·
                    refine ⟨167722978664200766672815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3578090211502949689020053 167722978664200766672815)
                    ·
                      rfl

theorem cell23_979918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_979918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979918 prefixEnd_979918 := by exact prefixLift 979918
  have htrace : WordTrace (prefixWord ++ tailWord_979918) baseStart_979918 baseEnd_979918 := by
    simpa [prefixWord, tailWord_979918, baseEnd_979918] using wordTrace_append hprefix tailTrace_979918
  have hstable : (prefixWord ++ tailWord_979918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979918).length < 2 ^ (prefixWord ++ tailWord_979918).sum := by decide
  have hdescent : baseEnd_979918 < baseStart_979918 := by decide
  rcases family_descends (prefixWord ++ tailWord_979918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979985 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 3, 3, 2]
def baseStart_979985 : Nat := 118140960795 + 979985 * 2 ^ 59
def prefixEnd_979985 : Nat := 4983230072969 + 3 ^ 40 * 979985 * 2
def baseEnd_979985 : Nat := 503203339196453537880637

theorem tailTrace_979985 : CollatzResearch.WordTrace tailWord_979985 prefixEnd_979985 503203339196453537880637 := by
  unfold tailWord_979985
  simp only [CollatzResearch.WordTrace]
  refine ⟨35742989354689187958253409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23828659569792791972168939 35742989354689187958253409)
  ·
    refine ⟨26807242016016890968690057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35742989354689187958253409 26807242016016890968690057)
    ·
      refine ⟨20105431512012668226517543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26807242016016890968690057 20105431512012668226517543)
      ·
        refine ⟨30158147268019002339776315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20105431512012668226517543 30158147268019002339776315)
        ·
          refine ⟨45237220902028503509664473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30158147268019002339776315 45237220902028503509664473)
          ·
            refine ⟨33927915676521377632248355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45237220902028503509664473 33927915676521377632248355)
            ·
              refine ⟨50891873514782066448372533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33927915676521377632248355 50891873514782066448372533)
              ·
                refine ⟨4771113142010818729534925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50891873514782066448372533 4771113142010818729534925)
                ·
                  refine ⟨1789167428254057023575597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4771113142010818729534925 1789167428254057023575597)
                  ·
                    refine ⟨670937785595271383840849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1789167428254057023575597 670937785595271383840849)
                    ·
                      refine ⟨503203339196453537880637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670937785595271383840849 503203339196453537880637)
                      ·
                        rfl

theorem cell23_979985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 3, 2].length) (baseStart_979985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_979985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_979985 prefixEnd_979985 := by exact prefixLift 979985
  have htrace : WordTrace (prefixWord ++ tailWord_979985) baseStart_979985 baseEnd_979985 := by
    simpa [prefixWord, tailWord_979985, baseEnd_979985] using wordTrace_append hprefix tailTrace_979985
  have hstable : (prefixWord ++ tailWord_979985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979985).length < 2 ^ (prefixWord ++ tailWord_979985).sum := by decide
  have hdescent : baseEnd_979985 < baseStart_979985 := by decide
  rcases family_descends (prefixWord ++ tailWord_979985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980018 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_980018 : Nat := 118140960795 + 980018 * 2 ^ 59
def prefixEnd_980018 : Nat := 4983230072969 + 3 ^ 40 * 980018 * 2
def baseEnd_980018 : Nat := 503220284058051908767985

theorem tailTrace_980018 : CollatzResearch.WordTrace tailWord_980018 prefixEnd_980018 503220284058051908767985 := by
  unfold tailWord_980018
  simp only [CollatzResearch.WordTrace]
  refine ⟨8936048240892408648551177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23829461975713089729469805 8936048240892408648551177)
  ·
    refine ⟨6702036180669306486413383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8936048240892408648551177 6702036180669306486413383)
    ·
      refine ⟨10053054271003959729620075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6702036180669306486413383 10053054271003959729620075)
      ·
        refine ⟨15079581406505939594430113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10053054271003959729620075 15079581406505939594430113)
        ·
          refine ⟨11309686054879454695822585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15079581406505939594430113 11309686054879454695822585)
          ·
            refine ⟨8482264541159591021866939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11309686054879454695822585 8482264541159591021866939)
            ·
              refine ⟨12723396811739386532800409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8482264541159591021866939 12723396811739386532800409)
              ·
                refine ⟨9542547608804539899600307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12723396811739386532800409 9542547608804539899600307)
                ·
                  refine ⟨14313821413206809849400461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9542547608804539899600307 14313821413206809849400461)
                  ·
                    refine ⟨5367683029952553693525173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14313821413206809849400461 5367683029952553693525173)
                    ·
                      refine ⟨503220284058051908767985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5367683029952553693525173 503220284058051908767985)
                      ·
                        rfl

theorem cell23_980018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_980018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980018 prefixEnd_980018 := by exact prefixLift 980018
  have htrace : WordTrace (prefixWord ++ tailWord_980018) baseStart_980018 baseEnd_980018 := by
    simpa [prefixWord, tailWord_980018, baseEnd_980018] using wordTrace_append hprefix tailTrace_980018
  have hstable : (prefixWord ++ tailWord_980018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980018).length < 2 ^ (prefixWord ++ tailWord_980018).sum := by decide
  have hdescent : baseEnd_980018 < baseStart_980018 := by decide
  rcases family_descends (prefixWord ++ tailWord_980018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980055 : List Nat := [1, 1, 3, 2, 2, 1, 1, 7, 5]
def baseStart_980055 : Nat := 118140960795 + 980055 * 2 ^ 59
def prefixEnd_980055 : Nat := 4983230072969 + 3 ^ 40 * 980055 * 2
def baseEnd_980055 : Nat := 55915475871363140445035

theorem tailTrace_980055 : CollatzResearch.WordTrace tailWord_980055 prefixEnd_980055 55915475871363140445035 := by
  unfold tailWord_980055
  simp only [CollatzResearch.WordTrace]
  refine ⟨35745542464435589913301619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23830361642957059942201079 35745542464435589913301619)
  ·
    refine ⟨53618313696653384869952429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35745542464435589913301619 53618313696653384869952429)
    ·
      refine ⟨20106867636245019326232161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53618313696653384869952429 20106867636245019326232161)
      ·
        refine ⟨15080150727183764494674121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20106867636245019326232161 15080150727183764494674121)
        ·
          refine ⟨11310113045387823371005591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15080150727183764494674121 11310113045387823371005591)
          ·
            refine ⟨16965169568081735056508387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11310113045387823371005591 16965169568081735056508387)
            ·
              refine ⟨25447754352122602584762581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16965169568081735056508387 25447754352122602584762581)
              ·
                refine ⟨596431742627873498080373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25447754352122602584762581 596431742627873498080373)
                ·
                  refine ⟨55915475871363140445035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 596431742627873498080373 55915475871363140445035)
                  ·
                    rfl

theorem cell23_980055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 5].length) (baseStart_980055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980055 prefixEnd_980055 := by exact prefixLift 980055
  have htrace : WordTrace (prefixWord ++ tailWord_980055) baseStart_980055 baseEnd_980055 := by
    simpa [prefixWord, tailWord_980055, baseEnd_980055] using wordTrace_append hprefix tailTrace_980055
  have hstable : (prefixWord ++ tailWord_980055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980055).length < 2 ^ (prefixWord ++ tailWord_980055).sum := by decide
  have hdescent : baseEnd_980055 < baseStart_980055 := by decide
  rcases family_descends (prefixWord ++ tailWord_980055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980066 : List Nat := [3, 3, 2, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_980066 : Nat := 118140960795 + 980066 * 2 ^ 59
def prefixEnd_980066 : Nat := 4983230072969 + 3 ^ 40 * 980066 * 2
def baseEnd_980066 : Nat := 503244931129467720967765

theorem tailTrace_980066 : CollatzResearch.WordTrace tailWord_980066 prefixEnd_980066 503244931129467720967765 := by
  unfold tailWord_980066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8936485916848934697988013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23830629111597159194634701 8936485916848934697988013)
  ·
    refine ⟨3351182218818350511745505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8936485916848934697988013 3351182218818350511745505)
    ·
      refine ⟨2513386664113762883809129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3351182218818350511745505 2513386664113762883809129)
      ·
        refine ⟨1885039998085322162856847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2513386664113762883809129 1885039998085322162856847)
        ·
          refine ⟨2827559997127983244285271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885039998085322162856847 2827559997127983244285271)
          ·
            refine ⟨4241339995691974866427907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827559997127983244285271 4241339995691974866427907)
            ·
              refine ⟨6362009993537962299641861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241339995691974866427907 6362009993537962299641861)
              ·
                refine ⟨1192876873788367931182849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6362009993537962299641861 1192876873788367931182849)
                ·
                  refine ⟨894657655341275948387137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1192876873788367931182849 894657655341275948387137)
                  ·
                    refine ⟨670993241505956961290353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 894657655341275948387137 670993241505956961290353)
                    ·
                      refine ⟨503244931129467720967765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 670993241505956961290353 503244931129467720967765)
                      ·
                        rfl

theorem cell23_980066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_980066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980066 prefixEnd_980066 := by exact prefixLift 980066
  have htrace : WordTrace (prefixWord ++ tailWord_980066) baseStart_980066 baseEnd_980066 := by
    simpa [prefixWord, tailWord_980066, baseEnd_980066] using wordTrace_append hprefix tailTrace_980066
  have hstable : (prefixWord ++ tailWord_980066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980066).length < 2 ^ (prefixWord ++ tailWord_980066).sum := by decide
  have hdescent : baseEnd_980066 < baseStart_980066 := by decide
  rcases family_descends (prefixWord ++ tailWord_980066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980068 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_980068 : Nat := 118140960795 + 980068 * 2 ^ 59
def prefixEnd_980068 : Nat := 4983230072969 + 3 ^ 40 * 980068 * 2
def baseEnd_980068 : Nat := 167748652696925571047585

theorem tailTrace_980068 : CollatzResearch.WordTrace tailWord_980068 prefixEnd_980068 167748652696925571047585 := by
  unfold tailWord_980068
  simp only [CollatzResearch.WordTrace]
  refine ⟨17873008306694246566762429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23830677742258995422349905 17873008306694246566762429)
  ·
    refine ⟨6702378115010342462535911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17873008306694246566762429 6702378115010342462535911)
    ·
      refine ⟨10053567172515513693803867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6702378115010342462535911 10053567172515513693803867)
      ·
        refine ⟨15080350758773270540705801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10053567172515513693803867 15080350758773270540705801)
        ·
          refine ⟨11310263069079952905529351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15080350758773270540705801 11310263069079952905529351)
          ·
            refine ⟨16965394603619929358294027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11310263069079952905529351 16965394603619929358294027)
            ·
              refine ⟨25448091905429894037441041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16965394603619929358294027 25448091905429894037441041)
              ·
                refine ⟨19086068929072420528080781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25448091905429894037441041 19086068929072420528080781)
                ·
                  refine ⟨7157275848402157698030293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19086068929072420528080781 7157275848402157698030293)
                  ·
                    refine ⟨167748652696925571047585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7157275848402157698030293 167748652696925571047585)
                    ·
                      rfl

theorem cell23_980068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_980068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980068 prefixEnd_980068 := by exact prefixLift 980068
  have htrace : WordTrace (prefixWord ++ tailWord_980068) baseStart_980068 baseEnd_980068 := by
    simpa [prefixWord, tailWord_980068, baseEnd_980068] using wordTrace_append hprefix tailTrace_980068
  have hstable : (prefixWord ++ tailWord_980068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980068).length < 2 ^ (prefixWord ++ tailWord_980068).sum := by decide
  have hdescent : baseEnd_980068 < baseStart_980068 := by decide
  rcases family_descends (prefixWord ++ tailWord_980068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980105 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 1, 3, 4]
def baseStart_980105 : Nat := 118140960795 + 980105 * 2 ^ 59
def prefixEnd_980105 : Nat := 4983230072969 + 3 ^ 40 * 980105 * 2
def baseEnd_980105 : Nat := 503264956874993068380085

theorem tailTrace_980105 : CollatzResearch.WordTrace tailWord_980105 prefixEnd_980105 503264956874993068380085 := by
  unfold tailWord_980105
  simp only [CollatzResearch.WordTrace]
  refine ⟨35747366114254448452621769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23831577409502965635081179 35747366114254448452621769)
  ·
    refine ⟨26810524585690836339466327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35747366114254448452621769 26810524585690836339466327)
    ·
      refine ⟨40215786878536254509199491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26810524585690836339466327 40215786878536254509199491)
      ·
        refine ⟨60323680317804381763799237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40215786878536254509199491 60323680317804381763799237)
        ·
          refine ⟨11310690059588321580712357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60323680317804381763799237 11310690059588321580712357)
          ·
            refine ⟨2120754386172810296383567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11310690059588321580712357 2120754386172810296383567)
            ·
              refine ⟨3181131579259215444575351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120754386172810296383567 3181131579259215444575351)
              ·
                refine ⟨4771697368888823166863027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3181131579259215444575351 4771697368888823166863027)
                ·
                  refine ⟨7157546053333234750294541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4771697368888823166863027 7157546053333234750294541)
                  ·
                    refine ⟨2684079769999963031360453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7157546053333234750294541 2684079769999963031360453)
                    ·
                      refine ⟨503264956874993068380085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2684079769999963031360453 503264956874993068380085)
                      ·
                        rfl

theorem cell23_980105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_980105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980105 prefixEnd_980105 := by exact prefixLift 980105
  have htrace : WordTrace (prefixWord ++ tailWord_980105) baseStart_980105 baseEnd_980105 := by
    simpa [prefixWord, tailWord_980105, baseEnd_980105] using wordTrace_append hprefix tailTrace_980105
  have hstable : (prefixWord ++ tailWord_980105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980105).length < 2 ^ (prefixWord ++ tailWord_980105).sum := by decide
  have hdescent : baseEnd_980105 < baseStart_980105 := by decide
  rcases family_descends (prefixWord ++ tailWord_980105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980132 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_980132 : Nat := 118140960795 + 980132 * 2 ^ 59
def prefixEnd_980132 : Nat := 4983230072969 + 3 ^ 40 * 980132 * 2
def baseEnd_980132 : Nat := 167759606950888154247487

theorem tailTrace_980132 : CollatzResearch.WordTrace tailWord_980132 prefixEnd_980132 167759606950888154247487 := by
  unfold tailWord_980132
  simp only [CollatzResearch.WordTrace]
  refine ⟨17874175442578316031927325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23832233923437754709236433 17874175442578316031927325)
  ·
    refine ⟨6702815790966868511972747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17874175442578316031927325 6702815790966868511972747)
    ·
      refine ⟨10054223686450302767959121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6702815790966868511972747 10054223686450302767959121)
      ·
        refine ⟨7540667764837727075969341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10054223686450302767959121 7540667764837727075969341)
        ·
          refine ⟨2827750411814147653488503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7540667764837727075969341 2827750411814147653488503)
          ·
            refine ⟨4241625617721221480232755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827750411814147653488503 4241625617721221480232755)
            ·
              refine ⟨6362438426581832220349133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241625617721221480232755 6362438426581832220349133)
              ·
                refine ⟨2385914409968187082630925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6362438426581832220349133 2385914409968187082630925)
                ·
                  refine ⟨894717903738070155986597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2385914409968187082630925 894717903738070155986597)
                  ·
                    refine ⟨167759606950888154247487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 894717903738070155986597 167759606950888154247487)
                    ·
                      rfl

theorem cell23_980132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_980132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980132 prefixEnd_980132 := by exact prefixLift 980132
  have htrace : WordTrace (prefixWord ++ tailWord_980132) baseStart_980132 baseEnd_980132 := by
    simpa [prefixWord, tailWord_980132, baseEnd_980132] using wordTrace_append hprefix tailTrace_980132
  have hstable : (prefixWord ++ tailWord_980132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980132).length < 2 ^ (prefixWord ++ tailWord_980132).sum := by decide
  have hdescent : baseEnd_980132 < baseStart_980132 := by decide
  rcases family_descends (prefixWord ++ tailWord_980132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980215 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 3]
def baseStart_980215 : Nat := 118140960795 + 980215 * 2 ^ 59
def prefixEnd_980215 : Nat := 4983230072969 + 3 ^ 40 * 980215 * 2
def baseEnd_980215 : Nat := 503321439746987638004579

theorem tailTrace_980215 : CollatzResearch.WordTrace tailWord_980215 prefixEnd_980215 503321439746987638004579 := by
  unfold tailWord_980215
  simp only [CollatzResearch.WordTrace]
  refine ⟨35751378143855937239126099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23834252095903958159417399 35751378143855937239126099)
  ·
    refine ⟨53627067215783905858689149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35751378143855937239126099 53627067215783905858689149)
    ·
      refine ⟨20110150205918964697008431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53627067215783905858689149 20110150205918964697008431)
      ·
        refine ⟨30165225308878447045512647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20110150205918964697008431 30165225308878447045512647)
        ·
          refine ⟨45247837963317670568268971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30165225308878447045512647 45247837963317670568268971)
          ·
            refine ⟨67871756944976505852403457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45247837963317670568268971 67871756944976505852403457)
            ·
              refine ⟨50903817708732379389302593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67871756944976505852403457 50903817708732379389302593)
              ·
                refine ⟨38177863281549284541976945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50903817708732379389302593 38177863281549284541976945)
                ·
                  refine ⟨28633397461161963406482709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38177863281549284541976945 28633397461161963406482709)
                  ·
                    refine ⟨1342190505991967034678877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28633397461161963406482709 1342190505991967034678877)
                    ·
                      refine ⟨503321439746987638004579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1342190505991967034678877 503321439746987638004579)
                      ·
                        rfl

theorem cell23_980215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_980215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980215 prefixEnd_980215 := by exact prefixLift 980215
  have htrace : WordTrace (prefixWord ++ tailWord_980215) baseStart_980215 baseEnd_980215 := by
    simpa [prefixWord, tailWord_980215, baseEnd_980215] using wordTrace_append hprefix tailTrace_980215
  have hstable : (prefixWord ++ tailWord_980215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980215).length < 2 ^ (prefixWord ++ tailWord_980215).sum := by decide
  have hdescent : baseEnd_980215 < baseStart_980215 := by decide
  rcases family_descends (prefixWord ++ tailWord_980215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980222 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_980222 : Nat := 118140960795 + 980222 * 2 ^ 59
def prefixEnd_980222 : Nat := 4983230072969 + 3 ^ 40 * 980222 * 2
def baseEnd_980222 : Nat := 167775011370523036872349

theorem tailTrace_980222 : CollatzResearch.WordTrace tailWord_980222 prefixEnd_980222 167775011370523036872349 := by
  unfold tailWord_980222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4468954181853822179328865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23834422303220384956420613 4468954181853822179328865)
  ·
    refine ⟨3351715636390366634496649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4468954181853822179328865 3351715636390366634496649)
    ·
      refine ⟨2513786727292774975872487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3351715636390366634496649 2513786727292774975872487)
      ·
        refine ⟨3770680090939162463808731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2513786727292774975872487 3770680090939162463808731)
        ·
          refine ⟨5656020136408743695713097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3770680090939162463808731 5656020136408743695713097)
          ·
            refine ⟨4242015102306557771784823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5656020136408743695713097 4242015102306557771784823)
            ·
              refine ⟨6363022653459836657677235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4242015102306557771784823 6363022653459836657677235)
              ·
                refine ⟨9544533980189754986515853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6363022653459836657677235 9544533980189754986515853)
                ·
                  refine ⟨3579200242571158119943445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9544533980189754986515853 3579200242571158119943445)
                  ·
                    refine ⟨167775011370523036872349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3579200242571158119943445 167775011370523036872349)
                    ·
                      rfl

theorem cell23_980222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_980222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980222 prefixEnd_980222 := by exact prefixLift 980222
  have htrace : WordTrace (prefixWord ++ tailWord_980222) baseStart_980222 baseEnd_980222 := by
    simpa [prefixWord, tailWord_980222, baseEnd_980222] using wordTrace_append hprefix tailTrace_980222
  have hstable : (prefixWord ++ tailWord_980222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980222).length < 2 ^ (prefixWord ++ tailWord_980222).sum := by decide
  have hdescent : baseEnd_980222 < baseStart_980222 := by decide
  rcases family_descends (prefixWord ++ tailWord_980222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980229 : List Nat := [1, 3, 1, 1, 2, 1, 7, 1, 1, 1, 4]
def baseStart_980229 : Nat := 118140960795 + 980229 * 2 ^ 59
def prefixEnd_980229 : Nat := 4983230072969 + 3 ^ 40 * 980229 * 2
def baseEnd_980229 : Nat := 503328628476150583229515

theorem tailTrace_980229 : CollatzResearch.WordTrace tailWord_980229 prefixEnd_980229 503328628476150583229515 := by
  unfold tailWord_980229
  simp only [CollatzResearch.WordTrace]
  refine ⟨35751888765805217630135741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23834592510536811753423827 35751888765805217630135741)
  ·
    refine ⟨13406958287176956611300903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35751888765805217630135741 13406958287176956611300903)
    ·
      refine ⟨20110437430765434916951355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13406958287176956611300903 20110437430765434916951355)
      ·
        refine ⟨30165656146148152375427033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20110437430765434916951355 30165656146148152375427033)
        ·
          refine ⟨22624242109611114281570275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30165656146148152375427033 22624242109611114281570275)
          ·
            refine ⟨33936363164416671422355413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22624242109611114281570275 33936363164416671422355413)
            ·
              refine ⟨795383511666015736461455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 33936363164416671422355413 795383511666015736461455)
              ·
                refine ⟨1193075267499023604692183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795383511666015736461455 1193075267499023604692183)
                ·
                  refine ⟨1789612901248535407038275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193075267499023604692183 1789612901248535407038275)
                  ·
                    refine ⟨2684419351872803110557413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1789612901248535407038275 2684419351872803110557413)
                    ·
                      refine ⟨503328628476150583229515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2684419351872803110557413 503328628476150583229515)
                      ·
                        rfl

theorem cell23_980229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 1, 1, 4].length) (baseStart_980229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980229 prefixEnd_980229 := by exact prefixLift 980229
  have htrace : WordTrace (prefixWord ++ tailWord_980229) baseStart_980229 baseEnd_980229 := by
    simpa [prefixWord, tailWord_980229, baseEnd_980229] using wordTrace_append hprefix tailTrace_980229
  have hstable : (prefixWord ++ tailWord_980229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980229).length < 2 ^ (prefixWord ++ tailWord_980229).sum := by decide
  have hdescent : baseEnd_980229 < baseStart_980229 := by decide
  rcases family_descends (prefixWord ++ tailWord_980229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980352 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 3]
def baseStart_980352 : Nat := 118140960795 + 980352 * 2 ^ 59
def prefixEnd_980352 : Nat := 4983230072969 + 3 ^ 40 * 980352 * 2
def baseEnd_980352 : Nat := 503391786596653601991449

theorem tailTrace_980352 : CollatzResearch.WordTrace tailWord_980352 prefixEnd_980352 503391786596653601991449 := by
  unfold tailWord_980352
  simp only [CollatzResearch.WordTrace]
  refine ⟨17878187472179804818431655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23837583296239739757908873 17878187472179804818431655)
  ·
    refine ⟨26817281208269707227647483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17878187472179804818431655 26817281208269707227647483)
    ·
      refine ⟨40225921812404560841471225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26817281208269707227647483 40225921812404560841471225)
      ·
        refine ⟨30169441359303420631103419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40225921812404560841471225 30169441359303420631103419)
        ·
          refine ⟨45254162038955130946655129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30169441359303420631103419 45254162038955130946655129)
          ·
            refine ⟨33940621529216348209991347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45254162038955130946655129 33940621529216348209991347)
            ·
              refine ⟨50910932293824522314987021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33940621529216348209991347 50910932293824522314987021)
              ·
                refine ⟨19091599610184195868120133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50910932293824522314987021 19091599610184195868120133)
                ·
                  refine ⟨3579674926909536725272525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19091599610184195868120133 3579674926909536725272525)
                  ·
                    refine ⟨1342378097591076271977197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3579674926909536725272525 1342378097591076271977197)
                    ·
                      refine ⟨503391786596653601991449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1342378097591076271977197 503391786596653601991449)
                      ·
                        rfl

theorem cell23_980352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_980352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980352 prefixEnd_980352 := by exact prefixLift 980352
  have htrace : WordTrace (prefixWord ++ tailWord_980352) baseStart_980352 baseEnd_980352 := by
    simpa [prefixWord, tailWord_980352, baseEnd_980352] using wordTrace_append hprefix tailTrace_980352
  have hstable : (prefixWord ++ tailWord_980352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980352).length < 2 ^ (prefixWord ++ tailWord_980352).sum := by decide
  have hdescent : baseEnd_980352 < baseStart_980352 := by decide
  rcases family_descends (prefixWord ++ tailWord_980352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980359 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 7]
def baseStart_980359 : Nat := 118140960795 + 980359 * 2 ^ 59
def prefixEnd_980359 : Nat := 4983230072969 + 3 ^ 40 * 980359 * 2
def baseEnd_980359 : Nat := 55932820106803897178213

theorem tailTrace_980359 : CollatzResearch.WordTrace tailWord_980359 prefixEnd_980359 55932820106803897178213 := by
  unfold tailWord_980359
  simp only [CollatzResearch.WordTrace]
  refine ⟨35756630255334249832368131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23837753503556166554912087 35756630255334249832368131)
  ·
    refine ⟨53634945383001374748552197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35756630255334249832368131 53634945383001374748552197)
    ·
      refine ⟨10056552259312757765353537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53634945383001374748552197 10056552259312757765353537)
      ·
        refine ⟨7542414194484568324015153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10056552259312757765353537 7542414194484568324015153)
        ·
          refine ⟨5656810645863426243011365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7542414194484568324015153 5656810645863426243011365)
          ·
            refine ⟨1060651996099392420564631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5656810645863426243011365 1060651996099392420564631)
            ·
              refine ⟨1590977994149088630846947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060651996099392420564631 1590977994149088630846947)
              ·
                refine ⟨2386466991223632946270421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590977994149088630846947 2386466991223632946270421)
                ·
                  refine ⟨55932820106803897178213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2386466991223632946270421 55932820106803897178213)
                  ·
                    rfl

theorem cell23_980359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 7].length) (baseStart_980359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980359 prefixEnd_980359 := by exact prefixLift 980359
  have htrace : WordTrace (prefixWord ++ tailWord_980359) baseStart_980359 baseEnd_980359 := by
    simpa [prefixWord, tailWord_980359, baseEnd_980359] using wordTrace_append hprefix tailTrace_980359
  have hstable : (prefixWord ++ tailWord_980359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980359).length < 2 ^ (prefixWord ++ tailWord_980359).sum := by decide
  have hdescent : baseEnd_980359 < baseStart_980359 := by decide
  rcases family_descends (prefixWord ++ tailWord_980359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980426 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 2, 4, 2]
def baseStart_980426 : Nat := 118140960795 + 980426 * 2 ^ 59
def prefixEnd_980426 : Nat := 4983230072969 + 3 ^ 40 * 980426 * 2
def baseEnd_980426 : Nat := 503429784165086312466109

theorem tailTrace_980426 : CollatzResearch.WordTrace tailWord_980426 prefixEnd_980426 503429784165086312466109 := by
  unfold tailWord_980426
  simp only [CollatzResearch.WordTrace]
  refine ⟨8939768486522880068764283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23839382630727680183371421 8939768486522880068764283)
  ·
    refine ⟨13409652729784320103146425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8939768486522880068764283 13409652729784320103146425)
    ·
      refine ⟨10057239547338240077359819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13409652729784320103146425 10057239547338240077359819)
      ·
        refine ⟨15085859321007360116039729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10057239547338240077359819 15085859321007360116039729)
        ·
          refine ⟨11314394490755520087029797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15085859321007360116039729 11314394490755520087029797)
          ·
            refine ⟨2121448967016660016318087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11314394490755520087029797 2121448967016660016318087)
            ·
              refine ⟨3182173450524990024477131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121448967016660016318087 3182173450524990024477131)
              ·
                refine ⟨4773260175787485036715697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3182173450524990024477131 4773260175787485036715697)
                ·
                  refine ⟨3579945131840613777536773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4773260175787485036715697 3579945131840613777536773)
                  ·
                    refine ⟨671239712220115083288145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3579945131840613777536773 671239712220115083288145)
                    ·
                      refine ⟨503429784165086312466109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 671239712220115083288145 503429784165086312466109)
                      ·
                        rfl

theorem cell23_980426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_980426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980426 prefixEnd_980426 := by exact prefixLift 980426
  have htrace : WordTrace (prefixWord ++ tailWord_980426) baseStart_980426 baseEnd_980426 := by
    simpa [prefixWord, tailWord_980426, baseEnd_980426] using wordTrace_append hprefix tailTrace_980426
  have hstable : (prefixWord ++ tailWord_980426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980426).length < 2 ^ (prefixWord ++ tailWord_980426).sum := by decide
  have hdescent : baseEnd_980426 < baseStart_980426 := by decide
  rcases family_descends (prefixWord ++ tailWord_980426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980452 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_980452 : Nat := 118140960795 + 980452 * 2 ^ 59
def prefixEnd_980452 : Nat := 4983230072969 + 3 ^ 40 * 980452 * 2
def baseEnd_980452 : Nat := 503443134662103210740989

theorem tailTrace_980452 : CollatzResearch.WordTrace tailWord_980452 prefixEnd_980452 503443134662103210740989 := by
  unfold tailWord_980452
  simp only [CollatzResearch.WordTrace]
  refine ⟨17880011121998663357751805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23840014829331551143669073 17880011121998663357751805)
  ·
    refine ⟨6705004170749498759156927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17880011121998663357751805 6705004170749498759156927)
    ·
      refine ⟨10057506256124248138735391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6705004170749498759156927 10057506256124248138735391)
      ·
        refine ⟨15086259384186372208103087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10057506256124248138735391 15086259384186372208103087)
        ·
          refine ⟨22629389076279558312154631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15086259384186372208103087 22629389076279558312154631)
          ·
            refine ⟨33944083614419337468231947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22629389076279558312154631 33944083614419337468231947)
            ·
              refine ⟨50916125421629006202347921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33944083614419337468231947 50916125421629006202347921)
              ·
                refine ⟨38187094066221754651760941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50916125421629006202347921 38187094066221754651760941)
                ·
                  refine ⟨14320160274833157994410353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38187094066221754651760941 14320160274833157994410353)
                  ·
                    refine ⟨10740120206124868495807765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14320160274833157994410353 10740120206124868495807765)
                    ·
                      refine ⟨503443134662103210740989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10740120206124868495807765 503443134662103210740989)
                      ·
                        rfl

theorem cell23_980452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_980452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980452 prefixEnd_980452 := by exact prefixLift 980452
  have htrace : WordTrace (prefixWord ++ tailWord_980452) baseStart_980452 baseEnd_980452 := by
    simpa [prefixWord, tailWord_980452, baseEnd_980452] using wordTrace_append hprefix tailTrace_980452
  have hstable : (prefixWord ++ tailWord_980452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980452).length < 2 ^ (prefixWord ++ tailWord_980452).sum := by decide
  have hdescent : baseEnd_980452 < baseStart_980452 := by decide
  rcases family_descends (prefixWord ++ tailWord_980452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980453 : List Nat := [1, 3, 1, 5, 1, 1, 1, 5, 1, 4]
def baseStart_980453 : Nat := 118140960795 + 980453 * 2 ^ 59
def prefixEnd_980453 : Nat := 4983230072969 + 3 ^ 40 * 980453 * 2
def baseEnd_980453 : Nat := 167814549380919235609495

theorem tailTrace_980453 : CollatzResearch.WordTrace tailWord_980453 prefixEnd_980453 167814549380919235609495 := by
  unfold tailWord_980453
  simp only [CollatzResearch.WordTrace]
  refine ⟨35760058716993703886290013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23840039144662469257526675 35760058716993703886290013)
  ·
    refine ⟨13410022018872638957358755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35760058716993703886290013 13410022018872638957358755)
    ·
      refine ⟨20115033028308958436038133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13410022018872638957358755 20115033028308958436038133)
      ·
        refine ⟨1885784346403964853378575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20115033028308958436038133 1885784346403964853378575)
        ·
          refine ⟨2828676519605947280067863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885784346403964853378575 2828676519605947280067863)
          ·
            refine ⟨4243014779408920920101795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828676519605947280067863 4243014779408920920101795)
            ·
              refine ⟨6364522169113381380152693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4243014779408920920101795 6364522169113381380152693)
              ·
                refine ⟨596673953354379504389315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6364522169113381380152693 596673953354379504389315)
                ·
                  refine ⟨895010930031569256583973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596673953354379504389315 895010930031569256583973)
                  ·
                    refine ⟨167814549380919235609495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 895010930031569256583973 167814549380919235609495)
                    ·
                      rfl

theorem cell23_980453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_980453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980453 prefixEnd_980453 := by exact prefixLift 980453
  have htrace : WordTrace (prefixWord ++ tailWord_980453) baseStart_980453 baseEnd_980453 := by
    simpa [prefixWord, tailWord_980453, baseEnd_980453] using wordTrace_append hprefix tailTrace_980453
  have hstable : (prefixWord ++ tailWord_980453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980453).length < 2 ^ (prefixWord ++ tailWord_980453).sum := by decide
  have hdescent : baseEnd_980453 < baseStart_980453 := by decide
  rcases family_descends (prefixWord ++ tailWord_980453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980466 : List Nat := [3, 2, 1, 4, 1, 1, 3, 2, 6]
def baseStart_980466 : Nat := 118140960795 + 980466 * 2 ^ 59
def prefixEnd_980466 : Nat := 4983230072969 + 3 ^ 40 * 980466 * 2
def baseEnd_980466 : Nat := 55938924821251795107325

theorem tailTrace_980466 : CollatzResearch.WordTrace tailWord_980466 prefixEnd_980466 55938924821251795107325 := by
  unfold tailWord_980466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8940133216486651776628313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23840355243964404737675501 8940133216486651776628313)
  ·
    refine ⟨6705099912364988832471235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8940133216486651776628313 6705099912364988832471235)
    ·
      refine ⟨10057649868547483248706853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6705099912364988832471235 10057649868547483248706853)
      ·
        refine ⟨1885809350352653109132535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10057649868547483248706853 1885809350352653109132535)
        ·
          refine ⟨2828714025528979663698803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885809350352653109132535 2828714025528979663698803)
          ·
            refine ⟨4243071038293469495548205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828714025528979663698803 4243071038293469495548205)
            ·
              refine ⟨1591151639360051060830577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4243071038293469495548205 1591151639360051060830577)
              ·
                refine ⟨1193363729520038295622933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1591151639360051060830577 1193363729520038295622933)
                ·
                  refine ⟨55938924821251795107325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1193363729520038295622933 55938924821251795107325)
                  ·
                    rfl

theorem cell23_980466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_980466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980466 prefixEnd_980466 := by exact prefixLift 980466
  have htrace : WordTrace (prefixWord ++ tailWord_980466) baseStart_980466 baseEnd_980466 := by
    simpa [prefixWord, tailWord_980466, baseEnd_980466] using wordTrace_append hprefix tailTrace_980466
  have hstable : (prefixWord ++ tailWord_980466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980466).length < 2 ^ (prefixWord ++ tailWord_980466).sum := by decide
  have hdescent : baseEnd_980466 < baseStart_980466 := by decide
  rcases family_descends (prefixWord ++ tailWord_980466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980476 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 3, 1, 3]
def baseStart_980476 : Nat := 118140960795 + 980476 * 2 ^ 59
def prefixEnd_980476 : Nat := 4983230072969 + 3 ^ 40 * 980476 * 2
def baseEnd_980476 : Nat := 503455458197811116840879

theorem tailTrace_980476 : CollatzResearch.WordTrace tailWord_980476 prefixEnd_980476 503455458197811116840879 := by
  unfold tailWord_980476
  simp only [CollatzResearch.WordTrace]
  refine ⟨17880448797955189407188641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23840598397273585876251521 17880448797955189407188641)
  ·
    refine ⟨13410336598466392055391481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17880448797955189407188641 13410336598466392055391481)
    ·
      refine ⟨10057752448849794041543611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13410336598466392055391481 10057752448849794041543611)
      ·
        refine ⟨15086628673274691062315417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10057752448849794041543611 15086628673274691062315417)
        ·
          refine ⟨11314971504956018296736563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15086628673274691062315417 11314971504956018296736563)
          ·
            refine ⟨16972457257434027445104845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11314971504956018296736563 16972457257434027445104845)
            ·
              refine ⟨6364671471537760291914317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16972457257434027445104845 6364671471537760291914317)
              ·
                refine ⟨2386751801826660109467869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6364671471537760291914317 2386751801826660109467869)
                ·
                  refine ⟨895031925684997541050451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2386751801826660109467869 895031925684997541050451)
                  ·
                    refine ⟨1342547888527496311575677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 895031925684997541050451 1342547888527496311575677)
                    ·
                      refine ⟨503455458197811116840879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1342547888527496311575677 503455458197811116840879)
                      ·
                        rfl

theorem cell23_980476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_980476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980476 prefixEnd_980476 := by exact prefixLift 980476
  have htrace : WordTrace (prefixWord ++ tailWord_980476) baseStart_980476 baseEnd_980476 := by
    simpa [prefixWord, tailWord_980476, baseEnd_980476] using wordTrace_append hprefix tailTrace_980476
  have hstable : (prefixWord ++ tailWord_980476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980476).length < 2 ^ (prefixWord ++ tailWord_980476).sum := by decide
  have hdescent : baseEnd_980476 < baseStart_980476 := by decide
  rcases family_descends (prefixWord ++ tailWord_980476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980509 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_980509 : Nat := 118140960795 + 980509 * 2 ^ 59
def prefixEnd_980509 : Nat := 4983230072969 + 3 ^ 40 * 980509 * 2
def baseEnd_980509 : Nat := 167824134353136495909409

theorem tailTrace_980509 : CollatzResearch.WordTrace tailWord_980509 prefixEnd_980509 167824134353136495909409 := by
  unfold tailWord_980509
  simp only [CollatzResearch.WordTrace]
  refine ⟨35762101204790825450328581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23841400803193883633552387 35762101204790825450328581)
  ·
    refine ⟨6705393975898279771936609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35762101204790825450328581 6705393975898279771936609)
    ·
      refine ⟨5029045481923709828952457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6705393975898279771936609 5029045481923709828952457)
      ·
        refine ⟨3771784111442782371714343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5029045481923709828952457 3771784111442782371714343)
        ·
          refine ⟨5657676167164173557571515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3771784111442782371714343 5657676167164173557571515)
          ·
            refine ⟨8486514250746260336357273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5657676167164173557571515 8486514250746260336357273)
            ·
              refine ⟨6364885688059695252267955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8486514250746260336357273 6364885688059695252267955)
              ·
                refine ⟨9547328532089542878401933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6364885688059695252267955 9547328532089542878401933)
                ·
                  refine ⟨3580248199533578579400725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9547328532089542878401933 3580248199533578579400725)
                  ·
                    refine ⟨167824134353136495909409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3580248199533578579400725 167824134353136495909409)
                    ·
                      rfl

theorem cell23_980509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_980509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980509 prefixEnd_980509 := by exact prefixLift 980509
  have htrace : WordTrace (prefixWord ++ tailWord_980509) baseStart_980509 baseEnd_980509 := by
    simpa [prefixWord, tailWord_980509, baseEnd_980509] using wordTrace_append hprefix tailTrace_980509
  have hstable : (prefixWord ++ tailWord_980509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980509).length < 2 ^ (prefixWord ++ tailWord_980509).sum := by decide
  have hdescent : baseEnd_980509 < baseStart_980509 := by decide
  rcases family_descends (prefixWord ++ tailWord_980509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980520 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_980520 : Nat := 118140960795 + 980520 * 2 ^ 59
def prefixEnd_980520 : Nat := 4983230072969 + 3 ^ 40 * 980520 * 2
def baseEnd_980520 : Nat := 503478051346608944690677

theorem tailTrace_980520 : CollatzResearch.WordTrace tailWord_980520 prefixEnd_980520 503478051346608944690677 := by
  unfold tailWord_980520
  simp only [CollatzResearch.WordTrace]
  refine ⟨17881251203875487164489507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23841668271833982885986009 17881251203875487164489507)
  ·
    refine ⟨26821876805813230746734261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17881251203875487164489507 26821876805813230746734261)
    ·
      refine ⟨2514550950544990382506337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26821876805813230746734261 2514550950544990382506337)
      ·
        refine ⟨1885913212908742786879753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2514550950544990382506337 1885913212908742786879753)
        ·
          refine ⟨1414434909681557090159815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1885913212908742786879753 1414434909681557090159815)
          ·
            refine ⟨2121652364522335635239723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414434909681557090159815 2121652364522335635239723)
            ·
              refine ⟨3182478546783503452859585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121652364522335635239723 3182478546783503452859585)
              ·
                refine ⟨2386858910087627589644689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182478546783503452859585 2386858910087627589644689)
                ·
                  refine ⟨1790144182565720692233517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2386858910087627589644689 1790144182565720692233517)
                  ·
                    refine ⟨671304068462145259587569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1790144182565720692233517 671304068462145259587569)
                    ·
                      refine ⟨503478051346608944690677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 671304068462145259587569 503478051346608944690677)
                      ·
                        rfl

theorem cell23_980520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_980520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980520 prefixEnd_980520 := by exact prefixLift 980520
  have htrace : WordTrace (prefixWord ++ tailWord_980520) baseStart_980520 baseEnd_980520 := by
    simpa [prefixWord, tailWord_980520, baseEnd_980520] using wordTrace_append hprefix tailTrace_980520
  have hstable : (prefixWord ++ tailWord_980520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980520).length < 2 ^ (prefixWord ++ tailWord_980520).sum := by decide
  have hdescent : baseEnd_980520 < baseStart_980520 := by decide
  rcases family_descends (prefixWord ++ tailWord_980520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980543 : List Nat := [1, 1, 2, 2, 3, 3, 4, 1, 2, 4]
def baseStart_980543 : Nat := 118140960795 + 980543 * 2 ^ 59
def prefixEnd_980543 : Nat := 4983230072969 + 3 ^ 40 * 980543 * 2
def baseEnd_980543 : Nat := 167829953800554118234357

theorem tailTrace_980543 : CollatzResearch.WordTrace tailWord_980543 prefixEnd_980543 167829953800554118234357 := by
  unfold tailWord_980543
  simp only [CollatzResearch.WordTrace]
  refine ⟨35763341286667649257066283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23842227524445099504710855 35763341286667649257066283)
  ·
    refine ⟨53645011930001473885599425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35763341286667649257066283 53645011930001473885599425)
    ·
      refine ⟨40233758947501105414199569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53645011930001473885599425 40233758947501105414199569)
      ·
        refine ⟨30175319210625829060649677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40233758947501105414199569 30175319210625829060649677)
        ·
          refine ⟨11315744703984685897743629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30175319210625829060649677 11315744703984685897743629)
          ·
            refine ⟨4243404263994257211653861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11315744703984685897743629 4243404263994257211653861)
            ·
              refine ⟨795638299498923227185099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4243404263994257211653861 795638299498923227185099)
              ·
                refine ⟨1193457449248384840777649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795638299498923227185099 1193457449248384840777649)
                ·
                  refine ⟨895093086936288630583237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1193457449248384840777649 895093086936288630583237)
                  ·
                    refine ⟨167829953800554118234357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 895093086936288630583237 167829953800554118234357)
                    ·
                      rfl

theorem cell23_980543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 2, 4].length) (baseStart_980543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980543 prefixEnd_980543 := by exact prefixLift 980543
  have htrace : WordTrace (prefixWord ++ tailWord_980543) baseStart_980543 baseEnd_980543 := by
    simpa [prefixWord, tailWord_980543, baseEnd_980543] using wordTrace_append hprefix tailTrace_980543
  have hstable : (prefixWord ++ tailWord_980543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980543).length < 2 ^ (prefixWord ++ tailWord_980543).sum := by decide
  have hdescent : baseEnd_980543 < baseStart_980543 := by decide
  rcases family_descends (prefixWord ++ tailWord_980543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980550 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_980550 : Nat := 118140960795 + 980550 * 2 ^ 59
def prefixEnd_980550 : Nat := 4983230072969 + 3 ^ 40 * 980550 * 2
def baseEnd_980550 : Nat := 503493455766243827315539

theorem tailTrace_980550 : CollatzResearch.WordTrace tailWord_980550 prefixEnd_980550 503493455766243827315539 := by
  unfold tailWord_980550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117612393676321545392847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23842397731761526301714069 1117612393676321545392847)
  ·
    refine ⟨1676418590514482318089271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1117612393676321545392847 1676418590514482318089271)
    ·
      refine ⟨2514627885771723477133907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1676418590514482318089271 2514627885771723477133907)
      ·
        refine ⟨3771941828657585215700861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2514627885771723477133907 3771941828657585215700861)
        ·
          refine ⟨1414478185746594455887823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3771941828657585215700861 1414478185746594455887823)
          ·
            refine ⟨2121717278619891683831735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414478185746594455887823 2121717278619891683831735)
            ·
              refine ⟨3182575917929837525747603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121717278619891683831735 3182575917929837525747603)
              ·
                refine ⟨4773863876894756288621405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3182575917929837525747603 4773863876894756288621405)
                ·
                  refine ⟨1790198953835533608233027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4773863876894756288621405 1790198953835533608233027)
                  ·
                    refine ⟨2685298430753300412349541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1790198953835533608233027 2685298430753300412349541)
                    ·
                      refine ⟨503493455766243827315539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2685298430753300412349541 503493455766243827315539)
                      ·
                        rfl

theorem cell23_980550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_980550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980550 prefixEnd_980550 := by exact prefixLift 980550
  have htrace : WordTrace (prefixWord ++ tailWord_980550) baseStart_980550 baseEnd_980550 := by
    simpa [prefixWord, tailWord_980550, baseEnd_980550] using wordTrace_append hprefix tailTrace_980550
  have hstable : (prefixWord ++ tailWord_980550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980550).length < 2 ^ (prefixWord ++ tailWord_980550).sum := by decide
  have hdescent : baseEnd_980550 < baseStart_980550 := by decide
  rcases family_descends (prefixWord ++ tailWord_980550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980573 : List Nat := [1, 4, 4, 2, 2, 10]
def baseStart_980573 : Nat := 118140960795 + 980573 * 2 ^ 59
def prefixEnd_980573 : Nat := 4983230072969 + 3 ^ 40 * 980573 * 2
def baseEnd_980573 : Nat := 2072038130951840482831

theorem tailTrace_980573 : CollatzResearch.WordTrace tailWord_980573 prefixEnd_980573 2072038130951840482831 := by
  unfold tailWord_980573
  simp only [CollatzResearch.WordTrace]
  refine ⟨35764435476558964380658373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23842956984372642920438915 35764435476558964380658373)
  ·
    refine ⟨6705831651854805821373445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35764435476558964380658373 6705831651854805821373445)
    ·
      refine ⟨1257343434722776091507521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6705831651854805821373445 1257343434722776091507521)
      ·
        refine ⟨943007576042082068630641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1257343434722776091507521 943007576042082068630641)
        ·
          refine ⟨707255682031561551472981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 943007576042082068630641 707255682031561551472981)
          ·
            refine ⟨2072038130951840482831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 707255682031561551472981 2072038130951840482831)
            ·
              rfl

theorem cell23_980573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 10].length) (baseStart_980573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980573 prefixEnd_980573 := by exact prefixLift 980573
  have htrace : WordTrace (prefixWord ++ tailWord_980573) baseStart_980573 baseEnd_980573 := by
    simpa [prefixWord, tailWord_980573, baseEnd_980573] using wordTrace_append hprefix tailTrace_980573
  have hstable : (prefixWord ++ tailWord_980573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980573).length < 2 ^ (prefixWord ++ tailWord_980573).sum := by decide
  have hdescent : baseEnd_980573 < baseStart_980573 := by decide
  rcases family_descends (prefixWord ++ tailWord_980573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980583 : List Nat := [1, 1, 5, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_980583 : Nat := 118140960795 + 980583 * 2 ^ 59
def prefixEnd_980583 : Nat := 4983230072969 + 3 ^ 40 * 980583 * 2
def baseEnd_980583 : Nat := 503510400627842198202887

theorem tailTrace_980583 : CollatzResearch.WordTrace tailWord_980583 prefixEnd_980583 503510400627842198202887 := by
  unfold tailWord_980583
  simp only [CollatzResearch.WordTrace]
  refine ⟨35764800206522736088522403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23843200137681824059014935 35764800206522736088522403)
  ·
    refine ⟨53647200309784104132783605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35764800206522736088522403 53647200309784104132783605)
    ·
      refine ⟨5029425029042259762448463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53647200309784104132783605 5029425029042259762448463)
      ·
        refine ⟨7544137543563389643672695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5029425029042259762448463 7544137543563389643672695)
        ·
          refine ⟨11316206315345084465509043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7544137543563389643672695 11316206315345084465509043)
          ·
            refine ⟨16974309473017626698263565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11316206315345084465509043 16974309473017626698263565)
            ·
              refine ⟨6365366052381610011848837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16974309473017626698263565 6365366052381610011848837)
              ·
                refine ⟨1193506134821551877221657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6365366052381610011848837 1193506134821551877221657)
                ·
                  refine ⟨895129601116163907916243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1193506134821551877221657 895129601116163907916243)
                  ·
                    refine ⟨1342694401674245861874365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 895129601116163907916243 1342694401674245861874365)
                    ·
                      refine ⟨503510400627842198202887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1342694401674245861874365 503510400627842198202887)
                      ·
                        rfl

theorem cell23_980583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_980583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980583 prefixEnd_980583 := by exact prefixLift 980583
  have htrace : WordTrace (prefixWord ++ tailWord_980583) baseStart_980583 baseEnd_980583 := by
    simpa [prefixWord, tailWord_980583, baseEnd_980583] using wordTrace_append hprefix tailTrace_980583
  have hstable : (prefixWord ++ tailWord_980583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980583).length < 2 ^ (prefixWord ++ tailWord_980583).sum := by decide
  have hdescent : baseEnd_980583 < baseStart_980583 := by decide
  rcases family_descends (prefixWord ++ tailWord_980583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980584 : List Nat := [2, 1, 4, 3, 1, 1, 4, 2, 1, 2, 2]
def baseStart_980584 : Nat := 118140960795 + 980584 * 2 ^ 59
def prefixEnd_980584 : Nat := 4983230072969 + 3 ^ 40 * 980584 * 2
def baseEnd_980584 : Nat := 503510914108496694290383

theorem tailTrace_980584 : CollatzResearch.WordTrace tailWord_980584 prefixEnd_980584 503510914108496694290383 := by
  unfold tailWord_980584
  simp only [CollatzResearch.WordTrace]
  refine ⟨17882418339759556629654403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23843224453012742172872537 17882418339759556629654403)
  ·
    refine ⟨26823627509639334944481605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17882418339759556629654403 26823627509639334944481605)
    ·
      refine ⟨5029430158057375302090301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26823627509639334944481605 5029430158057375302090301)
      ·
        refine ⟨1886036309271515738283863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5029430158057375302090301 1886036309271515738283863)
        ·
          refine ⟨2829054463907273607425795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886036309271515738283863 2829054463907273607425795)
          ·
            refine ⟨4243581695860910411138693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829054463907273607425795 4243581695860910411138693)
            ·
              refine ⟨795671567973920702088505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4243581695860910411138693 795671567973920702088505)
              ·
                refine ⟨596753675980440526566379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795671567973920702088505 596753675980440526566379)
                ·
                  refine ⟨895130513970660789849569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596753675980440526566379 895130513970660789849569)
                  ·
                    refine ⟨671347885477995592387177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 895130513970660789849569 671347885477995592387177)
                    ·
                      refine ⟨503510914108496694290383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 671347885477995592387177 503510914108496694290383)
                      ·
                        rfl

theorem cell23_980584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_980584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980584 prefixEnd_980584 := by exact prefixLift 980584
  have htrace : WordTrace (prefixWord ++ tailWord_980584) baseStart_980584 baseEnd_980584 := by
    simpa [prefixWord, tailWord_980584, baseEnd_980584] using wordTrace_append hprefix tailTrace_980584
  have hstable : (prefixWord ++ tailWord_980584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980584).length < 2 ^ (prefixWord ++ tailWord_980584).sum := by decide
  have hdescent : baseEnd_980584 < baseStart_980584 := by decide
  rcases family_descends (prefixWord ++ tailWord_980584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980619 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 4]
def baseStart_980619 : Nat := 118140960795 + 980619 * 2 ^ 59
def prefixEnd_980619 : Nat := 4983230072969 + 3 ^ 40 * 980619 * 2
def baseEnd_980619 : Nat := 503528885931404057352721

theorem tailTrace_980619 : CollatzResearch.WordTrace tailWord_980619 prefixEnd_980619 503528885931404057352721 := by
  unfold tailWord_980619
  simp only [CollatzResearch.WordTrace]
  refine ⟨35766113234392314236832911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23844075489594876157888607 35766113234392314236832911)
  ·
    refine ⟨53649169851588471355249367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35766113234392314236832911 53649169851588471355249367)
    ·
      refine ⟨80473754777382707032874051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53649169851588471355249367 80473754777382707032874051)
      ·
        refine ⟨120710632166074060549311077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80473754777382707032874051 120710632166074060549311077)
        ·
          refine ⟨22633243531138886352995827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120710632166074060549311077 22633243531138886352995827)
          ·
            refine ⟨33949865296708329529493741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22633243531138886352995827 33949865296708329529493741)
            ·
              refine ⟨12731199486265623573560153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33949865296708329529493741 12731199486265623573560153)
              ·
                refine ⟨9548399614699217680170115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12731199486265623573560153 9548399614699217680170115)
                ·
                  refine ⟨14322599422048826520255173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9548399614699217680170115 14322599422048826520255173)
                  ·
                    refine ⟨2685487391634154972547845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14322599422048826520255173 2685487391634154972547845)
                    ·
                      refine ⟨503528885931404057352721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2685487391634154972547845 503528885931404057352721)
                      ·
                        rfl

theorem cell23_980619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 4].length) (baseStart_980619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980619 prefixEnd_980619 := by exact prefixLift 980619
  have htrace : WordTrace (prefixWord ++ tailWord_980619) baseStart_980619 baseEnd_980619 := by
    simpa [prefixWord, tailWord_980619, baseEnd_980619] using wordTrace_append hprefix tailTrace_980619
  have hstable : (prefixWord ++ tailWord_980619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980619).length < 2 ^ (prefixWord ++ tailWord_980619).sum := by decide
  have hdescent : baseEnd_980619 < baseStart_980619 := by decide
  rcases family_descends (prefixWord ++ tailWord_980619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980640 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 4, 2, 2]
def baseStart_980640 : Nat := 118140960795 + 980640 * 2 ^ 59
def prefixEnd_980640 : Nat := 4983230072969 + 3 ^ 40 * 980640 * 2
def baseEnd_980640 : Nat := 503539669025148475190125

theorem tailTrace_980640 : CollatzResearch.WordTrace tailWord_980640 prefixEnd_980640 503539669025148475190125 := by
  unfold tailWord_980640
  simp only [CollatzResearch.WordTrace]
  refine ⟨17883439583658117411673687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23844586111544156548898249 17883439583658117411673687)
  ·
    refine ⟨26825159375487176117510531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17883439583658117411673687 26825159375487176117510531)
    ·
      refine ⟨40237739063230764176265797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26825159375487176117510531 40237739063230764176265797)
      ·
        refine ⟨7544576074355768283049837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40237739063230764176265797 7544576074355768283049837)
        ·
          refine ⟨2829216027883413106143689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7544576074355768283049837 2829216027883413106143689)
          ·
            refine ⟨2121912020912559829607767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2829216027883413106143689 2121912020912559829607767)
            ·
              refine ⟨3182868031368839744411651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121912020912559829607767 3182868031368839744411651)
              ·
                refine ⟨4774302047053259616617477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3182868031368839744411651 4774302047053259616617477)
                ·
                  refine ⟨895181633822486178115777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4774302047053259616617477 895181633822486178115777)
                  ·
                    refine ⟨671386225366864633586833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 895181633822486178115777 671386225366864633586833)
                    ·
                      refine ⟨503539669025148475190125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 671386225366864633586833 503539669025148475190125)
                      ·
                        rfl

theorem cell23_980640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_980640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980640 prefixEnd_980640 := by exact prefixLift 980640
  have htrace : WordTrace (prefixWord ++ tailWord_980640) baseStart_980640 baseEnd_980640 := by
    simpa [prefixWord, tailWord_980640, baseEnd_980640] using wordTrace_append hprefix tailTrace_980640
  have hstable : (prefixWord ++ tailWord_980640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980640).length < 2 ^ (prefixWord ++ tailWord_980640).sum := by decide
  have hdescent : baseEnd_980640 < baseStart_980640 := by decide
  rcases family_descends (prefixWord ++ tailWord_980640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980656 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 3]
def baseStart_980656 : Nat := 118140960795 + 980656 * 2 ^ 59
def prefixEnd_980656 : Nat := 4983230072969 + 3 ^ 40 * 980656 * 2
def baseEnd_980656 : Nat := 503547884715620412590051

theorem tailTrace_980656 : CollatzResearch.WordTrace tailWord_980656 prefixEnd_980656 503547884715620412590051 := by
  unfold tailWord_980656
  simp only [CollatzResearch.WordTrace]
  refine ⟨17883731367629134777964911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23844975156838846370619881 17883731367629134777964911)
  ·
    refine ⟨26825597051443702166947367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17883731367629134777964911 26825597051443702166947367)
    ·
      refine ⟨40238395577165553250421051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26825597051443702166947367 40238395577165553250421051)
      ·
        refine ⟨60357593365748329875631577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40238395577165553250421051 60357593365748329875631577)
        ·
          refine ⟨45268195024311247406723683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60357593365748329875631577 45268195024311247406723683)
          ·
            refine ⟨67902292536466871110085525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45268195024311247406723683 67902292536466871110085525)
            ·
              refine ⟨3182919962646884583285259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67902292536466871110085525 3182919962646884583285259)
              ·
                refine ⟨4774379943970326874927889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3182919962646884583285259 4774379943970326874927889)
                ·
                  refine ⟨3580784957977745156195917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4774379943970326874927889 3580784957977745156195917)
                  ·
                    refine ⟨1342794359241654433573469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3580784957977745156195917 1342794359241654433573469)
                    ·
                      refine ⟨503547884715620412590051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1342794359241654433573469 503547884715620412590051)
                      ·
                        rfl

theorem cell23_980656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 3].length) (baseStart_980656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980656 prefixEnd_980656 := by exact prefixLift 980656
  have htrace : WordTrace (prefixWord ++ tailWord_980656) baseStart_980656 baseEnd_980656 := by
    simpa [prefixWord, tailWord_980656, baseEnd_980656] using wordTrace_append hprefix tailTrace_980656
  have hstable : (prefixWord ++ tailWord_980656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980656).length < 2 ^ (prefixWord ++ tailWord_980656).sum := by decide
  have hdescent : baseEnd_980656 < baseStart_980656 := by decide
  rcases family_descends (prefixWord ++ tailWord_980656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980659 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 3, 7]
def baseStart_980659 : Nat := 118140960795 + 980659 * 2 ^ 59
def prefixEnd_980659 : Nat := 4983230072969 + 3 ^ 40 * 980659 * 2
def baseEnd_980659 : Nat := 167849808385861300284179

theorem tailTrace_980659 : CollatzResearch.WordTrace tailWord_980659 prefixEnd_980659 167849808385861300284179 := by
  unfold tailWord_980659
  simp only [CollatzResearch.WordTrace]
  refine ⟨35767572154247401068289031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23845048102831600712192687 35767572154247401068289031)
  ·
    refine ⟨53651358231371101602433547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35767572154247401068289031 53651358231371101602433547)
    ·
      refine ⟨80477037347056652403650321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53651358231371101602433547 80477037347056652403650321)
      ·
        refine ⟨60357778010292489302737741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80477037347056652403650321 60357778010292489302737741)
        ·
          refine ⟨22634166753859683488526653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60357778010292489302737741 22634166753859683488526653)
          ·
            refine ⟨8487812532697381308197495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22634166753859683488526653 8487812532697381308197495)
            ·
              refine ⟨12731718799046071962296243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8487812532697381308197495 12731718799046071962296243)
              ·
                refine ⟨19097578198569107943444365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12731718799046071962296243 19097578198569107943444365)
                ·
                  refine ⟨7161591824463415478791637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19097578198569107943444365 7161591824463415478791637)
                  ·
                    refine ⟨167849808385861300284179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7161591824463415478791637 167849808385861300284179)
                    ·
                      rfl

theorem cell23_980659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 7].length) (baseStart_980659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980659 prefixEnd_980659 := by exact prefixLift 980659
  have htrace : WordTrace (prefixWord ++ tailWord_980659) baseStart_980659 baseEnd_980659 := by
    simpa [prefixWord, tailWord_980659, baseEnd_980659] using wordTrace_append hprefix tailTrace_980659
  have hstable : (prefixWord ++ tailWord_980659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980659).length < 2 ^ (prefixWord ++ tailWord_980659).sum := by decide
  have hdescent : baseEnd_980659 < baseStart_980659 := by decide
  rcases family_descends (prefixWord ++ tailWord_980659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980676 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_980676 : Nat := 118140960795 + 980676 * 2 ^ 59
def prefixEnd_980676 : Nat := 4983230072969 + 3 ^ 40 * 980676 * 2
def baseEnd_980676 : Nat := 167852718109570111446653

theorem tailTrace_980676 : CollatzResearch.WordTrace tailWord_980676 prefixEnd_980676 167852718109570111446653 := by
  unfold tailWord_980676
  simp only [CollatzResearch.WordTrace]
  refine ⟨17884096097592906485828941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23845461463457208647771921 17884096097592906485828941)
  ·
    refine ⟨6706536036597339932185853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17884096097592906485828941 6706536036597339932185853)
    ·
      refine ⟨2514951013724002474569695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6706536036597339932185853 2514951013724002474569695)
      ·
        refine ⟨3772426520586003711854543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2514951013724002474569695 3772426520586003711854543)
        ·
          refine ⟨5658639780879005567781815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3772426520586003711854543 5658639780879005567781815)
          ·
            refine ⟨8487959671318508351672723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5658639780879005567781815 8487959671318508351672723)
            ·
              refine ⟨12731939506977762527509085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8487959671318508351672723 12731939506977762527509085)
              ·
                refine ⟨4774477315116660947815907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12731939506977762527509085 4774477315116660947815907)
                ·
                  refine ⟨7161715972674991421723861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4774477315116660947815907 7161715972674991421723861)
                  ·
                    refine ⟨167852718109570111446653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7161715972674991421723861 167852718109570111446653)
                    ·
                      rfl

theorem cell23_980676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_980676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980676 prefixEnd_980676 := by exact prefixLift 980676
  have htrace : WordTrace (prefixWord ++ tailWord_980676) baseStart_980676 baseEnd_980676 := by
    simpa [prefixWord, tailWord_980676, baseEnd_980676] using wordTrace_append hprefix tailTrace_980676
  have hstable : (prefixWord ++ tailWord_980676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980676).length < 2 ^ (prefixWord ++ tailWord_980676).sum := by decide
  have hdescent : baseEnd_980676 < baseStart_980676 := by decide
  rcases family_descends (prefixWord ++ tailWord_980676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980686 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_980686 : Nat := 118140960795 + 980686 * 2 ^ 59
def prefixEnd_980686 : Nat := 4983230072969 + 3 ^ 40 * 980686 * 2
def baseEnd_980686 : Nat := 503563289135255295214913

theorem tailTrace_980686 : CollatzResearch.WordTrace tailWord_980686 prefixEnd_980686 503563289135255295214913 := by
  unfold tailWord_980686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4471069615643698084940239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23845704616766389786347941 4471069615643698084940239)
  ·
    refine ⟨6706604423465547127410359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4471069615643698084940239 6706604423465547127410359)
    ·
      refine ⟨10059906635198320691115539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6706604423465547127410359 10059906635198320691115539)
      ·
        refine ⟨15089859952797481036673309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10059906635198320691115539 15089859952797481036673309)
        ·
          refine ⟨5658697482299055388752491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15089859952797481036673309 5658697482299055388752491)
          ·
            refine ⟨8488046223448583083128737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5658697482299055388752491 8488046223448583083128737)
            ·
              refine ⟨6366034667586437312346553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8488046223448583083128737 6366034667586437312346553)
              ·
                refine ⟨4774526000689827984259915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6366034667586437312346553 4774526000689827984259915)
                ·
                  refine ⟨7161789001034741976389873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4774526000689827984259915 7161789001034741976389873)
                  ·
                    refine ⟨5371341750776056482292405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7161789001034741976389873 5371341750776056482292405)
                    ·
                      refine ⟨503563289135255295214913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5371341750776056482292405 503563289135255295214913)
                      ·
                        rfl

theorem cell23_980686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_980686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980686 prefixEnd_980686 := by exact prefixLift 980686
  have htrace : WordTrace (prefixWord ++ tailWord_980686) baseStart_980686 baseEnd_980686 := by
    simpa [prefixWord, tailWord_980686, baseEnd_980686] using wordTrace_append hprefix tailTrace_980686
  have hstable : (prefixWord ++ tailWord_980686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980686).length < 2 ^ (prefixWord ++ tailWord_980686).sum := by decide
  have hdescent : baseEnd_980686 < baseStart_980686 := by decide
  rcases family_descends (prefixWord ++ tailWord_980686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980716 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 3]
def baseStart_980716 : Nat := 118140960795 + 980716 * 2 ^ 59
def prefixEnd_980716 : Nat := 4983230072969 + 3 ^ 40 * 980716 * 2
def baseEnd_980716 : Nat := 503578693554890177839775

theorem tailTrace_980716 : CollatzResearch.WordTrace tailWord_980716 prefixEnd_980716 503578693554890177839775 := by
  unfold tailWord_980716
  simp only [CollatzResearch.WordTrace]
  refine ⟨17884825557520449901557001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23846434076693933202076001 17884825557520449901557001)
  ·
    refine ⟨13413619168140337426167751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17884825557520449901557001 13413619168140337426167751)
    ·
      refine ⟨20120428752210506139251627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13413619168140337426167751 20120428752210506139251627)
      ·
        refine ⟨30180643128315759208877441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20120428752210506139251627 30180643128315759208877441)
        ·
          refine ⟨22635482346236819406658081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30180643128315759208877441 22635482346236819406658081)
          ·
            refine ⟨16976611759677614554993561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22635482346236819406658081 16976611759677614554993561)
            ·
              refine ⟨12732458819758210916245171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16976611759677614554993561 12732458819758210916245171)
              ·
                refine ⟨19098688229637316374367757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12732458819758210916245171 19098688229637316374367757)
                ·
                  refine ⟨7162008086113993640387909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19098688229637316374367757 7162008086113993640387909)
                  ·
                    refine ⟨1342876516146373807572733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7162008086113993640387909 1342876516146373807572733)
                    ·
                      refine ⟨503578693554890177839775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1342876516146373807572733 503578693554890177839775)
                      ·
                        rfl

theorem cell23_980716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_980716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980716 prefixEnd_980716 := by exact prefixLift 980716
  have htrace : WordTrace (prefixWord ++ tailWord_980716) baseStart_980716 baseEnd_980716 := by
    simpa [prefixWord, tailWord_980716, baseEnd_980716] using wordTrace_append hprefix tailTrace_980716
  have hstable : (prefixWord ++ tailWord_980716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980716).length < 2 ^ (prefixWord ++ tailWord_980716).sum := by decide
  have hdescent : baseEnd_980716 < baseStart_980716 := by decide
  rcases family_descends (prefixWord ++ tailWord_980716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980757 : List Nat := [1, 3, 2, 1, 2, 3, 4, 2, 1, 4]
def baseStart_980757 : Nat := 118140960795 + 980757 * 2 ^ 59
def prefixEnd_980757 : Nat := 4983230072969 + 3 ^ 40 * 980757 * 2
def baseEnd_980757 : Nat := 167866582087241505809029

theorem tailTrace_980757 : CollatzResearch.WordTrace tailWord_980757 prefixEnd_980757 167866582087241505809029 := by
  unfold tailWord_980757
  simp only [CollatzResearch.WordTrace]
  refine ⟨35771146507892363805356525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23847431005261575870237683 35771146507892363805356525)
  ·
    refine ⟨13414179940459636427008697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35771146507892363805356525 13414179940459636427008697)
    ·
      refine ⟨10060634955344727320256523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13414179940459636427008697 10060634955344727320256523)
      ·
        refine ⟨15090952433017090980384785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10060634955344727320256523 15090952433017090980384785)
        ·
          refine ⟨11318214324762818235288589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15090952433017090980384785 11318214324762818235288589)
          ·
            refine ⟨4244330371786056838233221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11318214324762818235288589 4244330371786056838233221)
            ·
              refine ⟨795811944709885657168729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4244330371786056838233221 795811944709885657168729)
              ·
                refine ⟨596858958532414242876547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 795811944709885657168729 596858958532414242876547)
                ·
                  refine ⟨895288437798621364314821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596858958532414242876547 895288437798621364314821)
                  ·
                    refine ⟨167866582087241505809029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 895288437798621364314821 167866582087241505809029)
                    ·
                      rfl

theorem cell23_980757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_980757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980757 prefixEnd_980757 := by exact prefixLift 980757
  have htrace : WordTrace (prefixWord ++ tailWord_980757) baseStart_980757 baseEnd_980757 := by
    simpa [prefixWord, tailWord_980757, baseEnd_980757] using wordTrace_append hprefix tailTrace_980757
  have hstable : (prefixWord ++ tailWord_980757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980757).length < 2 ^ (prefixWord ++ tailWord_980757).sum := by decide
  have hdescent : baseEnd_980757 < baseStart_980757 := by decide
  rcases family_descends (prefixWord ++ tailWord_980757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980780 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 3]
def baseStart_980780 : Nat := 118140960795 + 980780 * 2 ^ 59
def prefixEnd_980780 : Nat := 4983230072969 + 3 ^ 40 * 980780 * 2
def baseEnd_980780 : Nat := 503611556316777927439481

theorem tailTrace_980780 : CollatzResearch.WordTrace tailWord_980780 prefixEnd_980780 503611556316777927439481 := by
  unfold tailWord_980780
  simp only [CollatzResearch.WordTrace]
  refine ⟨17885992693404519366721897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23847990257872692488962529 17885992693404519366721897)
  ·
    refine ⟨13414494520053389525041423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17885992693404519366721897 13414494520053389525041423)
    ·
      refine ⟨20121741780080084287562135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13414494520053389525041423 20121741780080084287562135)
      ·
        refine ⟨30182612670120126431343203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20121741780080084287562135 30182612670120126431343203)
        ·
          refine ⟨45273919005180189647014805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30182612670120126431343203 45273919005180189647014805)
          ·
            refine ⟨2122214953367821389703819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45273919005180189647014805 2122214953367821389703819)
            ·
              refine ⟨3183322430051732084555729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122214953367821389703819 3183322430051732084555729)
              ·
                refine ⟨2387491822538799063416797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3183322430051732084555729 2387491822538799063416797)
                ·
                  refine ⟨895309433452049648781299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2387491822538799063416797 895309433452049648781299)
                  ·
                    refine ⟨1342964150178074473171949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 895309433452049648781299 1342964150178074473171949)
                    ·
                      refine ⟨503611556316777927439481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1342964150178074473171949 503611556316777927439481)
                      ·
                        rfl

theorem cell23_980780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_980780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980780 prefixEnd_980780 := by exact prefixLift 980780
  have htrace : WordTrace (prefixWord ++ tailWord_980780) baseStart_980780 baseEnd_980780 := by
    simpa [prefixWord, tailWord_980780, baseEnd_980780] using wordTrace_append hprefix tailTrace_980780
  have hstable : (prefixWord ++ tailWord_980780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980780).length < 2 ^ (prefixWord ++ tailWord_980780).sum := by decide
  have hdescent : baseEnd_980780 < baseStart_980780 := by decide
  rcases family_descends (prefixWord ++ tailWord_980780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980816 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 6]
def baseStart_980816 : Nat := 118140960795 + 980816 * 2 ^ 59
def prefixEnd_980816 : Nat := 4983230072969 + 3 ^ 40 * 980816 * 2
def baseEnd_980816 : Nat := 503630041620339786589315

theorem tailTrace_980816 : CollatzResearch.WordTrace tailWord_980816 prefixEnd_980816 503630041620339786589315 := by
  unfold tailWord_980816
  simp only [CollatzResearch.WordTrace]
  refine ⟨17886649207339308440877151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23848865609785744587836201 17886649207339308440877151)
  ·
    refine ⟨26829973811008962661315727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17886649207339308440877151 26829973811008962661315727)
    ·
      refine ⟨40244960716513443991973591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26829973811008962661315727 40244960716513443991973591)
      ·
        refine ⟨60367441074770165987960387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40244960716513443991973591 60367441074770165987960387)
        ·
          refine ⟨90551161612155248981940581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60367441074770165987960387 90551161612155248981940581)
          ·
            refine ⟨16978342802279109184113859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90551161612155248981940581 16978342802279109184113859)
            ·
              refine ⟨25467514203418663776170789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16978342802279109184113859 25467514203418663776170789)
              ·
                refine ⟨4775158913140999458032023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25467514203418663776170789 4775158913140999458032023)
                ·
                  refine ⟨7162738369711499187048035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775158913140999458032023 7162738369711499187048035)
                  ·
                    refine ⟨10744107554567248780572053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7162738369711499187048035 10744107554567248780572053)
                    ·
                      refine ⟨503630041620339786589315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10744107554567248780572053 503630041620339786589315)
                      ·
                        rfl

theorem cell23_980816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_980816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980816 prefixEnd_980816 := by exact prefixLift 980816
  have htrace : WordTrace (prefixWord ++ tailWord_980816) baseStart_980816 baseEnd_980816 := by
    simpa [prefixWord, tailWord_980816, baseEnd_980816] using wordTrace_append hprefix tailTrace_980816
  have hstable : (prefixWord ++ tailWord_980816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980816).length < 2 ^ (prefixWord ++ tailWord_980816).sum := by decide
  have hdescent : baseEnd_980816 < baseStart_980816 := by decide
  rcases family_descends (prefixWord ++ tailWord_980816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980826 : List Nat := [3, 1, 1, 2, 1, 3, 2, 10]
def baseStart_980826 : Nat := 118140960795 + 980826 * 2 ^ 59
def prefixEnd_980826 : Nat := 4983230072969 + 3 ^ 40 * 980826 * 2
def baseEnd_980826 : Nat := 18653154682477212869047

theorem tailTrace_980826 : CollatzResearch.WordTrace tailWord_980826 prefixEnd_980826 18653154682477212869047 := by
  unfold tailWord_980826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8943415786160597147404583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23849108763094925726412221 8943415786160597147404583)
  ·
    refine ⟨13415123679240895721106875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8943415786160597147404583 13415123679240895721106875)
    ·
      refine ⟨20122685518861343581660313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13415123679240895721106875 20122685518861343581660313)
      ·
        refine ⟨15092014139146007686245235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20122685518861343581660313 15092014139146007686245235)
        ·
          refine ⟨22638021208719011529367853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15092014139146007686245235 22638021208719011529367853)
          ·
            refine ⟨8489257953269629323512945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22638021208719011529367853 8489257953269629323512945)
            ·
              refine ⟨6366943464952221992634709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8489257953269629323512945 6366943464952221992634709)
              ·
                refine ⟨18653154682477212869047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6366943464952221992634709 18653154682477212869047)
                ·
                  rfl

theorem cell23_980826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 10].length) (baseStart_980826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980826 prefixEnd_980826 := by exact prefixLift 980826
  have htrace : WordTrace (prefixWord ++ tailWord_980826) baseStart_980826 baseEnd_980826 := by
    simpa [prefixWord, tailWord_980826, baseEnd_980826] using wordTrace_append hprefix tailTrace_980826
  have hstable : (prefixWord ++ tailWord_980826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980826).length < 2 ^ (prefixWord ++ tailWord_980826).sum := by decide
  have hdescent : baseEnd_980826 < baseStart_980826 := by decide
  rcases family_descends (prefixWord ++ tailWord_980826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980871 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 3, 2, 2]
def baseStart_980871 : Nat := 118140960795 + 980871 * 2 ^ 59
def prefixEnd_980871 : Nat := 4983230072969 + 3 ^ 40 * 980871 * 2
def baseEnd_980871 : Nat := 503658283056337071401563

theorem tailTrace_980871 : CollatzResearch.WordTrace tailWord_980871 prefixEnd_980871 503658283056337071401563 := by
  unfold tailWord_980871
  simp only [CollatzResearch.WordTrace]
  refine ⟨35775304429479361275006467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23850202952986240850004311 35775304429479361275006467)
  ·
    refine ⟨53662956644219041912509701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35775304429479361275006467 53662956644219041912509701)
    ·
      refine ⟨10061804370791070358595569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53662956644219041912509701 10061804370791070358595569)
      ·
        refine ⟨7546353278093302768946677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10061804370791070358595569 7546353278093302768946677)
        ·
          refine ⟨707470619821247134588751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7546353278093302768946677 707470619821247134588751)
          ·
            refine ⟨1061205929731870701883127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707470619821247134588751 1061205929731870701883127)
            ·
              refine ⟨1591808894597806052824691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061205929731870701883127 1591808894597806052824691)
              ·
                refine ⟨2387713341896709079237037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1591808894597806052824691 2387713341896709079237037)
                ·
                  refine ⟨895392503211265904713889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2387713341896709079237037 895392503211265904713889)
                  ·
                    refine ⟨671544377408449428535417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 895392503211265904713889 671544377408449428535417)
                    ·
                      refine ⟨503658283056337071401563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 671544377408449428535417 503658283056337071401563)
                      ·
                        rfl

theorem cell23_980871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_980871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980871 prefixEnd_980871 := by exact prefixLift 980871
  have htrace : WordTrace (prefixWord ++ tailWord_980871) baseStart_980871 baseEnd_980871 := by
    simpa [prefixWord, tailWord_980871, baseEnd_980871] using wordTrace_append hprefix tailTrace_980871
  have hstable : (prefixWord ++ tailWord_980871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980871).length < 2 ^ (prefixWord ++ tailWord_980871).sum := by decide
  have hdescent : baseEnd_980871 < baseStart_980871 := by decide
  rcases family_descends (prefixWord ++ tailWord_980871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980887 : List Nat := [1, 1, 3, 3, 1, 4, 1, 3, 2, 1, 3]
def baseStart_980887 : Nat := 118140960795 + 980887 * 2 ^ 59
def prefixEnd_980887 : Nat := 4983230072969 + 3 ^ 40 * 980887 * 2
def baseEnd_980887 : Nat := 503666498746809008801489

theorem tailTrace_980887 : CollatzResearch.WordTrace tailWord_980887 prefixEnd_980887 503666498746809008801489 := by
  unfold tailWord_980887
  simp only [CollatzResearch.WordTrace]
  refine ⟨35775887997421396007588915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23850591998280930671725943 35775887997421396007588915)
  ·
    refine ⟨53663831996132094011383373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35775887997421396007588915 53663831996132094011383373)
    ·
      refine ⟨20123936998549535254268765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53663831996132094011383373 20123936998549535254268765)
      ·
        refine ⟨7546476374456075720350787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20123936998549535254268765 7546476374456075720350787)
        ·
          refine ⟨11319714561684113580526181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7546476374456075720350787 11319714561684113580526181)
          ·
            refine ⟨2122446480315771296348659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11319714561684113580526181 2122446480315771296348659)
            ·
              refine ⟨3183669720473656944522989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122446480315771296348659 3183669720473656944522989)
              ·
                refine ⟨1193876145177621354196121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3183669720473656944522989 1193876145177621354196121)
                ·
                  refine ⟨895407108883216015647091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1193876145177621354196121 895407108883216015647091)
                  ·
                    refine ⟨1343110663324824023470637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 895407108883216015647091 1343110663324824023470637)
                    ·
                      refine ⟨503666498746809008801489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1343110663324824023470637 503666498746809008801489)
                      ·
                        rfl

theorem cell23_980887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_980887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980887 prefixEnd_980887 := by exact prefixLift 980887
  have htrace : WordTrace (prefixWord ++ tailWord_980887) baseStart_980887 baseEnd_980887 := by
    simpa [prefixWord, tailWord_980887, baseEnd_980887] using wordTrace_append hprefix tailTrace_980887
  have hstable : (prefixWord ++ tailWord_980887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980887).length < 2 ^ (prefixWord ++ tailWord_980887).sum := by decide
  have hdescent : baseEnd_980887 < baseStart_980887 := by decide
  rcases family_descends (prefixWord ++ tailWord_980887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980904 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_980904 : Nat := 118140960795 + 980904 * 2 ^ 59
def prefixEnd_980904 : Nat := 4983230072969 + 3 ^ 40 * 980904 * 2
def baseEnd_980904 : Nat := 503675227917935442288911

theorem tailTrace_980904 : CollatzResearch.WordTrace tailWord_980904 prefixEnd_980904 503675227917935442288911 := by
  unfold tailWord_980904
  simp only [CollatzResearch.WordTrace]
  refine ⟨17888254019179903955478883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23851005358906538607305177 17888254019179903955478883)
  ·
    refine ⟨26832381028769855933218325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17888254019179903955478883 26832381028769855933218325)
    ·
      refine ⟨1257767860723586996869609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26832381028769855933218325 1257767860723586996869609)
      ·
        refine ⟨943325895542690247652207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1257767860723586996869609 943325895542690247652207)
        ·
          refine ⟨1414988843314035371478311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943325895542690247652207 1414988843314035371478311)
          ·
            refine ⟨2122483264971053057217467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414988843314035371478311 2122483264971053057217467)
            ·
              refine ⟨3183724897456579585826201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122483264971053057217467 3183724897456579585826201)
              ·
                refine ⟨2387793673092434689369651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3183724897456579585826201 2387793673092434689369651)
                ·
                  refine ⟨3581690509638652034054477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387793673092434689369651 3581690509638652034054477)
                  ·
                    refine ⟨1343133941114494512770429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3581690509638652034054477 1343133941114494512770429)
                    ·
                      refine ⟨503675227917935442288911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1343133941114494512770429 503675227917935442288911)
                      ·
                        rfl

theorem cell23_980904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_980904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980904 prefixEnd_980904 := by exact prefixLift 980904
  have htrace : WordTrace (prefixWord ++ tailWord_980904) baseStart_980904 baseEnd_980904 := by
    simpa [prefixWord, tailWord_980904, baseEnd_980904] using wordTrace_append hprefix tailTrace_980904
  have hstable : (prefixWord ++ tailWord_980904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980904).length < 2 ^ (prefixWord ++ tailWord_980904).sum := by decide
  have hdescent : baseEnd_980904 < baseStart_980904 := by decide
  rcases family_descends (prefixWord ++ tailWord_980904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980940 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 2, 2, 4]
def baseStart_980940 : Nat := 118140960795 + 980940 * 2 ^ 59
def prefixEnd_980940 : Nat := 4983230072969 + 3 ^ 40 * 980940 * 2
def baseEnd_980940 : Nat := 503693713221497301438745

theorem tailTrace_980940 : CollatzResearch.WordTrace tailWord_980940 prefixEnd_980940 503693713221497301438745 := by
  unfold tailWord_980940
  simp only [CollatzResearch.WordTrace]
  refine ⟨17888910533114693029634137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23851880710819590706178849 17888910533114693029634137)
  ·
    refine ⟨13416682899836019772225603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17888910533114693029634137 13416682899836019772225603)
    ·
      refine ⟨20125024349754029658338405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13416682899836019772225603 20125024349754029658338405)
      ·
        refine ⟨3773442065578880560938451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20125024349754029658338405 3773442065578880560938451)
        ·
          refine ⟨5660163098368320841407677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3773442065578880560938451 5660163098368320841407677)
          ·
            refine ⟨2122561161888120315527879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5660163098368320841407677 2122561161888120315527879)
            ·
              refine ⟨3183841742832180473291819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122561161888120315527879 3183841742832180473291819)
              ·
                refine ⟨4775762614248270709937729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3183841742832180473291819 4775762614248270709937729)
                ·
                  refine ⟨3581821960686203032453297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4775762614248270709937729 3581821960686203032453297)
                  ·
                    refine ⟨2686366470514652274339973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3581821960686203032453297 2686366470514652274339973)
                    ·
                      refine ⟨503693713221497301438745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2686366470514652274339973 503693713221497301438745)
                      ·
                        rfl

theorem cell23_980940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_980940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_980940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_980940 prefixEnd_980940 := by exact prefixLift 980940
  have htrace : WordTrace (prefixWord ++ tailWord_980940) baseStart_980940 baseEnd_980940 := by
    simpa [prefixWord, tailWord_980940, baseEnd_980940] using wordTrace_append hprefix tailTrace_980940
  have hstable : (prefixWord ++ tailWord_980940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980940).length < 2 ^ (prefixWord ++ tailWord_980940).sum := by decide
  have hdescent : baseEnd_980940 < baseStart_980940 := by decide
  rcases family_descends (prefixWord ++ tailWord_980940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981023 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 10]
def baseStart_981023 : Nat := 118140960795 + 981023 * 2 ^ 59
def prefixEnd_981023 : Nat := 4983230072969 + 3 ^ 40 * 981023 * 2
def baseEnd_981023 : Nat := 55970703568424497411207

theorem tailTrace_981023 : CollatzResearch.WordTrace tailWord_981023 prefixEnd_981023 55970703568424497411207 := by
  unfold tailWord_981023
  simp only [CollatzResearch.WordTrace]
  refine ⟨35780848324928691234539723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23853898883285794156359815 35780848324928691234539723)
  ·
    refine ⟨53671272487393036851809585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35780848324928691234539723 53671272487393036851809585)
    ·
      refine ⟨40253454365544777638857189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53671272487393036851809585 40253454365544777638857189)
      ·
        refine ⟨7547522693539645807285723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40253454365544777638857189 7547522693539645807285723)
        ·
          refine ⟨11321284040309468710928585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7547522693539645807285723 11321284040309468710928585)
          ·
            refine ⟨8490963030232101533196439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11321284040309468710928585 8490963030232101533196439)
            ·
              refine ⟨12736444545348152299794659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8490963030232101533196439 12736444545348152299794659)
              ·
                refine ⟨19104666818022228449691989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12736444545348152299794659 19104666818022228449691989)
                ·
                  refine ⟨55970703568424497411207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 19104666818022228449691989 55970703568424497411207)
                  ·
                    rfl

theorem cell23_981023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 10].length) (baseStart_981023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981023 prefixEnd_981023 := by exact prefixLift 981023
  have htrace : WordTrace (prefixWord ++ tailWord_981023) baseStart_981023 baseEnd_981023 := by
    simpa [prefixWord, tailWord_981023, baseEnd_981023] using wordTrace_append hprefix tailTrace_981023
  have hstable : (prefixWord ++ tailWord_981023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981023).length < 2 ^ (prefixWord ++ tailWord_981023).sum := by decide
  have hdescent : baseEnd_981023 < baseStart_981023 := by decide
  rcases family_descends (prefixWord ++ tailWord_981023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981043 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 8]
def baseStart_981043 : Nat := 118140960795 + 981043 * 2 ^ 59
def prefixEnd_981043 : Nat := 4983230072969 + 3 ^ 40 * 981043 * 2
def baseEnd_981043 : Nat := 503746601728910398450771

theorem tailTrace_981043 : CollatzResearch.WordTrace tailWord_981043 prefixEnd_981043 503746601728910398450771 := by
  unfold tailWord_981043
  simp only [CollatzResearch.WordTrace]
  refine ⟨35781577784856234650267783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23854385189904156433511855 35781577784856234650267783)
  ·
    refine ⟨53672366677284351975401675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35781577784856234650267783 53672366677284351975401675)
    ·
      refine ⟨80508550015926527963102513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53672366677284351975401675 80508550015926527963102513)
      ·
        refine ⟨60381412511944895972326885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80508550015926527963102513 60381412511944895972326885)
        ·
          refine ⟨11321514845989667994811291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60381412511944895972326885 11321514845989667994811291)
          ·
            refine ⟨16982272268984501992216937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11321514845989667994811291 16982272268984501992216937)
            ·
              refine ⟨12736704201738376494162703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16982272268984501992216937 12736704201738376494162703)
              ·
                refine ⟨19105056302607564741244055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12736704201738376494162703 19105056302607564741244055)
                ·
                  refine ⟨28657584453911347111866083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19105056302607564741244055 28657584453911347111866083)
                  ·
                    refine ⟨42986376680867020667799125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28657584453911347111866083 42986376680867020667799125)
                    ·
                      refine ⟨503746601728910398450771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 42986376680867020667799125 503746601728910398450771)
                      ·
                        rfl

theorem cell23_981043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_981043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981043 prefixEnd_981043 := by exact prefixLift 981043
  have htrace : WordTrace (prefixWord ++ tailWord_981043) baseStart_981043 baseEnd_981043 := by
    simpa [prefixWord, tailWord_981043, baseEnd_981043] using wordTrace_append hprefix tailTrace_981043
  have hstable : (prefixWord ++ tailWord_981043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981043).length < 2 ^ (prefixWord ++ tailWord_981043).sum := by decide
  have hdescent : baseEnd_981043 < baseStart_981043 := by decide
  rcases family_descends (prefixWord ++ tailWord_981043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981057 : List Nat := [1, 2, 5, 1, 2, 2, 1, 3, 6]
def baseStart_981057 : Nat := 118140960795 + 981057 * 2 ^ 59
def prefixEnd_981057 : Nat := 4983230072969 + 3 ^ 40 * 981057 * 2
def baseEnd_981057 : Nat := 55972643384230371519523

theorem tailTrace_981057 : CollatzResearch.WordTrace tailWord_981057 prefixEnd_981057 55972643384230371519523 := by
  unfold tailWord_981057
  simp only [CollatzResearch.WordTrace]
  refine ⟨35782088406805515041277425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23854725604537010027518283 35782088406805515041277425)
  ·
    refine ⟨26836566305104136280958069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35782088406805515041277425 26836566305104136280958069)
    ·
      refine ⟨2515928091103512776339819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26836566305104136280958069 2515928091103512776339819)
      ·
        refine ⟨3773892136655269164509729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2515928091103512776339819 3773892136655269164509729)
        ·
          refine ⟨2830419102491451873382297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3773892136655269164509729 2830419102491451873382297)
          ·
            refine ⟨2122814326868588905036723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2830419102491451873382297 2122814326868588905036723)
            ·
              refine ⟨3184221490302883357555085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122814326868588905036723 3184221490302883357555085)
              ·
                refine ⟨1194083058863581259083157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3184221490302883357555085 1194083058863581259083157)
                ·
                  refine ⟨55972643384230371519523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1194083058863581259083157 55972643384230371519523)
                  ·
                    rfl

theorem cell23_981057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 6].length) (baseStart_981057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981057 prefixEnd_981057 := by exact prefixLift 981057
  have htrace : WordTrace (prefixWord ++ tailWord_981057) baseStart_981057 baseEnd_981057 := by
    simpa [prefixWord, tailWord_981057, baseEnd_981057] using wordTrace_append hprefix tailTrace_981057
  have hstable : (prefixWord ++ tailWord_981057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981057).length < 2 ^ (prefixWord ++ tailWord_981057).sum := by decide
  have hdescent : baseEnd_981057 < baseStart_981057 := by decide
  rcases family_descends (prefixWord ++ tailWord_981057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981101 : List Nat := [1, 5, 1, 1, 2, 1, 3, 4, 1, 1, 3]
def baseStart_981101 : Nat := 118140960795 + 981101 * 2 ^ 59
def prefixEnd_981101 : Nat := 4983230072969 + 3 ^ 40 * 981101 * 2
def baseEnd_981101 : Nat := 503776383606871171525505

theorem tailTrace_981101 : CollatzResearch.WordTrace tailWord_981101 prefixEnd_981101 503776383606871171525505 := by
  unfold tailWord_981101
  simp only [CollatzResearch.WordTrace]
  refine ⟨35783693218646110555879157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23855795479097407037252771 35783693218646110555879157)
  ·
    refine ⟨3354721239248072864613671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35783693218646110555879157 3354721239248072864613671)
    ·
      refine ⟨5032081858872109296920507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3354721239248072864613671 5032081858872109296920507)
      ·
        refine ⟨7548122788308163945380761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5032081858872109296920507 7548122788308163945380761)
        ·
          refine ⟨5661092091231122959035571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7548122788308163945380761 5661092091231122959035571)
          ·
            refine ⟨8491638136846684438553357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5661092091231122959035571 8491638136846684438553357)
            ·
              refine ⟨3184364301317506664457509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8491638136846684438553357 3184364301317506664457509)
              ·
                refine ⟨597068306497032499585783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3184364301317506664457509 597068306497032499585783)
                ·
                  refine ⟨895602459745548749378675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597068306497032499585783 895602459745548749378675)
                  ·
                    refine ⟨1343403689618323124068013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 895602459745548749378675 1343403689618323124068013)
                    ·
                      refine ⟨503776383606871171525505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1343403689618323124068013 503776383606871171525505)
                      ·
                        rfl

theorem cell23_981101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_981101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981101 prefixEnd_981101 := by exact prefixLift 981101
  have htrace : WordTrace (prefixWord ++ tailWord_981101) baseStart_981101 baseEnd_981101 := by
    simpa [prefixWord, tailWord_981101, baseEnd_981101] using wordTrace_append hprefix tailTrace_981101
  have hstable : (prefixWord ++ tailWord_981101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981101).length < 2 ^ (prefixWord ++ tailWord_981101).sum := by decide
  have hdescent : baseEnd_981101 < baseStart_981101 := by decide
  rcases family_descends (prefixWord ++ tailWord_981101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981117 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_981117 : Nat := 118140960795 + 981117 * 2 ^ 59
def prefixEnd_981117 : Nat := 4983230072969 + 3 ^ 40 * 981117 * 2
def baseEnd_981117 : Nat := 167928199765781036308477

theorem tailTrace_981117 : CollatzResearch.WordTrace tailWord_981117 prefixEnd_981117 167928199765781036308477 := by
  unfold tailWord_981117
  simp only [CollatzResearch.WordTrace]
  refine ⟨35784276786588145288461605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23856184524392096858974403 35784276786588145288461605)
  ·
    refine ⟨6709551897485277241586551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35784276786588145288461605 6709551897485277241586551)
    ·
      refine ⟨10064327846227915862379827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6709551897485277241586551 10064327846227915862379827)
      ·
        refine ⟨15096491769341873793569741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10064327846227915862379827 15096491769341873793569741)
        ·
          refine ⟨5661184413503202672588653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15096491769341873793569741 5661184413503202672588653)
          ·
            refine ⟨2122944155063701002220745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5661184413503202672588653 2122944155063701002220745)
            ·
              refine ⟨1592208116297775751665559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2122944155063701002220745 1592208116297775751665559)
              ·
                refine ⟨2388312174446663627498339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592208116297775751665559 2388312174446663627498339)
                ·
                  refine ⟨3582468261669995441247509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388312174446663627498339 3582468261669995441247509)
                  ·
                    refine ⟨167928199765781036308477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3582468261669995441247509 167928199765781036308477)
                    ·
                      rfl

theorem cell23_981117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_981117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981117 prefixEnd_981117 := by exact prefixLift 981117
  have htrace : WordTrace (prefixWord ++ tailWord_981117) baseStart_981117 baseEnd_981117 := by
    simpa [prefixWord, tailWord_981117, baseEnd_981117] using wordTrace_append hprefix tailTrace_981117
  have hstable : (prefixWord ++ tailWord_981117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981117).length < 2 ^ (prefixWord ++ tailWord_981117).sum := by decide
  have hdescent : baseEnd_981117 < baseStart_981117 := by decide
  rcases family_descends (prefixWord ++ tailWord_981117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981127 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_981127 : Nat := 118140960795 + 981127 * 2 ^ 59
def prefixEnd_981127 : Nat := 4983230072969 + 3 ^ 40 * 981127 * 2
def baseEnd_981127 : Nat := 503789734103888069800385

theorem tailTrace_981127 : CollatzResearch.WordTrace tailWord_981127 prefixEnd_981127 503789734103888069800385 := by
  unfold tailWord_981127
  simp only [CollatzResearch.WordTrace]
  refine ⟨35784641516551916996325635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23856427677701277997550423 35784641516551916996325635)
  ·
    refine ⟨53676962274827875494488453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35784641516551916996325635 53676962274827875494488453)
    ·
      refine ⟨10064430426530226655216585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53676962274827875494488453 10064430426530226655216585)
      ·
        refine ⟨7548322819897669991412439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10064430426530226655216585 7548322819897669991412439)
        ·
          refine ⟨11322484229846504987118659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7548322819897669991412439 11322484229846504987118659)
          ·
            refine ⟨16983726344769757480677989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11322484229846504987118659 16983726344769757480677989)
            ·
              refine ⟨3184448689644329527627123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16983726344769757480677989 3184448689644329527627123)
              ·
                refine ⟨4776673034466494291440685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3184448689644329527627123 4776673034466494291440685)
                ·
                  refine ⟨1791252387924935359290257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4776673034466494291440685 1791252387924935359290257)
                  ·
                    refine ⟨1343439290943701519467693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1791252387924935359290257 1343439290943701519467693)
                    ·
                      refine ⟨503789734103888069800385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1343439290943701519467693 503789734103888069800385)
                      ·
                        rfl

theorem cell23_981127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_981127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981127 prefixEnd_981127 := by exact prefixLift 981127
  have htrace : WordTrace (prefixWord ++ tailWord_981127) baseStart_981127 baseEnd_981127 := by
    simpa [prefixWord, tailWord_981127, baseEnd_981127] using wordTrace_append hprefix tailTrace_981127
  have hstable : (prefixWord ++ tailWord_981127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981127).length < 2 ^ (prefixWord ++ tailWord_981127).sum := by decide
  have hdescent : baseEnd_981127 < baseStart_981127 := by decide
  rcases family_descends (prefixWord ++ tailWord_981127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981142 : List Nat := [5, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_981142 : Nat := 118140960795 + 981142 * 2 ^ 59
def prefixEnd_981142 : Nat := 4983230072969 + 3 ^ 40 * 981142 * 2
def baseEnd_981142 : Nat := 55977492923745056790313

theorem tailTrace_981142 : CollatzResearch.WordTrace tailWord_981142 prefixEnd_981142 55977492923745056790313 := by
  unfold tailWord_981142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2236574288218598409882605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23856792407665049705414453 2236574288218598409882605)
  ·
    refine ⟨838715358081974403705977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2236574288218598409882605 838715358081974403705977)
    ·
      refine ⟨629036518561480802779483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 838715358081974403705977 629036518561480802779483)
      ·
        refine ⟨943554777842221204169225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629036518561480802779483 943554777842221204169225)
        ·
          refine ⟨707666083381665903126919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 943554777842221204169225 707666083381665903126919)
          ·
            refine ⟨1061499125072498854690379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707666083381665903126919 1061499125072498854690379)
            ·
              refine ⟨1592248687608748282035569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061499125072498854690379 1592248687608748282035569)
              ·
                refine ⟨1194186515706561211526677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1592248687608748282035569 1194186515706561211526677)
                ·
                  refine ⟨55977492923745056790313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1194186515706561211526677 55977492923745056790313)
                  ·
                    rfl

theorem cell23_981142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_981142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981142 prefixEnd_981142 := by exact prefixLift 981142
  have htrace : WordTrace (prefixWord ++ tailWord_981142) baseStart_981142 baseEnd_981142 := by
    simpa [prefixWord, tailWord_981142, baseEnd_981142] using wordTrace_append hprefix tailTrace_981142
  have hstable : (prefixWord ++ tailWord_981142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981142).length < 2 ^ (prefixWord ++ tailWord_981142).sum := by decide
  have hdescent : baseEnd_981142 < baseStart_981142 := by decide
  rcases family_descends (prefixWord ++ tailWord_981142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981151 : List Nat := [1, 1, 2, 6, 1, 3, 1, 2, 2, 4]
def baseStart_981151 : Nat := 118140960795 + 981151 * 2 ^ 59
def prefixEnd_981151 : Nat := 4983230072969 + 3 ^ 40 * 981151 * 2
def baseEnd_981151 : Nat := 167934019213198658633425

theorem tailTrace_981151 : CollatzResearch.WordTrace tailWord_981151 prefixEnd_981151 167934019213198658633425 := by
  unfold tailWord_981151
  simp only [CollatzResearch.WordTrace]
  refine ⟨35785516868464969095199307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23857011245643312730132871 35785516868464969095199307)
  ·
    refine ⟨53678275302697453642798961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35785516868464969095199307 53678275302697453642798961)
    ·
      refine ⟨40258706477023090232099221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53678275302697453642798961 40258706477023090232099221)
      ·
        refine ⟨1887126866110457354629651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40258706477023090232099221 1887126866110457354629651)
        ·
          refine ⟨2830690299165686031944477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887126866110457354629651 2830690299165686031944477)
          ·
            refine ⟨1061508862187132261979179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2830690299165686031944477 1061508862187132261979179)
            ·
              refine ⟨1592263293280698392968769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061508862187132261979179 1592263293280698392968769)
              ·
                refine ⟨1194197469960523794726577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1592263293280698392968769 1194197469960523794726577)
                ·
                  refine ⟨895648102470392846044933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1194197469960523794726577 895648102470392846044933)
                  ·
                    refine ⟨167934019213198658633425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 895648102470392846044933 167934019213198658633425)
                    ·
                      rfl

theorem cell23_981151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 4].length) (baseStart_981151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981151 prefixEnd_981151 := by exact prefixLift 981151
  have htrace : WordTrace (prefixWord ++ tailWord_981151) baseStart_981151 baseEnd_981151 := by
    simpa [prefixWord, tailWord_981151, baseEnd_981151] using wordTrace_append hprefix tailTrace_981151
  have hstable : (prefixWord ++ tailWord_981151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981151).length < 2 ^ (prefixWord ++ tailWord_981151).sum := by decide
  have hdescent : baseEnd_981151 < baseStart_981151 := by decide
  rcases family_descends (prefixWord ++ tailWord_981151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981217 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_981217 : Nat := 118140960795 + 981217 * 2 ^ 59
def prefixEnd_981217 : Nat := 4983230072969 + 3 ^ 40 * 981217 * 2
def baseEnd_981217 : Nat := 503835947362792717674971

theorem tailTrace_981217 : CollatzResearch.WordTrace tailWord_981217 prefixEnd_981217 503835947362792717674971 := by
  unfold tailWord_981217
  simp only [CollatzResearch.WordTrace]
  refine ⟨35787924086225862367101905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23858616057483908244734603 35787924086225862367101905)
  ·
    refine ⟨26840943064669396775326429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35787924086225862367101905 26840943064669396775326429)
    ·
      refine ⟨10065353649251023790747411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26840943064669396775326429 10065353649251023790747411)
      ·
        refine ⟨15098030473876535686121117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10065353649251023790747411 15098030473876535686121117)
        ·
          refine ⟨5661761427703700882295419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15098030473876535686121117 5661761427703700882295419)
          ·
            refine ⟨8492642141555551323443129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5661761427703700882295419 8492642141555551323443129)
            ·
              refine ⟨6369481606166663492582347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8492642141555551323443129 6369481606166663492582347)
              ·
                refine ⟨9554222409249995238873521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369481606166663492582347 9554222409249995238873521)
                ·
                  refine ⟨7165666806937496429155141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9554222409249995238873521 7165666806937496429155141)
                  ·
                    refine ⟨1343562526300780580466589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7165666806937496429155141 1343562526300780580466589)
                    ·
                      refine ⟨503835947362792717674971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1343562526300780580466589 503835947362792717674971)
                      ·
                        rfl

theorem cell23_981217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_981217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981217 prefixEnd_981217 := by exact prefixLift 981217
  have htrace : WordTrace (prefixWord ++ tailWord_981217) baseStart_981217 baseEnd_981217 := by
    simpa [prefixWord, tailWord_981217, baseEnd_981217] using wordTrace_append hprefix tailTrace_981217
  have hstable : (prefixWord ++ tailWord_981217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981217).length < 2 ^ (prefixWord ++ tailWord_981217).sum := by decide
  have hdescent : baseEnd_981217 < baseStart_981217 := by decide
  rcases family_descends (prefixWord ++ tailWord_981217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981240 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_981240 : Nat := 118140960795 + 981240 * 2 ^ 59
def prefixEnd_981240 : Nat := 4983230072969 + 3 ^ 40 * 981240 * 2
def baseEnd_981240 : Nat := 503847757417846127687365

theorem tailTrace_981240 : CollatzResearch.WordTrace tailWord_981240 prefixEnd_981240 503847757417846127687365 := by
  unfold tailWord_981240
  simp only [CollatzResearch.WordTrace]
  refine ⟨17894381482571268647594587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23859175310095024863459449 17894381482571268647594587)
  ·
    refine ⟨26841572223856902971391881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17894381482571268647594587 26841572223856902971391881)
    ·
      refine ⟨20131179167892677228543911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26841572223856902971391881 20131179167892677228543911)
      ·
        refine ⟨30196768751839015842815867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20131179167892677228543911 30196768751839015842815867)
        ·
          refine ⟨45295153127758523764223801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30196768751839015842815867 45295153127758523764223801)
          ·
            refine ⟨33971364845818892823167851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45295153127758523764223801 33971364845818892823167851)
            ·
              refine ⟨50957047268728339234751777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33971364845818892823167851 50957047268728339234751777)
              ·
                refine ⟨38217785451546254426063833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50957047268728339234751777 38217785451546254426063833)
                ·
                  refine ⟨28663339088659690819547875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38217785451546254426063833 28663339088659690819547875)
                  ·
                    refine ⟨42995008632989536229321813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28663339088659690819547875 42995008632989536229321813)
                    ·
                      refine ⟨503847757417846127687365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 42995008632989536229321813 503847757417846127687365)
                      ·
                        rfl

theorem cell23_981240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_981240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981240 prefixEnd_981240 := by exact prefixLift 981240
  have htrace : WordTrace (prefixWord ++ tailWord_981240) baseStart_981240 baseEnd_981240 := by
    simpa [prefixWord, tailWord_981240, baseEnd_981240] using wordTrace_append hprefix tailTrace_981240
  have hstable : (prefixWord ++ tailWord_981240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981240).length < 2 ^ (prefixWord ++ tailWord_981240).sum := by decide
  have hdescent : baseEnd_981240 < baseStart_981240 := by decide
  rcases family_descends (prefixWord ++ tailWord_981240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981271 : List Nat := [1, 1, 3, 4, 1, 2, 4, 2, 5]
def baseStart_981271 : Nat := 118140960795 + 981271 * 2 ^ 59
def prefixEnd_981271 : Nat := 4983230072969 + 3 ^ 40 * 981271 * 2
def baseEnd_981271 : Nat := 55984852813126167377747

theorem tailTrace_981271 : CollatzResearch.WordTrace tailWord_981271 prefixEnd_981271 55984852813126167377747 := by
  unfold tailWord_981271
  simp only [CollatzResearch.WordTrace]
  refine ⟨35789893628030229589567667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23859929085353486393045111 35789893628030229589567667)
  ·
    refine ⟨53684840442045344384351501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35789893628030229589567667 53684840442045344384351501)
    ·
      refine ⟨20131815165767004144131813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53684840442045344384351501 20131815165767004144131813)
      ·
        refine ⟨3774715343581313277024715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20131815165767004144131813 3774715343581313277024715)
        ·
          refine ⟨5662073015371969915537073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3774715343581313277024715 5662073015371969915537073)
          ·
            refine ⟨4246554761528977436652805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5662073015371969915537073 4246554761528977436652805)
            ·
              refine ⟨796229017786683269372401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4246554761528977436652805 796229017786683269372401)
              ·
                refine ⟨597171763340012452029301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796229017786683269372401 597171763340012452029301)
                ·
                  refine ⟨55984852813126167377747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 597171763340012452029301 55984852813126167377747)
                  ·
                    rfl

theorem cell23_981271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 5].length) (baseStart_981271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981271 prefixEnd_981271 := by exact prefixLift 981271
  have htrace : WordTrace (prefixWord ++ tailWord_981271) baseStart_981271 baseEnd_981271 := by
    simpa [prefixWord, tailWord_981271, baseEnd_981271] using wordTrace_append hprefix tailTrace_981271
  have hstable : (prefixWord ++ tailWord_981271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981271).length < 2 ^ (prefixWord ++ tailWord_981271).sum := by decide
  have hdescent : baseEnd_981271 < baseStart_981271 := by decide
  rcases family_descends (prefixWord ++ tailWord_981271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981304 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 2, 1, 4]
def baseStart_981304 : Nat := 118140960795 + 981304 * 2 ^ 59
def prefixEnd_981304 : Nat := 4983230072969 + 3 ^ 40 * 981304 * 2
def baseEnd_981304 : Nat := 503880620179733877287071

theorem tailTrace_981304 : CollatzResearch.WordTrace tailWord_981304 prefixEnd_981304 503880620179733877287071 := by
  unfold tailWord_981304
  simp only [CollatzResearch.WordTrace]
  refine ⟨17895548618455338112759483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23860731491273784150345977 17895548618455338112759483)
  ·
    refine ⟨26843322927683007169139225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17895548618455338112759483 26843322927683007169139225)
    ·
      refine ⟨20132492195762255376854419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26843322927683007169139225 20132492195762255376854419)
      ·
        refine ⟨30198738293643383065281629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20132492195762255376854419 30198738293643383065281629)
        ·
          refine ⟨11324526860116268649480611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30198738293643383065281629 11324526860116268649480611)
          ·
            refine ⟨16986790290174402974220917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11324526860116268649480611 16986790290174402974220917)
            ·
              refine ⟨1592511589703850278833211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16986790290174402974220917 1592511589703850278833211)
              ·
                refine ⟨2388767384555775418249817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592511589703850278833211 2388767384555775418249817)
                ·
                  refine ⟨1791575538416831563687363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2388767384555775418249817 1791575538416831563687363)
                  ·
                    refine ⟨2687363307625247345531045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1791575538416831563687363 2687363307625247345531045)
                    ·
                      refine ⟨503880620179733877287071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2687363307625247345531045 503880620179733877287071)
                      ·
                        rfl

theorem cell23_981304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_981304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981304 prefixEnd_981304 := by exact prefixLift 981304
  have htrace : WordTrace (prefixWord ++ tailWord_981304) baseStart_981304 baseEnd_981304 := by
    simpa [prefixWord, tailWord_981304, baseEnd_981304] using wordTrace_append hprefix tailTrace_981304
  have hstable : (prefixWord ++ tailWord_981304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981304).length < 2 ^ (prefixWord ++ tailWord_981304).sum := by decide
  have hdescent : baseEnd_981304 < baseStart_981304 := by decide
  rcases family_descends (prefixWord ++ tailWord_981304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981324 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 4, 2, 3]
def baseStart_981324 : Nat := 118140960795 + 981324 * 2 ^ 59
def prefixEnd_981324 : Nat := 4983230072969 + 3 ^ 40 * 981324 * 2
def baseEnd_981324 : Nat := 503890889792823799036979

theorem tailTrace_981324 : CollatzResearch.WordTrace tailWord_981324 prefixEnd_981324 503890889792823799036979 := by
  unfold tailWord_981324
  simp only [CollatzResearch.WordTrace]
  refine ⟨17895913348419109820623513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23861217797892146427498017 17895913348419109820623513)
  ·
    refine ⟨13421935011314332365467635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17895913348419109820623513 13421935011314332365467635)
    ·
      refine ⟨20132902516971498548201453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13421935011314332365467635 20132902516971498548201453)
      ·
        refine ⟨7549838443864311955575545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20132902516971498548201453 7549838443864311955575545)
        ·
          refine ⟨5662378832898233966681659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7549838443864311955575545 5662378832898233966681659)
          ·
            refine ⟨8493568249347350950022489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5662378832898233966681659 8493568249347350950022489)
            ·
              refine ⟨6370176187010513212516867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8493568249347350950022489 6370176187010513212516867)
              ·
                refine ⟨9555264280515769818775301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6370176187010513212516867 9555264280515769818775301)
                ·
                  refine ⟨1791612052596706841020369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9555264280515769818775301 1791612052596706841020369)
                  ·
                    refine ⟨1343709039447530130765277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1791612052596706841020369 1343709039447530130765277)
                    ·
                      refine ⟨503890889792823799036979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1343709039447530130765277 503890889792823799036979)
                      ·
                        rfl

theorem cell23_981324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_981324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981324 prefixEnd_981324 := by exact prefixLift 981324
  have htrace : WordTrace (prefixWord ++ tailWord_981324) baseStart_981324 baseEnd_981324 := by
    simpa [prefixWord, tailWord_981324, baseEnd_981324] using wordTrace_append hprefix tailTrace_981324
  have hstable : (prefixWord ++ tailWord_981324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981324).length < 2 ^ (prefixWord ++ tailWord_981324).sum := by decide
  have hdescent : baseEnd_981324 < baseStart_981324 := by decide
  rcases family_descends (prefixWord ++ tailWord_981324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981327 : List Nat := [1, 1, 2, 1, 1, 2, 1, 8, 6]
def baseStart_981327 : Nat := 118140960795 + 981327 * 2 ^ 59
def prefixEnd_981327 : Nat := 4983230072969 + 3 ^ 40 * 981327 * 2
def baseEnd_981327 : Nat := 55988047803865254144385

theorem tailTrace_981327 : CollatzResearch.WordTrace tailWord_981327 prefixEnd_981327 55988047803865254144385 := by
  unfold tailWord_981327
  simp only [CollatzResearch.WordTrace]
  refine ⟨35791936115827351153606235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23861290743884900769070823 35791936115827351153606235)
  ·
    refine ⟨53687904173741026730409353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35791936115827351153606235 53687904173741026730409353)
    ·
      refine ⟨40265928130305770047807015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53687904173741026730409353 40265928130305770047807015)
      ·
        refine ⟨60398892195458655071710523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40265928130305770047807015 60398892195458655071710523)
        ·
          refine ⟨90598338293187982607565785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60398892195458655071710523 90598338293187982607565785)
          ·
            refine ⟨67948753719890986955674339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90598338293187982607565785 67948753719890986955674339)
            ·
              refine ⟨101923130579836480433511509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67948753719890986955674339 101923130579836480433511509)
              ·
                refine ⟨1194411686482458755080213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 101923130579836480433511509 1194411686482458755080213)
                ·
                  refine ⟨55988047803865254144385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1194411686482458755080213 55988047803865254144385)
                  ·
                    rfl

theorem cell23_981327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 6].length) (baseStart_981327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981327 prefixEnd_981327 := by exact prefixLift 981327
  have htrace : WordTrace (prefixWord ++ tailWord_981327) baseStart_981327 baseEnd_981327 := by
    simpa [prefixWord, tailWord_981327, baseEnd_981327] using wordTrace_append hprefix tailTrace_981327
  have hstable : (prefixWord ++ tailWord_981327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981327).length < 2 ^ (prefixWord ++ tailWord_981327).sum := by decide
  have hdescent : baseEnd_981327 < baseStart_981327 := by decide
  rcases family_descends (prefixWord ++ tailWord_981327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981347 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 6]
def baseStart_981347 : Nat := 118140960795 + 981347 * 2 ^ 59
def prefixEnd_981347 : Nat := 4983230072969 + 3 ^ 40 * 981347 * 2
def baseEnd_981347 : Nat := 503902699847877209049373

theorem tailTrace_981347 : CollatzResearch.WordTrace tailWord_981347 prefixEnd_981347 503902699847877209049373 := by
  unfold tailWord_981347
  simp only [CollatzResearch.WordTrace]
  refine ⟨35792665575754894569334295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23861777050503263046222863 35792665575754894569334295)
  ·
    refine ⟨53688998363632341854001443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35792665575754894569334295 53688998363632341854001443)
    ·
      refine ⟨80533497545448512781002165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53688998363632341854001443 80533497545448512781002165)
      ·
        refine ⟨7550015394885798073218953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80533497545448512781002165 7550015394885798073218953)
        ·
          refine ⟨5662511546164348554914215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7550015394885798073218953 5662511546164348554914215)
          ·
            refine ⟨8493767319246522832371323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5662511546164348554914215 8493767319246522832371323)
            ·
              refine ⟨12740650978869784248556985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8493767319246522832371323 12740650978869784248556985)
              ·
                refine ⟨9555488234152338186417739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12740650978869784248556985 9555488234152338186417739)
                ·
                  refine ⟨14333232351228507279626609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9555488234152338186417739 14333232351228507279626609)
                  ·
                    refine ⟨10749924263421380459719957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14333232351228507279626609 10749924263421380459719957)
                    ·
                      refine ⟨503902699847877209049373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10749924263421380459719957 503902699847877209049373)
                      ·
                        rfl

theorem cell23_981347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_981347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981347 prefixEnd_981347 := by exact prefixLift 981347
  have htrace : WordTrace (prefixWord ++ tailWord_981347) baseStart_981347 baseEnd_981347 := by
    simpa [prefixWord, tailWord_981347, baseEnd_981347] using wordTrace_append hprefix tailTrace_981347
  have hstable : (prefixWord ++ tailWord_981347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981347).length < 2 ^ (prefixWord ++ tailWord_981347).sum := by decide
  have hdescent : baseEnd_981347 < baseStart_981347 := by decide
  rcases family_descends (prefixWord ++ tailWord_981347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981365 : List Nat := [1, 3, 4, 1, 2, 3, 1, 3, 1, 4]
def baseStart_981365 : Nat := 118140960795 + 981365 * 2 ^ 59
def prefixEnd_981365 : Nat := 4983230072969 + 3 ^ 40 * 981365 * 2
def baseEnd_981365 : Nat := 167970647499886046208097

theorem tailTrace_981365 : CollatzResearch.WordTrace tailWord_981365 prefixEnd_981365 167970647499886046208097 := by
  unfold tailWord_981365
  simp only [CollatzResearch.WordTrace]
  refine ⟨35793322089689683643489549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23862214726459789095659699 35793322089689683643489549)
  ·
    refine ⟨13422495783633631366308581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35793322089689683643489549 13422495783633631366308581)
    ·
      refine ⟨2516717959431305881182859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13422495783633631366308581 2516717959431305881182859)
      ·
        refine ⟨3775076939146958821774289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2516717959431305881182859 3775076939146958821774289)
        ·
          refine ⟨2831307704360219116330717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3775076939146958821774289 2831307704360219116330717)
          ·
            refine ⟨1061740389135082168624019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2831307704360219116330717 1061740389135082168624019)
            ·
              refine ⟨1592610583702623252936029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061740389135082168624019 1592610583702623252936029)
              ·
                refine ⟨597228968888483719851011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1592610583702623252936029 597228968888483719851011)
                ·
                  refine ⟨895843453332725579776517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597228968888483719851011 895843453332725579776517)
                  ·
                    refine ⟨167970647499886046208097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 895843453332725579776517 167970647499886046208097)
                    ·
                      rfl

theorem cell23_981365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_981365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981365 prefixEnd_981365 := by exact prefixLift 981365
  have htrace : WordTrace (prefixWord ++ tailWord_981365) baseStart_981365 baseEnd_981365 := by
    simpa [prefixWord, tailWord_981365, baseEnd_981365] using wordTrace_append hprefix tailTrace_981365
  have hstable : (prefixWord ++ tailWord_981365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981365).length < 2 ^ (prefixWord ++ tailWord_981365).sum := by decide
  have hdescent : baseEnd_981365 < baseStart_981365 := by decide
  rcases family_descends (prefixWord ++ tailWord_981365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981388 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 3, 1, 3]
def baseStart_981388 : Nat := 118140960795 + 981388 * 2 ^ 59
def prefixEnd_981388 : Nat := 4983230072969 + 3 ^ 40 * 981388 * 2
def baseEnd_981388 : Nat := 503923752554711548636685

theorem tailTrace_981388 : CollatzResearch.WordTrace tailWord_981388 prefixEnd_981388 503923752554711548636685 := by
  unfold tailWord_981388
  simp only [CollatzResearch.WordTrace]
  refine ⟨17897080484303179285788409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23862773979070905714384545 17897080484303179285788409)
  ·
    refine ⟨13422810363227384464341307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17897080484303179285788409 13422810363227384464341307)
    ·
      refine ⟨20134215544841076696511961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13422810363227384464341307 20134215544841076696511961)
      ·
        refine ⟨15100661658630807522383971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20134215544841076696511961 15100661658630807522383971)
        ·
          refine ⟨22650992487946211283575957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15100661658630807522383971 22650992487946211283575957)
          ·
            refine ⟨1061765272872478653917623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22650992487946211283575957 1061765272872478653917623)
            ·
              refine ⟨1592647909308717980876435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061765272872478653917623 1592647909308717980876435)
              ·
                refine ⟨2388971863963076971314653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592647909308717980876435 2388971863963076971314653)
                ·
                  refine ⟨895864448986153864242995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2388971863963076971314653 895864448986153864242995)
                  ·
                    refine ⟨1343796673479230796364493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 895864448986153864242995 1343796673479230796364493)
                    ·
                      refine ⟨503923752554711548636685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1343796673479230796364493 503923752554711548636685)
                      ·
                        rfl

theorem cell23_981388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_981388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981388 prefixEnd_981388 := by exact prefixLift 981388
  have htrace : WordTrace (prefixWord ++ tailWord_981388) baseStart_981388 baseEnd_981388 := by
    simpa [prefixWord, tailWord_981388, baseEnd_981388] using wordTrace_append hprefix tailTrace_981388
  have hstable : (prefixWord ++ tailWord_981388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981388).length < 2 ^ (prefixWord ++ tailWord_981388).sum := by decide
  have hdescent : baseEnd_981388 < baseStart_981388 := by decide
  rcases family_descends (prefixWord ++ tailWord_981388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981411 : List Nat := [1, 1, 1, 4, 1, 4, 3, 2, 1, 1, 4]
def baseStart_981411 : Nat := 118140960795 + 981411 * 2 ^ 59
def prefixEnd_981411 : Nat := 4983230072969 + 3 ^ 40 * 981411 * 2
def baseEnd_981411 : Nat := 503935562609764958649079

theorem tailTrace_981411 : CollatzResearch.WordTrace tailWord_981411 prefixEnd_981411 503935562609764958649079 := by
  unfold tailWord_981411
  simp only [CollatzResearch.WordTrace]
  refine ⟨35794999847523033499664087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23863333231682022333109391 35794999847523033499664087)
  ·
    refine ⟨53692499771284550249496131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35794999847523033499664087 53692499771284550249496131)
    ·
      refine ⟨80538749656926825374244197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53692499771284550249496131 80538749656926825374244197)
      ·
        refine ⟨15101015560673779757670787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80538749656926825374244197 15101015560673779757670787)
        ·
          refine ⟨22651523341010669636506181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15101015560673779757670787 22651523341010669636506181)
          ·
            refine ⟨4247160626439500556844909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22651523341010669636506181 4247160626439500556844909)
            ·
              refine ⟨1592685234914812708816841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4247160626439500556844909 1592685234914812708816841)
              ·
                refine ⟨1194513926186109531612631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1592685234914812708816841 1194513926186109531612631)
                ·
                  refine ⟨1791770889279164297418947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194513926186109531612631 1791770889279164297418947)
                  ·
                    refine ⟨2687656333918746446128421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1791770889279164297418947 2687656333918746446128421)
                    ·
                      refine ⟨503935562609764958649079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2687656333918746446128421 503935562609764958649079)
                      ·
                        rfl

theorem cell23_981411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_981411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981411 prefixEnd_981411 := by exact prefixLift 981411
  have htrace : WordTrace (prefixWord ++ tailWord_981411) baseStart_981411 baseEnd_981411 := by
    simpa [prefixWord, tailWord_981411, baseEnd_981411] using wordTrace_append hprefix tailTrace_981411
  have hstable : (prefixWord ++ tailWord_981411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981411).length < 2 ^ (prefixWord ++ tailWord_981411).sum := by decide
  have hdescent : baseEnd_981411 < baseStart_981411 := by decide
  rcases family_descends (prefixWord ++ tailWord_981411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981431 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 1, 1, 5]
def baseStart_981431 : Nat := 118140960795 + 981431 * 2 ^ 59
def prefixEnd_981431 : Nat := 4983230072969 + 3 ^ 40 * 981431 * 2
def baseEnd_981431 : Nat := 503945832222854880398987

theorem tailTrace_981431 : CollatzResearch.WordTrace tailWord_981431 prefixEnd_981431 503945832222854880398987 := by
  unfold tailWord_981431
  simp only [CollatzResearch.WordTrace]
  refine ⟨35795729307450576915392147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23863819538300384610261431 35795729307450576915392147)
  ·
    refine ⟨53693593961175865373088221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35795729307450576915392147 53693593961175865373088221)
    ·
      refine ⟨20135097735440949514908083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53693593961175865373088221 20135097735440949514908083)
      ·
        refine ⟨30202646603161424272362125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20135097735440949514908083 30202646603161424272362125)
        ·
          refine ⟨11325992476185534102135797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30202646603161424272362125 11325992476185534102135797)
          ·
            refine ⟨1061811794642393822075231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11325992476185534102135797 1061811794642393822075231)
            ·
              refine ⟨1592717691963590733112847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061811794642393822075231 1592717691963590733112847)
              ·
                refine ⟨2389076537945386099669271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592717691963590733112847 2389076537945386099669271)
                ·
                  refine ⟨3583614806918079149503907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389076537945386099669271 3583614806918079149503907)
                  ·
                    refine ⟨5375422210377118724255861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3583614806918079149503907 5375422210377118724255861)
                    ·
                      refine ⟨503945832222854880398987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5375422210377118724255861 503945832222854880398987)
                      ·
                        rfl

theorem cell23_981431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_981431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981431 prefixEnd_981431 := by exact prefixLift 981431
  have htrace : WordTrace (prefixWord ++ tailWord_981431) baseStart_981431 baseEnd_981431 := by
    simpa [prefixWord, tailWord_981431, baseEnd_981431] using wordTrace_append hprefix tailTrace_981431
  have hstable : (prefixWord ++ tailWord_981431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981431).length < 2 ^ (prefixWord ++ tailWord_981431).sum := by decide
  have hdescent : baseEnd_981431 < baseStart_981431 := by decide
  rcases family_descends (prefixWord ++ tailWord_981431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981461 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_981461 : Nat := 118140960795 + 981461 * 2 ^ 59
def prefixEnd_981461 : Nat := 4983230072969 + 3 ^ 40 * 981461 * 2
def baseEnd_981461 : Nat := 503961236642489763023849

theorem tailTrace_981461 : CollatzResearch.WordTrace tailWord_981461 prefixEnd_981461 503961236642489763023849 := by
  unfold tailWord_981461
  simp only [CollatzResearch.WordTrace]
  refine ⟨35796823497341892038984237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23864548998227928025989491 35796823497341892038984237)
  ·
    refine ⟨13423808811503209514619089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35796823497341892038984237 13423808811503209514619089)
    ·
      refine ⟨10067856608627407135964317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13423808811503209514619089 10067856608627407135964317)
      ·
        refine ⟨3775446228235277675986619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10067856608627407135964317 3775446228235277675986619)
        ·
          refine ⟨5663169342352916513979929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3775446228235277675986619 5663169342352916513979929)
          ·
            refine ⟨4247377006764687385484947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5663169342352916513979929 4247377006764687385484947)
            ·
              refine ⟨6371065510147031078227421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4247377006764687385484947 6371065510147031078227421)
              ·
                refine ⟨2389149566305136654335283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6371065510147031078227421 2389149566305136654335283)
                ·
                  refine ⟨3583724349457704981502925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389149566305136654335283 3583724349457704981502925)
                  ·
                    refine ⟨1343896631046639368063597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3583724349457704981502925 1343896631046639368063597)
                    ·
                      refine ⟨503961236642489763023849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1343896631046639368063597 503961236642489763023849)
                      ·
                        rfl

theorem cell23_981461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_981461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981461 prefixEnd_981461 := by exact prefixLift 981461
  have htrace : WordTrace (prefixWord ++ tailWord_981461) baseStart_981461 baseEnd_981461 := by
    simpa [prefixWord, tailWord_981461, baseEnd_981461] using wordTrace_append hprefix tailTrace_981461
  have hstable : (prefixWord ++ tailWord_981461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981461).length < 2 ^ (prefixWord ++ tailWord_981461).sum := by decide
  have hdescent : baseEnd_981461 < baseStart_981461 := by decide
  rcases family_descends (prefixWord ++ tailWord_981461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981488 : List Nat := [2, 1, 1, 1, 3, 3, 3, 3, 1, 3, 2]
def baseStart_981488 : Nat := 118140960795 + 981488 * 2 ^ 59
def prefixEnd_981488 : Nat := 4983230072969 + 3 ^ 40 * 981488 * 2
def baseEnd_981488 : Nat := 503975100620161157386225

theorem tailTrace_981488 : CollatzResearch.WordTrace tailWord_981488 prefixEnd_981488 503975100620161157386225 := by
  unfold tailWord_981488
  simp only [CollatzResearch.WordTrace]
  refine ⟨17898904134122037825108559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23865205512162717100144745 17898904134122037825108559)
  ·
    refine ⟨26848356201183056737662839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17898904134122037825108559 26848356201183056737662839)
    ·
      refine ⟨40272534301774585106494259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26848356201183056737662839 40272534301774585106494259)
      ·
        refine ⟨60408801452661877659741389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40272534301774585106494259 60408801452661877659741389)
        ·
          refine ⟨22653300544748204122403021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60408801452661877659741389 22653300544748204122403021)
          ·
            refine ⟨8494987704280576545901133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22653300544748204122403021 8494987704280576545901133)
            ·
              refine ⟨3185620389105216204712925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8494987704280576545901133 3185620389105216204712925)
              ·
                refine ⟨1194607645914456076767347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3185620389105216204712925 1194607645914456076767347)
                ·
                  refine ⟨1791911468871684115151021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194607645914456076767347 1791911468871684115151021)
                  ·
                    refine ⟨671966800826881543181633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1791911468871684115151021 671966800826881543181633)
                    ·
                      refine ⟨503975100620161157386225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 671966800826881543181633 503975100620161157386225)
                      ·
                        rfl

theorem cell23_981488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 1, 3, 2].length) (baseStart_981488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981488 prefixEnd_981488 := by exact prefixLift 981488
  have htrace : WordTrace (prefixWord ++ tailWord_981488) baseStart_981488 baseEnd_981488 := by
    simpa [prefixWord, tailWord_981488, baseEnd_981488] using wordTrace_append hprefix tailTrace_981488
  have hstable : (prefixWord ++ tailWord_981488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981488).length < 2 ^ (prefixWord ++ tailWord_981488).sum := by decide
  have hdescent : baseEnd_981488 < baseStart_981488 := by decide
  rcases family_descends (prefixWord ++ tailWord_981488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981558 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_981558 : Nat := 118140960795 + 981558 * 2 ^ 59
def prefixEnd_981558 : Nat := 4983230072969 + 3 ^ 40 * 981558 * 2
def baseEnd_981558 : Nat := 56001227140663987056767

theorem tailTrace_981558 : CollatzResearch.WordTrace tailWord_981558 prefixEnd_981558 56001227140663987056767 := by
  unfold tailWord_981558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2237522586124404850329083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23866907585326985070176885 2237522586124404850329083)
  ·
    refine ⟨3356283879186607275493625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2237522586124404850329083 3356283879186607275493625)
    ·
      refine ⟨2517212909389955456620219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3356283879186607275493625 2517212909389955456620219)
      ·
        refine ⟨3775819364084933184930329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2517212909389955456620219 3775819364084933184930329)
        ·
          refine ⟨2831864523063699888697747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3775819364084933184930329 2831864523063699888697747)
          ·
            refine ⟨4247796784595549833046621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831864523063699888697747 4247796784595549833046621)
            ·
              refine ⟨1592923794223331187392483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4247796784595549833046621 1592923794223331187392483)
              ·
                refine ⟨2389385691334996781088725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592923794223331187392483 2389385691334996781088725)
                ·
                  refine ⟨56001227140663987056767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2389385691334996781088725 56001227140663987056767)
                  ·
                    rfl

theorem cell23_981558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_981558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981558 prefixEnd_981558 := by exact prefixLift 981558
  have htrace : WordTrace (prefixWord ++ tailWord_981558) baseStart_981558 baseEnd_981558 := by
    simpa [prefixWord, tailWord_981558, baseEnd_981558] using wordTrace_append hprefix tailTrace_981558
  have hstable : (prefixWord ++ tailWord_981558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981558).length < 2 ^ (prefixWord ++ tailWord_981558).sum := by decide
  have hdescent : baseEnd_981558 < baseStart_981558 := by decide
  rcases family_descends (prefixWord ++ tailWord_981558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981569 : List Nat := [1, 2, 5, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_981569 : Nat := 118140960795 + 981569 * 2 ^ 59
def prefixEnd_981569 : Nat := 4983230072969 + 3 ^ 40 * 981569 * 2
def baseEnd_981569 : Nat := 504016692553175340473353

theorem tailTrace_981569 : CollatzResearch.WordTrace tailWord_981569 prefixEnd_981569 504016692553175340473353 := by
  unfold tailWord_981569
  simp only [CollatzResearch.WordTrace]
  refine ⟨35800762580950626483915761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23867175053967084322610507 35800762580950626483915761)
  ·
    refine ⟨26850571935712969862936821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35800762580950626483915761 26850571935712969862936821)
    ·
      refine ⟨2517241118973090924650327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26850571935712969862936821 2517241118973090924650327)
      ·
        refine ⟨3775861678459636386975491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2517241118973090924650327 3775861678459636386975491)
        ·
          refine ⟨5663792517689454580463237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3775861678459636386975491 5663792517689454580463237)
          ·
            refine ⟨1061961097066772733836857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5663792517689454580463237 1061961097066772733836857)
            ·
              refine ⟨796470822800079550377643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1061961097066772733836857 796470822800079550377643)
              ·
                refine ⟨1194706234200119325566465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796470822800079550377643 1194706234200119325566465)
                ·
                  refine ⟨896029675650089494174849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1194706234200119325566465 896029675650089494174849)
                  ·
                    refine ⟨672022256737567120631137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 896029675650089494174849 672022256737567120631137)
                    ·
                      refine ⟨504016692553175340473353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 672022256737567120631137 504016692553175340473353)
                      ·
                        rfl

theorem cell23_981569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_981569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981569 prefixEnd_981569 := by exact prefixLift 981569
  have htrace : WordTrace (prefixWord ++ tailWord_981569) baseStart_981569 baseEnd_981569 := by
    simpa [prefixWord, tailWord_981569, baseEnd_981569] using wordTrace_append hprefix tailTrace_981569
  have hstable : (prefixWord ++ tailWord_981569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981569).length < 2 ^ (prefixWord ++ tailWord_981569).sum := by decide
  have hdescent : baseEnd_981569 < baseStart_981569 := by decide
  rcases family_descends (prefixWord ++ tailWord_981569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981588 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_981588 : Nat := 118140960795 + 981588 * 2 ^ 59
def prefixEnd_981588 : Nat := 4983230072969 + 3 ^ 40 * 981588 * 2
def baseEnd_981588 : Nat := 168008816228536922045255

theorem tailTrace_981588 : CollatzResearch.WordTrace tailWord_981588 prefixEnd_981588 168008816228536922045255 := by
  unfold tailWord_981588
  simp only [CollatzResearch.WordTrace]
  refine ⟨17900727783940896364428709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23867637045254528485904945 17900727783940896364428709)
  ·
    refine ⟨3356386459488918068330383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17900727783940896364428709 3356386459488918068330383)
    ·
      refine ⟨5034579689233377102495575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3356386459488918068330383 5034579689233377102495575)
      ·
        refine ⟨7551869533850065653743363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5034579689233377102495575 7551869533850065653743363)
        ·
          refine ⟨11327804300775098480615045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7551869533850065653743363 11327804300775098480615045)
          ·
            refine ⟨2123963306395330965115321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11327804300775098480615045 2123963306395330965115321)
            ·
              refine ⟨1592972479796498223836491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2123963306395330965115321 1592972479796498223836491)
              ·
                refine ⟨2389458719694747335754737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592972479796498223836491 2389458719694747335754737)
                ·
                  refine ⟨1792094039771060501816053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2389458719694747335754737 1792094039771060501816053)
                  ·
                    refine ⟨168008816228536922045255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1792094039771060501816053 168008816228536922045255)
                    ·
                      rfl

theorem cell23_981588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_981588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981588 prefixEnd_981588 := by exact prefixLift 981588
  have htrace : WordTrace (prefixWord ++ tailWord_981588) baseStart_981588 baseEnd_981588 := by
    simpa [prefixWord, tailWord_981588, baseEnd_981588] using wordTrace_append hprefix tailTrace_981588
  have hstable : (prefixWord ++ tailWord_981588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981588).length < 2 ^ (prefixWord ++ tailWord_981588).sum := by decide
  have hdescent : baseEnd_981588 < baseStart_981588 := by decide
  rcases family_descends (prefixWord ++ tailWord_981588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981594 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_981594 : Nat := 118140960795 + 981594 * 2 ^ 59
def prefixEnd_981594 : Nat := 4983230072969 + 3 ^ 40 * 981594 * 2
def baseEnd_981594 : Nat := 504029529569537742660737

theorem tailTrace_981594 : CollatzResearch.WordTrace tailWord_981594 prefixEnd_981594 504029529569537742660737 := by
  unfold tailWord_981594
  simp only [CollatzResearch.WordTrace]
  refine ⟨8950418601465013938393959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23867782937240037169050557 8950418601465013938393959)
  ·
    refine ⟨13425627902197520907590939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8950418601465013938393959 13425627902197520907590939)
    ·
      refine ⟨20138441853296281361386409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13425627902197520907590939 20138441853296281361386409)
      ·
        refine ⟨15103831389972211021039807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20138441853296281361386409 15103831389972211021039807)
        ·
          refine ⟨22655747084958316531559711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15103831389972211021039807 22655747084958316531559711)
          ·
            refine ⟨33983620627437474797339567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22655747084958316531559711 33983620627437474797339567)
            ·
              refine ⟨50975430941156212196009351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33983620627437474797339567 50975430941156212196009351)
              ·
                refine ⟨76463146411734318294014027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50975430941156212196009351 76463146411734318294014027)
                ·
                  refine ⟨114694719617601477441021041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76463146411734318294014027 114694719617601477441021041)
                  ·
                    refine ⟨86021039713201108080765781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114694719617601477441021041 86021039713201108080765781)
                    ·
                      refine ⟨504029529569537742660737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 86021039713201108080765781 504029529569537742660737)
                      ·
                        rfl

theorem cell23_981594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_981594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981594 prefixEnd_981594 := by exact prefixLift 981594
  have htrace : WordTrace (prefixWord ++ tailWord_981594) baseStart_981594 baseEnd_981594 := by
    simpa [prefixWord, tailWord_981594, baseEnd_981594] using wordTrace_append hprefix tailTrace_981594
  have hstable : (prefixWord ++ tailWord_981594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981594).length < 2 ^ (prefixWord ++ tailWord_981594).sum := by decide
  have hdescent : baseEnd_981594 < baseStart_981594 := by decide
  rcases family_descends (prefixWord ++ tailWord_981594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981611 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 3]
def baseStart_981611 : Nat := 118140960795 + 981611 * 2 ^ 59
def prefixEnd_981611 : Nat := 4983230072969 + 3 ^ 40 * 981611 * 2
def baseEnd_981611 : Nat := 504038258740664176148159

theorem tailTrace_981611 : CollatzResearch.WordTrace tailWord_981611 prefixEnd_981611 504038258740664176148159 := by
  unfold tailWord_981611
  simp only [CollatzResearch.WordTrace]
  refine ⟨35802294446798467656944687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23868196297865645104629791 35802294446798467656944687)
  ·
    refine ⟨53703441670197701485417031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35802294446798467656944687 53703441670197701485417031)
    ·
      refine ⟨80555162505296552228125547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53703441670197701485417031 80555162505296552228125547)
      ·
        refine ⟨120832743757944828342188321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80555162505296552228125547 120832743757944828342188321)
        ·
          refine ⟨90624557818458621256641241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120832743757944828342188321 90624557818458621256641241)
          ·
            refine ⟨67968418363843965942480931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90624557818458621256641241 67968418363843965942480931)
            ·
              refine ⟨101952627545765948913721397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67968418363843965942480931 101952627545765948913721397)
              ·
                refine ⟨9558058832415557710661381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101952627545765948913721397 9558058832415557710661381)
                ·
                  refine ⟨1792136031077917070749009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9558058832415557710661381 1792136031077917070749009)
                  ·
                    refine ⟨1344102023308437803061757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1792136031077917070749009 1344102023308437803061757)
                    ·
                      refine ⟨504038258740664176148159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1344102023308437803061757 504038258740664176148159)
                      ·
                        rfl

theorem cell23_981611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 3].length) (baseStart_981611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981611 prefixEnd_981611 := by exact prefixLift 981611
  have htrace : WordTrace (prefixWord ++ tailWord_981611) baseStart_981611 baseEnd_981611 := by
    simpa [prefixWord, tailWord_981611, baseEnd_981611] using wordTrace_append hprefix tailTrace_981611
  have hstable : (prefixWord ++ tailWord_981611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981611).length < 2 ^ (prefixWord ++ tailWord_981611).sum := by decide
  have hdescent : baseEnd_981611 < baseStart_981611 := by decide
  rcases family_descends (prefixWord ++ tailWord_981611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981642 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 2, 1, 4]
def baseStart_981642 : Nat := 118140960795 + 981642 * 2 ^ 59
def prefixEnd_981642 : Nat := 4983230072969 + 3 ^ 40 * 981642 * 2
def baseEnd_981642 : Nat := 504054176640953554860517

theorem tailTrace_981642 : CollatzResearch.WordTrace tailWord_981642 prefixEnd_981642 504054176640953554860517 := by
  unfold tailWord_981642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8950856277421539987830795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23868950073124106634215453 8950856277421539987830795)
  ·
    refine ⟨13426284416132309981746193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8950856277421539987830795 13426284416132309981746193)
    ·
      refine ⟨10069713312099232486309645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13426284416132309981746193 10069713312099232486309645)
      ·
        refine ⟨3776142492037212182366117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10069713312099232486309645 3776142492037212182366117)
        ·
          refine ⟨708026717256977284193647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3776142492037212182366117 708026717256977284193647)
          ·
            refine ⟨1062040075885465926290471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708026717256977284193647 1062040075885465926290471)
            ·
              refine ⟨1593060113828198889435707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062040075885465926290471 1593060113828198889435707)
              ·
                refine ⟨2389590170742298334153561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593060113828198889435707 2389590170742298334153561)
                ·
                  refine ⟨1792192628056723750615171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2389590170742298334153561 1792192628056723750615171)
                  ·
                    refine ⟨2688288942085085625922757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1792192628056723750615171 2688288942085085625922757)
                    ·
                      refine ⟨504054176640953554860517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2688288942085085625922757 504054176640953554860517)
                      ·
                        rfl

theorem cell23_981642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_981642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981642 prefixEnd_981642 := by exact prefixLift 981642
  have htrace : WordTrace (prefixWord ++ tailWord_981642) baseStart_981642 baseEnd_981642 := by
    simpa [prefixWord, tailWord_981642, baseEnd_981642] using wordTrace_append hprefix tailTrace_981642
  have hstable : (prefixWord ++ tailWord_981642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981642).length < 2 ^ (prefixWord ++ tailWord_981642).sum := by decide
  have hdescent : baseEnd_981642 < baseStart_981642 := by decide
  rcases family_descends (prefixWord ++ tailWord_981642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981652 : List Nat := [2, 4, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_981652 : Nat := 118140960795 + 981652 * 2 ^ 59
def prefixEnd_981652 : Nat := 4983230072969 + 3 ^ 40 * 981652 * 2
def baseEnd_981652 : Nat := 168019770482499505245157

theorem tailTrace_981652 : CollatzResearch.WordTrace tailWord_981652 prefixEnd_981652 168019770482499505245157 := by
  unfold tailWord_981652
  simp only [CollatzResearch.WordTrace]
  refine ⟨17901894919824965829593605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23869193226433287772791473 17901894919824965829593605)
  ·
    refine ⟨3356605297467181093048801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17901894919824965829593605 3356605297467181093048801)
    ·
      refine ⟨2517453973100385819786601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3356605297467181093048801 2517453973100385819786601)
      ·
        refine ⟨1888090479825289364839951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2517453973100385819786601 1888090479825289364839951)
        ·
          refine ⟨2832135719737934047259927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888090479825289364839951 2832135719737934047259927)
          ·
            refine ⟨4248203579606901070889891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832135719737934047259927 4248203579606901070889891)
            ·
              refine ⟨6372305369410351606334837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4248203579606901070889891 6372305369410351606334837)
              ·
                refine ⟨597403628382220463093891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6372305369410351606334837 597403628382220463093891)
                ·
                  refine ⟨896105442573330694640837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597403628382220463093891 896105442573330694640837)
                  ·
                    refine ⟨168019770482499505245157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 896105442573330694640837 168019770482499505245157)
                    ·
                      rfl

theorem cell23_981652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_981652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981652 prefixEnd_981652 := by exact prefixLift 981652
  have htrace : WordTrace (prefixWord ++ tailWord_981652) baseStart_981652 baseEnd_981652 := by
    simpa [prefixWord, tailWord_981652, baseEnd_981652] using wordTrace_append hprefix tailTrace_981652
  have hstable : (prefixWord ++ tailWord_981652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981652).length < 2 ^ (prefixWord ++ tailWord_981652).sum := by decide
  have hdescent : baseEnd_981652 < baseStart_981652 := by decide
  rcases family_descends (prefixWord ++ tailWord_981652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981665 : List Nat := [1, 2, 3, 3, 3, 2, 1, 2, 6]
def baseStart_981665 : Nat := 118140960795 + 981665 * 2 ^ 59
def prefixEnd_981665 : Nat := 4983230072969 + 3 ^ 40 * 981665 * 2
def baseEnd_981665 : Nat := 56007331855111884985879

theorem tailTrace_981665 : CollatzResearch.WordTrace tailWord_981665 prefixEnd_981665 56007331855111884985879 := by
  unfold tailWord_981665
  simp only [CollatzResearch.WordTrace]
  refine ⟨35804263988602834879410449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23869509325735223252940299 35804263988602834879410449)
  ·
    refine ⟨26853197991452126159557837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35804263988602834879410449 26853197991452126159557837)
    ·
      refine ⟨10069949246794547309834189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26853197991452126159557837 10069949246794547309834189)
      ·
        refine ⟨3776230967547955241187821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10069949246794547309834189 3776230967547955241187821)
        ·
          refine ⟨1416086612830483215445433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3776230967547955241187821 1416086612830483215445433)
          ·
            refine ⟨1062064959622862411584075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1416086612830483215445433 1062064959622862411584075)
            ·
              refine ⟨1593097439434293617376113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062064959622862411584075 1593097439434293617376113)
              ·
                refine ⟨1194823079575720213032085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1593097439434293617376113 1194823079575720213032085)
                ·
                  refine ⟨56007331855111884985879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1194823079575720213032085 56007331855111884985879)
                  ·
                    rfl

theorem cell23_981665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 6].length) (baseStart_981665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981665 prefixEnd_981665 := by exact prefixLift 981665
  have htrace : WordTrace (prefixWord ++ tailWord_981665) baseStart_981665 baseEnd_981665 := by
    simpa [prefixWord, tailWord_981665, baseEnd_981665] using wordTrace_append hprefix tailTrace_981665
  have hstable : (prefixWord ++ tailWord_981665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981665).length < 2 ^ (prefixWord ++ tailWord_981665).sum := by decide
  have hdescent : baseEnd_981665 < baseStart_981665 := by decide
  rcases family_descends (prefixWord ++ tailWord_981665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981685 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_981685 : Nat := 118140960795 + 981685 * 2 ^ 59
def prefixEnd_981685 : Nat := 4983230072969 + 3 ^ 40 * 981685 * 2
def baseEnd_981685 : Nat := 504076256309096886622819

theorem tailTrace_981685 : CollatzResearch.WordTrace tailWord_981685 prefixEnd_981685 504076256309096886622819 := by
  unfold tailWord_981685
  simp only [CollatzResearch.WordTrace]
  refine ⟨35804993448530378295138509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23869995632353585530092339 35804993448530378295138509)
  ·
    refine ⟨13426872543198891860676941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35804993448530378295138509 13426872543198891860676941)
    ·
      refine ⟨5035077203699584447753853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13426872543198891860676941 5035077203699584447753853)
      ·
        refine ⟨1888153951387344167907695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5035077203699584447753853 1888153951387344167907695)
        ·
          refine ⟨2832230927081016251861543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888153951387344167907695 2832230927081016251861543)
          ·
            refine ⟨4248346390621524377792315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832230927081016251861543 4248346390621524377792315)
            ·
              refine ⟨6372519585932286566688473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4248346390621524377792315 6372519585932286566688473)
              ·
                refine ⟨4779389689449214925016355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6372519585932286566688473 4779389689449214925016355)
                ·
                  refine ⟨7169084534173822387524533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779389689449214925016355 7169084534173822387524533)
                  ·
                    refine ⟨672101675078795848830425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7169084534173822387524533 672101675078795848830425)
                    ·
                      refine ⟨504076256309096886622819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 672101675078795848830425 504076256309096886622819)
                      ·
                        rfl

theorem cell23_981685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_981685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981685 prefixEnd_981685 := by exact prefixLift 981685
  have htrace : WordTrace (prefixWord ++ tailWord_981685) baseStart_981685 baseEnd_981685 := by
    simpa [prefixWord, tailWord_981685, baseEnd_981685] using wordTrace_append hprefix tailTrace_981685
  have hstable : (prefixWord ++ tailWord_981685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981685).length < 2 ^ (prefixWord ++ tailWord_981685).sum := by decide
  have hdescent : baseEnd_981685 < baseStart_981685 := by decide
  rcases family_descends (prefixWord ++ tailWord_981685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981732 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 3, 2, 2]
def baseStart_981732 : Nat := 118140960795 + 981732 * 2 ^ 59
def prefixEnd_981732 : Nat := 4983230072969 + 3 ^ 40 * 981732 * 2
def baseEnd_981732 : Nat := 504100389899858202735103

theorem tailTrace_981732 : CollatzResearch.WordTrace tailWord_981732 prefixEnd_981732 504100389899858202735103 := by
  unfold tailWord_981732
  simp only [CollatzResearch.WordTrace]
  refine ⟨17903353839680052661049725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23871138452906736881399633 17903353839680052661049725)
  ·
    refine ⟨6713757689880019747893647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17903353839680052661049725 6713757689880019747893647)
    ·
      refine ⟨10070636534820029621840471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6713757689880019747893647 10070636534820029621840471)
      ·
        refine ⟨15105954802230044432760707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10070636534820029621840471 15105954802230044432760707)
        ·
          refine ⟨22658932203345066649141061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15105954802230044432760707 22658932203345066649141061)
          ·
            refine ⟨4248549788127199996713949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22658932203345066649141061 4248549788127199996713949)
            ·
              refine ⟨1593206170547699998767731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4248549788127199996713949 1593206170547699998767731)
              ·
                refine ⟨2389809255821549998151597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593206170547699998767731 2389809255821549998151597)
                ·
                  refine ⟨896178470933081249306849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2389809255821549998151597 896178470933081249306849)
                  ·
                    refine ⟨672133853199810936980137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 896178470933081249306849 672133853199810936980137)
                    ·
                      refine ⟨504100389899858202735103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 672133853199810936980137 504100389899858202735103)
                      ·
                        rfl

theorem cell23_981732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_981732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981732 prefixEnd_981732 := by exact prefixLift 981732
  have htrace : WordTrace (prefixWord ++ tailWord_981732) baseStart_981732 baseEnd_981732 := by
    simpa [prefixWord, tailWord_981732, baseEnd_981732] using wordTrace_append hprefix tailTrace_981732
  have hstable : (prefixWord ++ tailWord_981732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981732).length < 2 ^ (prefixWord ++ tailWord_981732).sum := by decide
  have hdescent : baseEnd_981732 < baseStart_981732 := by decide
  rcases family_descends (prefixWord ++ tailWord_981732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981742 : List Nat := [4, 1, 2, 1, 1, 3, 4, 1, 2, 4]
def baseStart_981742 : Nat := 118140960795 + 981742 * 2 ^ 59
def prefixEnd_981742 : Nat := 4983230072969 + 3 ^ 40 * 981742 * 2
def baseEnd_981742 : Nat := 168035174902134387870019

theorem tailTrace_981742 : CollatzResearch.WordTrace tailWord_981742 prefixEnd_981742 168035174902134387870019 := by
  unfold tailWord_981742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4475884051165484628745435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23871381606215918019975653 4475884051165484628745435)
  ·
    refine ⟨6713826076748226943118153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4475884051165484628745435 6713826076748226943118153)
    ·
      refine ⟨5035369557561170207338615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6713826076748226943118153 5035369557561170207338615)
      ·
        refine ⟨7553054336341755311007923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5035369557561170207338615 7553054336341755311007923)
        ·
          refine ⟨11329581504512632966511885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7553054336341755311007923 11329581504512632966511885)
          ·
            refine ⟨4248593064192237362441957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11329581504512632966511885 4248593064192237362441957)
            ·
              refine ⟨796611199536044505457867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4248593064192237362441957 796611199536044505457867)
              ·
                refine ⟨1194916799304066758186801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796611199536044505457867 1194916799304066758186801)
                ·
                  refine ⟨896187599478050068640101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1194916799304066758186801 896187599478050068640101)
                  ·
                    refine ⟨168035174902134387870019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 896187599478050068640101 168035174902134387870019)
                    ·
                      rfl

theorem cell23_981742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_981742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981742 prefixEnd_981742 := by exact prefixLift 981742
  have htrace : WordTrace (prefixWord ++ tailWord_981742) baseStart_981742 baseEnd_981742 := by
    simpa [prefixWord, tailWord_981742, baseEnd_981742] using wordTrace_append hprefix tailTrace_981742
  have hstable : (prefixWord ++ tailWord_981742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981742).length < 2 ^ (prefixWord ++ tailWord_981742).sum := by decide
  have hdescent : baseEnd_981742 < baseStart_981742 := by decide
  rcases family_descends (prefixWord ++ tailWord_981742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981749 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_981749 : Nat := 118140960795 + 981749 * 2 ^ 59
def prefixEnd_981749 : Nat := 4983230072969 + 3 ^ 40 * 981749 * 2
def baseEnd_981749 : Nat := 504109119070984636222525

theorem tailTrace_981749 : CollatzResearch.WordTrace tailWord_981749 prefixEnd_981749 504109119070984636222525 := by
  unfold tailWord_981749
  simp only [CollatzResearch.WordTrace]
  refine ⟨35807327720298517225468301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23871551813532344816978867 35807327720298517225468301)
  ·
    refine ⟨13427747895111943959550613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35807327720298517225468301 13427747895111943959550613)
    ·
      refine ⟨629425682583372373103935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13427747895111943959550613 629425682583372373103935)
      ·
        refine ⟨944138523875058559655903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629425682583372373103935 944138523875058559655903)
        ·
          refine ⟨1416207785812587839483855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944138523875058559655903 1416207785812587839483855)
          ·
            refine ⟨2124311678718881759225783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416207785812587839483855 2124311678718881759225783)
            ·
              refine ⟨3186467518078322638838675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124311678718881759225783 3186467518078322638838675)
              ·
                refine ⟨4779701277117483958258013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186467518078322638838675 4779701277117483958258013)
                ·
                  refine ⟨1792387978919056484346755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4779701277117483958258013 1792387978919056484346755)
                  ·
                    refine ⟨2688581968378584726520133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1792387978919056484346755 2688581968378584726520133)
                    ·
                      refine ⟨504109119070984636222525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2688581968378584726520133 504109119070984636222525)
                      ·
                        rfl

theorem cell23_981749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_981749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981749 prefixEnd_981749 := by exact prefixLift 981749
  have htrace : WordTrace (prefixWord ++ tailWord_981749) baseStart_981749 baseEnd_981749 := by
    simpa [prefixWord, tailWord_981749, baseEnd_981749] using wordTrace_append hprefix tailTrace_981749
  have hstable : (prefixWord ++ tailWord_981749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981749).length < 2 ^ (prefixWord ++ tailWord_981749).sum := by decide
  have hdescent : baseEnd_981749 < baseStart_981749 := by decide
  rcases family_descends (prefixWord ++ tailWord_981749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981783 : List Nat := [1, 1, 3, 4, 3, 2, 2, 2, 1, 2, 2]
def baseStart_981783 : Nat := 118140960795 + 981783 * 2 ^ 59
def prefixEnd_981783 : Nat := 4983230072969 + 3 ^ 40 * 981783 * 2
def baseEnd_981783 : Nat := 504126577413237503197369

theorem tailTrace_981783 : CollatzResearch.WordTrace tailWord_981783 prefixEnd_981783 504126577413237503197369 := by
  unfold tailWord_981783
  simp only [CollatzResearch.WordTrace]
  refine ⟨35808567802175341032206003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23872378534783560688137335 35808567802175341032206003)
  ·
    refine ⟨53712851703263011548309005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35808567802175341032206003 53712851703263011548309005)
    ·
      refine ⟨20142319388723629330615877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53712851703263011548309005 20142319388723629330615877)
      ·
        refine ⟨3776684885385680499490477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20142319388723629330615877 3776684885385680499490477)
        ·
          refine ⟨1416256832019630187308929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3776684885385680499490477 1416256832019630187308929)
          ·
            refine ⟨1062192624014722640481697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1416256832019630187308929 1062192624014722640481697)
            ·
              refine ⟨796644468011041980361273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062192624014722640481697 796644468011041980361273)
              ·
                refine ⟨597483351008281485270955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796644468011041980361273 597483351008281485270955)
                ·
                  refine ⟨896225026512422227906433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597483351008281485270955 896225026512422227906433)
                  ·
                    refine ⟨672168769884316670929825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 896225026512422227906433 672168769884316670929825)
                    ·
                      refine ⟨504126577413237503197369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 672168769884316670929825 504126577413237503197369)
                      ·
                        rfl

theorem cell23_981783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_981783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981783 prefixEnd_981783 := by exact prefixLift 981783
  have htrace : WordTrace (prefixWord ++ tailWord_981783) baseStart_981783 baseEnd_981783 := by
    simpa [prefixWord, tailWord_981783, baseEnd_981783] using wordTrace_append hprefix tailTrace_981783
  have hstable : (prefixWord ++ tailWord_981783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981783).length < 2 ^ (prefixWord ++ tailWord_981783).sum := by decide
  have hdescent : baseEnd_981783 < baseStart_981783 := by decide
  rcases family_descends (prefixWord ++ tailWord_981783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981788 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_981788 : Nat := 118140960795 + 981788 * 2 ^ 59
def prefixEnd_981788 : Nat := 4983230072969 + 3 ^ 40 * 981788 * 2
def baseEnd_981788 : Nat := 504129144816509983634845

theorem tailTrace_981788 : CollatzResearch.WordTrace tailWord_981788 prefixEnd_981788 504129144816509983634845 := by
  unfold tailWord_981788
  simp only [CollatzResearch.WordTrace]
  refine ⟨17904375083578613443069009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23872500111438151257425345 17904375083578613443069009)
  ·
    refine ⟨13428281312683960082301757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17904375083578613443069009 13428281312683960082301757)
    ·
      refine ⟨5035605492256485030863159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13428281312683960082301757 5035605492256485030863159)
      ·
        refine ⟨7553408238384727546294739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5035605492256485030863159 7553408238384727546294739)
        ·
          refine ⟨11330112357577091319442109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7553408238384727546294739 11330112357577091319442109)
          ·
            refine ⟨4248792134091409244790791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11330112357577091319442109 4248792134091409244790791)
            ·
              refine ⟨6373188201137113867186187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4248792134091409244790791 6373188201137113867186187)
              ·
                refine ⟨9559782301705670800779281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6373188201137113867186187 9559782301705670800779281)
                ·
                  refine ⟨7169836726279253100584461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9559782301705670800779281 7169836726279253100584461)
                  ·
                    refine ⟨2688688772354719912719173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7169836726279253100584461 2688688772354719912719173)
                    ·
                      refine ⟨504129144816509983634845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2688688772354719912719173 504129144816509983634845)
                      ·
                        rfl

theorem cell23_981788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_981788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981788 prefixEnd_981788 := by exact prefixLift 981788
  have htrace : WordTrace (prefixWord ++ tailWord_981788) baseStart_981788 baseEnd_981788 := by
    simpa [prefixWord, tailWord_981788, baseEnd_981788] using wordTrace_append hprefix tailTrace_981788
  have hstable : (prefixWord ++ tailWord_981788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981788).length < 2 ^ (prefixWord ++ tailWord_981788).sum := by decide
  have hdescent : baseEnd_981788 < baseStart_981788 := by decide
  rcases family_descends (prefixWord ++ tailWord_981788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981801 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 6]
def baseStart_981801 : Nat := 118140960795 + 981801 * 2 ^ 59
def prefixEnd_981801 : Nat := 4983230072969 + 3 ^ 40 * 981801 * 2
def baseEnd_981801 : Nat := 504135820065018432772285

theorem tailTrace_981801 : CollatzResearch.WordTrace tailWord_981801 prefixEnd_981801 504135820065018432772285 := by
  unfold tailWord_981801
  simp only [CollatzResearch.WordTrace]
  refine ⟨35809224316110130106361257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23872816210740086737574171 35809224316110130106361257)
  ·
    refine ⟨26856918237082597579770943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35809224316110130106361257 26856918237082597579770943)
    ·
      refine ⟨40285377355623896369656415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26856918237082597579770943 40285377355623896369656415)
      ·
        refine ⟨60428066033435844554484623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40285377355623896369656415 60428066033435844554484623)
        ·
          refine ⟨90642099050153766831726935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60428066033435844554484623 90642099050153766831726935)
          ·
            refine ⟨135963148575230650247590403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90642099050153766831726935 135963148575230650247590403)
            ·
              refine ⟨203944722862845975371385605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135963148575230650247590403 203944722862845975371385605)
              ·
                refine ⟨38239635536783620382134801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203944722862845975371385605 38239635536783620382134801)
                ·
                  refine ⟨28679726652587715286601101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38239635536783620382134801 28679726652587715286601101)
                  ·
                    refine ⟨10754897494720393232475413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28679726652587715286601101 10754897494720393232475413)
                    ·
                      refine ⟨504135820065018432772285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10754897494720393232475413 504135820065018432772285)
                      ·
                        rfl

theorem cell23_981801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_981801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981801 prefixEnd_981801 := by exact prefixLift 981801
  have htrace : WordTrace (prefixWord ++ tailWord_981801) baseStart_981801 baseEnd_981801 := by
    simpa [prefixWord, tailWord_981801, baseEnd_981801] using wordTrace_append hprefix tailTrace_981801
  have hstable : (prefixWord ++ tailWord_981801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981801).length < 2 ^ (prefixWord ++ tailWord_981801).sum := by decide
  have hdescent : baseEnd_981801 < baseStart_981801 := by decide
  rcases family_descends (prefixWord ++ tailWord_981801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981845 : List Nat := [1, 3, 2, 2, 2, 1, 1, 6, 5]
def baseStart_981845 : Nat := 118140960795 + 981845 * 2 ^ 59
def prefixEnd_981845 : Nat := 4983230072969 + 3 ^ 40 * 981845 * 2
def baseEnd_981845 : Nat := 56017601468201806735787

theorem tailTrace_981845 : CollatzResearch.WordTrace tailWord_981845 prefixEnd_981845 56017601468201806735787 := by
  unfold tailWord_981845
  simp only [CollatzResearch.WordTrace]
  refine ⟨35810829127950725620962989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23873886085300483747308659 35810829127950725620962989)
  ·
    refine ⟨13429060922981522107861121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35810829127950725620962989 13429060922981522107861121)
    ·
      refine ⟨10071795692236141580895841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13429060922981522107861121 10071795692236141580895841)
      ·
        refine ⟨7553846769177106185671881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10071795692236141580895841 7553846769177106185671881)
        ·
          refine ⟨5665385076882829639253911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7553846769177106185671881 5665385076882829639253911)
          ·
            refine ⟨8498077615324244458880867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5665385076882829639253911 8498077615324244458880867)
            ·
              refine ⟨12747116422986366688321301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8498077615324244458880867 12747116422986366688321301)
              ·
                refine ⟨597521082327485938515061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12747116422986366688321301 597521082327485938515061)
                ·
                  refine ⟨56017601468201806735787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 597521082327485938515061 56017601468201806735787)
                  ·
                    rfl

theorem cell23_981845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 5].length) (baseStart_981845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981845 prefixEnd_981845 := by exact prefixLift 981845
  have htrace : WordTrace (prefixWord ++ tailWord_981845) baseStart_981845 baseEnd_981845 := by
    simpa [prefixWord, tailWord_981845, baseEnd_981845] using wordTrace_append hprefix tailTrace_981845
  have hstable : (prefixWord ++ tailWord_981845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981845).length < 2 ^ (prefixWord ++ tailWord_981845).sum := by decide
  have hdescent : baseEnd_981845 < baseStart_981845 := by decide
  rcases family_descends (prefixWord ++ tailWord_981845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981895 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_981895 : Nat := 118140960795 + 981895 * 2 ^ 59
def prefixEnd_981895 : Nat := 4983230072969 + 3 ^ 40 * 981895 * 2
def baseEnd_981895 : Nat := 504184087246541064996853

theorem tailTrace_981895 : CollatzResearch.WordTrace tailWord_981895 prefixEnd_981895 504184087246541064996853 := by
  unfold tailWord_981895
  simp only [CollatzResearch.WordTrace]
  refine ⟨35812652777769584160283139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23875101851846389440188759 35812652777769584160283139)
  ·
    refine ⟨53718979166654376240424709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35812652777769584160283139 53718979166654376240424709)
    ·
      refine ⟨10072308593747695545079633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53718979166654376240424709 10072308593747695545079633)
      ·
        refine ⟨7554231445310771658809725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10072308593747695545079633 7554231445310771658809725)
        ·
          refine ⟨2832836791991539372053647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7554231445310771658809725 2832836791991539372053647)
          ·
            refine ⟨4249255187987309058080471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832836791991539372053647 4249255187987309058080471)
            ·
              refine ⟨6373882781980963587120707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4249255187987309058080471 6373882781980963587120707)
              ·
                refine ⟨9560824172971445380681061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6373882781980963587120707 9560824172971445380681061)
                ·
                  refine ⟨1792654532432146008877699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9560824172971445380681061 1792654532432146008877699)
                  ·
                    refine ⟨2688981798648219013316549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1792654532432146008877699 2688981798648219013316549)
                    ·
                      refine ⟨504184087246541064996853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2688981798648219013316549 504184087246541064996853)
                      ·
                        rfl

theorem cell23_981895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_981895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981895 prefixEnd_981895 := by exact prefixLift 981895
  have htrace : WordTrace (prefixWord ++ tailWord_981895) baseStart_981895 baseEnd_981895 := by
    simpa [prefixWord, tailWord_981895, baseEnd_981895] using wordTrace_append hprefix tailTrace_981895
  have hstable : (prefixWord ++ tailWord_981895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981895).length < 2 ^ (prefixWord ++ tailWord_981895).sum := by decide
  have hdescent : baseEnd_981895 < baseStart_981895 := by decide
  rcases family_descends (prefixWord ++ tailWord_981895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981938 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_981938 : Nat := 118140960795 + 981938 * 2 ^ 59
def prefixEnd_981938 : Nat := 4983230072969 + 3 ^ 40 * 981938 * 2
def baseEnd_981938 : Nat := 504206166914684396759155

theorem tailTrace_981938 : CollatzResearch.WordTrace tailWord_981938 prefixEnd_981938 504206166914684396759155 := by
  unfold tailWord_981938
  simp only [CollatzResearch.WordTrace]
  refine ⟨8953555279153450626024617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23876147411075868336065645 8953555279153450626024617)
  ·
    refine ⟨6715166459365087969518463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8953555279153450626024617 6715166459365087969518463)
    ·
      refine ⟨10072749689047631954277695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6715166459365087969518463 10072749689047631954277695)
      ·
        refine ⟨15109124533571447931416543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10072749689047631954277695 15109124533571447931416543)
        ·
          refine ⟨22663686800357171897124815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15109124533571447931416543 22663686800357171897124815)
          ·
            refine ⟨33995530200535757845687223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22663686800357171897124815 33995530200535757845687223)
            ·
              refine ⟨50993295300803636768530835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33995530200535757845687223 50993295300803636768530835)
              ·
                refine ⟨76489942951205455152796253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50993295300803636768530835 76489942951205455152796253)
                ·
                  refine ⟨28683728606702045682298595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76489942951205455152796253 28683728606702045682298595)
                  ·
                    refine ⟨43025592910053068523447893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28683728606702045682298595 43025592910053068523447893)
                    ·
                      refine ⟨504206166914684396759155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 43025592910053068523447893 504206166914684396759155)
                      ·
                        rfl

theorem cell23_981938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_981938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_981938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_981938 prefixEnd_981938 := by exact prefixLift 981938
  have htrace : WordTrace (prefixWord ++ tailWord_981938) baseStart_981938 baseEnd_981938 := by
    simpa [prefixWord, tailWord_981938, baseEnd_981938] using wordTrace_append hprefix tailTrace_981938
  have hstable : (prefixWord ++ tailWord_981938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981938).length < 2 ^ (prefixWord ++ tailWord_981938).sum := by decide
  have hdescent : baseEnd_981938 < baseStart_981938 := by decide
  rcases family_descends (prefixWord ++ tailWord_981938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
