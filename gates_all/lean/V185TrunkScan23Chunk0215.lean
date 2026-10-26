import V185TrunkScan23Chunk0214

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1271969 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 4, 4]
def baseStart_1271969 : Nat := 118140960795 + 1271969 * 2 ^ 59
def prefixEnd_1271969 : Nat := 4983230072969 + 3 ^ 40 * 1271969 * 2
def baseEnd_1271969 : Nat := 217710491539613049712609

theorem tailTrace_1271969 : CollatzResearch.WordTrace tailWord_1271969 prefixEnd_1271969 217710491539613049712609 := by
  unfold tailWord_1271969
  simp only [CollatzResearch.WordTrace]
  refine ⟨46392520728881022855346961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30928347152587348570231307 46392520728881022855346961)
  ·
    refine ⟨34794390546660767141510221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46392520728881022855346961 34794390546660767141510221)
    ·
      refine ⟨13047896454997787678066333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34794390546660767141510221 13047896454997787678066333)
      ·
        refine ⟨4892961170624170379274875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13047896454997787678066333 4892961170624170379274875)
        ·
          refine ⟨7339441755936255568912313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4892961170624170379274875 7339441755936255568912313)
          ·
            refine ⟨5504581316952191676684235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7339441755936255568912313 5504581316952191676684235)
            ·
              refine ⟨8256871975428287515026353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5504581316952191676684235 8256871975428287515026353)
              ·
                refine ⟨6192653981571215636269765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8256871975428287515026353 6192653981571215636269765)
                ·
                  refine ⟨1161122621544602931800581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6192653981571215636269765 1161122621544602931800581)
                  ·
                    refine ⟨217710491539613049712609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1161122621544602931800581 217710491539613049712609)
                    ·
                      rfl

theorem cell23_1271969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_1271969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271969 prefixEnd_1271969 := by exact prefixLift 1271969
  have htrace : WordTrace (prefixWord ++ tailWord_1271969) baseStart_1271969 baseEnd_1271969 := by
    simpa [prefixWord, tailWord_1271969, baseEnd_1271969] using wordTrace_append hprefix tailTrace_1271969
  have hstable : (prefixWord ++ tailWord_1271969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271969).length < 2 ^ (prefixWord ++ tailWord_1271969).sum := by decide
  have hdescent : baseEnd_1271969 < baseStart_1271969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271970 : List Nat := [3, 3, 1, 3, 1, 1, 3, 3, 1, 1, 3]
def baseStart_1271970 : Nat := 118140960795 + 1271970 * 2 ^ 59
def prefixEnd_1271970 : Nat := 4983230072969 + 3 ^ 40 * 1271970 * 2
def baseEnd_1271970 : Nat := 653131988099493645225323

theorem tailTrace_1271970 : CollatzResearch.WordTrace tailWord_1271970 prefixEnd_1271970 653131988099493645225323 := by
  unfold tailWord_1271970
  simp only [CollatzResearch.WordTrace]
  refine ⟨11598139300469350006533341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30928371467918266684088909 11598139300469350006533341)
  ·
    refine ⟨4349302237676006252450003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11598139300469350006533341 4349302237676006252450003)
    ·
      refine ⟨6523953356514009378675005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4349302237676006252450003 6523953356514009378675005)
      ·
        refine ⟨2446482508692753517003127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6523953356514009378675005 2446482508692753517003127)
        ·
          refine ⟨3669723763039130275504691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446482508692753517003127 3669723763039130275504691)
          ·
            refine ⟨5504585644558695413257037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3669723763039130275504691 5504585644558695413257037)
            ·
              refine ⟨2064219616709510779971389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5504585644558695413257037 2064219616709510779971389)
              ·
                refine ⟨774082356266066542489271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2064219616709510779971389 774082356266066542489271)
                ·
                  refine ⟨1161123534399099813733907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 774082356266066542489271 1161123534399099813733907)
                  ·
                    refine ⟨1741685301598649720600861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1161123534399099813733907 1741685301598649720600861)
                    ·
                      refine ⟨653131988099493645225323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1741685301598649720600861 653131988099493645225323)
                      ·
                        rfl

theorem cell23_1271970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_1271970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271970 prefixEnd_1271970 := by exact prefixLift 1271970
  have htrace : WordTrace (prefixWord ++ tailWord_1271970) baseStart_1271970 baseEnd_1271970 := by
    simpa [prefixWord, tailWord_1271970, baseEnd_1271970] using wordTrace_append hprefix tailTrace_1271970
  have hstable : (prefixWord ++ tailWord_1271970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271970).length < 2 ^ (prefixWord ++ tailWord_1271970).sum := by decide
  have hdescent : baseEnd_1271970 < baseStart_1271970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272009 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 6, 1, 3]
def baseStart_1272009 : Nat := 118140960795 + 1272009 * 2 ^ 59
def prefixEnd_1272009 : Nat := 4983230072969 + 3 ^ 40 * 1272009 * 2
def baseEnd_1272009 : Nat := 653152013845018992637643

theorem tailTrace_1272009 : CollatzResearch.WordTrace tailWord_1272009 prefixEnd_1272009 653152013845018992637643 := by
  unfold tailWord_1272009
  simp only [CollatzResearch.WordTrace]
  refine ⟨46393979648736109686803081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30929319765824073124535387 46393979648736109686803081)
  ·
    refine ⟨34795484736552082265102311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46393979648736109686803081 34795484736552082265102311)
    ·
      refine ⟨52193227104828123397653467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34795484736552082265102311 52193227104828123397653467)
      ·
        refine ⟨78289840657242185096480201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52193227104828123397653467 78289840657242185096480201)
        ·
          refine ⟨58717380492931638822360151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78289840657242185096480201 58717380492931638822360151)
          ·
            refine ⟨88076070739397458233540227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58717380492931638822360151 88076070739397458233540227)
            ·
              refine ⟨132114106109096187350310341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88076070739397458233540227 132114106109096187350310341)
              ·
                refine ⟨24771394895455535128183189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132114106109096187350310341 24771394895455535128183189)
                ·
                  refine ⟨1161159135724478209133587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24771394895455535128183189 1161159135724478209133587)
                  ·
                    refine ⟨1741738703586717313700381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1161159135724478209133587 1741738703586717313700381)
                    ·
                      refine ⟨653152013845018992637643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1741738703586717313700381 653152013845018992637643)
                      ·
                        rfl

theorem cell23_1272009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 1, 3].length) (baseStart_1272009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272009 prefixEnd_1272009 := by exact prefixLift 1272009
  have htrace : WordTrace (prefixWord ++ tailWord_1272009) baseStart_1272009 baseEnd_1272009 := by
    simpa [prefixWord, tailWord_1272009, baseEnd_1272009] using wordTrace_append hprefix tailTrace_1272009
  have hstable : (prefixWord ++ tailWord_1272009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272009).length < 2 ^ (prefixWord ++ tailWord_1272009).sum := by decide
  have hdescent : baseEnd_1272009 < baseStart_1272009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272099 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 3]
def baseStart_1272099 : Nat := 118140960795 + 1272099 * 2 ^ 59
def prefixEnd_1272099 : Nat := 4983230072969 + 3 ^ 40 * 1272099 * 2
def baseEnd_1272099 : Nat := 653198227103923640512229

theorem tailTrace_1272099 : CollatzResearch.WordTrace tailWord_1272099 prefixEnd_1272099 653198227103923640512229 := by
  unfold tailWord_1272099
  simp only [CollatzResearch.WordTrace]
  refine ⟨46397262218410055057579351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30931508145606703371719567 46397262218410055057579351)
  ·
    refine ⟨69595893327615082586369027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46397262218410055057579351 69595893327615082586369027)
    ·
      refine ⟨104393839991422623879553541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69595893327615082586369027 104393839991422623879553541)
      ·
        refine ⟨19573844998391741977416289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104393839991422623879553541 19573844998391741977416289)
        ·
          refine ⟨14680383748793806483062217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19573844998391741977416289 14680383748793806483062217)
          ·
            refine ⟨11010287811595354862296663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14680383748793806483062217 11010287811595354862296663)
            ·
              refine ⟨16515431717393032293444995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11010287811595354862296663 16515431717393032293444995)
              ·
                refine ⟨24773147576089548440167493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16515431717393032293444995 24773147576089548440167493)
                ·
                  refine ⟨4644965170516790332531405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24773147576089548440167493 4644965170516790332531405)
                  ·
                    refine ⟨1741861938943796374699277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4644965170516790332531405 1741861938943796374699277)
                    ·
                      refine ⟨653198227103923640512229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1741861938943796374699277 653198227103923640512229)
                      ·
                        rfl

theorem cell23_1272099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_1272099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272099 prefixEnd_1272099 := by exact prefixLift 1272099
  have htrace : WordTrace (prefixWord ++ tailWord_1272099) baseStart_1272099 baseEnd_1272099 := by
    simpa [prefixWord, tailWord_1272099, baseEnd_1272099] using wordTrace_append hprefix tailTrace_1272099
  have hstable : (prefixWord ++ tailWord_1272099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272099).length < 2 ^ (prefixWord ++ tailWord_1272099).sum := by decide
  have hdescent : baseEnd_1272099 < baseStart_1272099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272100 : List Nat := [2, 3, 1, 3, 1, 2, 3, 2, 2, 2, 2]
def baseStart_1272100 : Nat := 118140960795 + 1272100 * 2 ^ 59
def prefixEnd_1272100 : Nat := 4983230072969 + 3 ^ 40 * 1272100 * 2
def baseEnd_1272100 : Nat := 653198740584578136599725

theorem tailTrace_1272100 : CollatzResearch.WordTrace tailWord_1272100 prefixEnd_1272100 653198740584578136599725 := by
  unfold tailWord_1272100
  simp only [CollatzResearch.WordTrace]
  refine ⟨23198649345703216114182877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30931532460937621485577169 23198649345703216114182877)
  ·
    refine ⟨8699493504638706042818579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23198649345703216114182877 8699493504638706042818579)
    ·
      refine ⟨13049240256958059064227869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8699493504638706042818579 13049240256958059064227869)
      ·
        refine ⟨4893465096359272149085451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13049240256958059064227869 4893465096359272149085451)
        ·
          refine ⟨7340197644538908223628177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893465096359272149085451 7340197644538908223628177)
          ·
            refine ⟨5505148233404181167721133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7340197644538908223628177 5505148233404181167721133)
            ·
              refine ⟨2064430587526567937895425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5505148233404181167721133 2064430587526567937895425)
              ·
                refine ⟨1548322940644925953421569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2064430587526567937895425 1548322940644925953421569)
                ·
                  refine ⟨1161242205483694465066177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1548322940644925953421569 1161242205483694465066177)
                  ·
                    refine ⟨870931654112770848799633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1161242205483694465066177 870931654112770848799633)
                    ·
                      refine ⟨653198740584578136599725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870931654112770848799633 653198740584578136599725)
                      ·
                        rfl

theorem cell23_1272100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_1272100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272100 prefixEnd_1272100 := by exact prefixLift 1272100
  have htrace : WordTrace (prefixWord ++ tailWord_1272100) baseStart_1272100 baseEnd_1272100 := by
    simpa [prefixWord, tailWord_1272100, baseEnd_1272100] using wordTrace_append hprefix tailTrace_1272100
  have hstable : (prefixWord ++ tailWord_1272100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272100).length < 2 ^ (prefixWord ++ tailWord_1272100).sum := by decide
  have hdescent : baseEnd_1272100 < baseStart_1272100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272179 : List Nat := [1, 1, 1, 2, 2, 1, 2, 7, 6]
def baseStart_1272179 : Nat := 118140960795 + 1272179 * 2 ^ 59
def prefixEnd_1272179 : Nat := 4983230072969 + 3 ^ 40 * 1272179 * 2
def baseEnd_1272179 : Nat := 72582145061809258612429

theorem tailTrace_1272179 : CollatzResearch.WordTrace tailWord_1272179 prefixEnd_1272179 72582145061809258612429 := by
  unfold tailWord_1272179
  simp only [CollatzResearch.WordTrace]
  refine ⟨46400180058120228720491591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30933453372080152480327727 46400180058120228720491591)
  ·
    refine ⟨69600270087180343080737387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46400180058120228720491591 69600270087180343080737387)
    ·
      refine ⟨104400405130770514621106081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69600270087180343080737387 104400405130770514621106081)
      ·
        refine ⟨78300303848077885965829561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104400405130770514621106081 78300303848077885965829561)
        ·
          refine ⟨58725227886058414474372171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78300303848077885965829561 58725227886058414474372171)
          ·
            refine ⟨88087841829087621711558257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58725227886058414474372171 88087841829087621711558257)
            ·
              refine ⟨66065881371815716283668693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88087841829087621711558257 66065881371815716283668693)
              ·
                refine ⟨1548419094651930850398485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66065881371815716283668693 1548419094651930850398485)
                ·
                  refine ⟨72582145061809258612429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1548419094651930850398485 72582145061809258612429)
                  ·
                    rfl

theorem cell23_1272179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 6].length) (baseStart_1272179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272179 prefixEnd_1272179 := by exact prefixLift 1272179
  have htrace : WordTrace (prefixWord ++ tailWord_1272179) baseStart_1272179 baseEnd_1272179 := by
    simpa [prefixWord, tailWord_1272179, baseEnd_1272179] using wordTrace_append hprefix tailTrace_1272179
  have hstable : (prefixWord ++ tailWord_1272179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272179).length < 2 ^ (prefixWord ++ tailWord_1272179).sum := by decide
  have hdescent : baseEnd_1272179 < baseStart_1272179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272193 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1272193 : Nat := 118140960795 + 1272193 * 2 ^ 59
def prefixEnd_1272193 : Nat := 4983230072969 + 3 ^ 40 * 1272193 * 2
def baseEnd_1272193 : Nat := 653246494285446272736797

theorem tailTrace_1272193 : CollatzResearch.WordTrace tailWord_1272193 prefixEnd_1272193 653246494285446272736797 := by
  unfold tailWord_1272193
  simp only [CollatzResearch.WordTrace]
  refine ⟨46400690680069509111501233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30933793786713006074334155 46400690680069509111501233)
  ·
    refine ⟨34800518010052131833625925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46400690680069509111501233 34800518010052131833625925)
    ·
      refine ⟨6525097126884774718804861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34800518010052131833625925 6525097126884774718804861)
      ·
        refine ⟨2446911422581790519551823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6525097126884774718804861 2446911422581790519551823)
        ·
          refine ⟨3670367133872685779327735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446911422581790519551823 3670367133872685779327735)
          ·
            refine ⟨5505550700809028668991603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3670367133872685779327735 5505550700809028668991603)
            ·
              refine ⟨8258326051213543003487405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5505550700809028668991603 8258326051213543003487405)
              ·
                refine ⟨3096872269205078626307777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8258326051213543003487405 3096872269205078626307777)
                ·
                  refine ⟨2322654201903808969730833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3096872269205078626307777 2322654201903808969730833)
                  ·
                    refine ⟨1741990651427856727298125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2322654201903808969730833 1741990651427856727298125)
                    ·
                      refine ⟨653246494285446272736797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1741990651427856727298125 653246494285446272736797)
                      ·
                        rfl

theorem cell23_1272193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1272193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272193 prefixEnd_1272193 := by exact prefixLift 1272193
  have htrace : WordTrace (prefixWord ++ tailWord_1272193) baseStart_1272193 baseEnd_1272193 := by
    simpa [prefixWord, tailWord_1272193, baseEnd_1272193] using wordTrace_append hprefix tailTrace_1272193
  have hstable : (prefixWord ++ tailWord_1272193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272193).length < 2 ^ (prefixWord ++ tailWord_1272193).sum := by decide
  have hdescent : baseEnd_1272193 < baseStart_1272193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272209 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 7, 5]
def baseStart_1272209 : Nat := 118140960795 + 1272209 * 2 ^ 59
def prefixEnd_1272209 : Nat := 4983230072969 + 3 ^ 40 * 1272209 * 2
def baseEnd_1272209 : Nat := 217751569991972736712241

theorem tailTrace_1272209 : CollatzResearch.WordTrace tailWord_1272209 prefixEnd_1272209 217751569991972736712241 := by
  unfold tailWord_1272209
  simp only [CollatzResearch.WordTrace]
  refine ⟨46401274248011543844083681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30934182832007695896055787 46401274248011543844083681)
  ·
    refine ⟨34800955686008657883062761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46401274248011543844083681 34800955686008657883062761)
    ·
      refine ⟨26100716764506493412297071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34800955686008657883062761 26100716764506493412297071)
      ·
        refine ⟨39151075146759740118445607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26100716764506493412297071 39151075146759740118445607)
        ·
          refine ⟨58726612720139610177668411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39151075146759740118445607 58726612720139610177668411)
          ·
            refine ⟨88089919080209415266502617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58726612720139610177668411 88089919080209415266502617)
            ·
              refine ⟨66067439310157061449876963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88089919080209415266502617 66067439310157061449876963)
              ·
                refine ⟨99101158965235592174815445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66067439310157061449876963 99101158965235592174815445)
                ·
                  refine ⟨2322683413247709191597237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 99101158965235592174815445 2322683413247709191597237)
                  ·
                    refine ⟨217751569991972736712241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2322683413247709191597237 217751569991972736712241)
                    ·
                      rfl

theorem cell23_1272209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_1272209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272209 prefixEnd_1272209 := by exact prefixLift 1272209
  have htrace : WordTrace (prefixWord ++ tailWord_1272209) baseStart_1272209 baseEnd_1272209 := by
    simpa [prefixWord, tailWord_1272209, baseEnd_1272209] using wordTrace_append hprefix tailTrace_1272209
  have hstable : (prefixWord ++ tailWord_1272209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272209).length < 2 ^ (prefixWord ++ tailWord_1272209).sum := by decide
  have hdescent : baseEnd_1272209 < baseStart_1272209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272223 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 3, 1, 3]
def baseStart_1272223 : Nat := 118140960795 + 1272223 * 2 ^ 59
def prefixEnd_1272223 : Nat := 4983230072969 + 3 ^ 40 * 1272223 * 2
def baseEnd_1272223 : Nat := 653261898705081155361659

theorem tailTrace_1272223 : CollatzResearch.WordTrace tailWord_1272223 prefixEnd_1272223 653261898705081155361659 := by
  unfold tailWord_1272223
  simp only [CollatzResearch.WordTrace]
  refine ⟨46401784869960824235093323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30934523246640549490062215 46401784869960824235093323)
  ·
    refine ⟨69602677304941236352639985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46401784869960824235093323 69602677304941236352639985)
    ·
      refine ⟨52202007978705927264479989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69602677304941236352639985 52202007978705927264479989)
      ·
        refine ⟨4893938248003680681044999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52202007978705927264479989 4893938248003680681044999)
        ·
          refine ⟨7340907372005521021567499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893938248003680681044999 7340907372005521021567499)
          ·
            refine ⟨11011361058008281532351249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7340907372005521021567499 11011361058008281532351249)
            ·
              refine ⟨8258520793506211149263437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11011361058008281532351249 8258520793506211149263437)
              ·
                refine ⟨3096945297564829180973789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8258520793506211149263437 3096945297564829180973789)
                ·
                  refine ⟨1161354486586810942865171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3096945297564829180973789 1161354486586810942865171)
                  ·
                    refine ⟨1742031729880216414297757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1161354486586810942865171 1742031729880216414297757)
                    ·
                      refine ⟨653261898705081155361659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1742031729880216414297757 653261898705081155361659)
                      ·
                        rfl

theorem cell23_1272223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_1272223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272223 prefixEnd_1272223 := by exact prefixLift 1272223
  have htrace : WordTrace (prefixWord ++ tailWord_1272223) baseStart_1272223 baseEnd_1272223 := by
    simpa [prefixWord, tailWord_1272223, baseEnd_1272223] using wordTrace_append hprefix tailTrace_1272223
  have hstable : (prefixWord ++ tailWord_1272223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272223).length < 2 ^ (prefixWord ++ tailWord_1272223).sum := by decide
  have hdescent : baseEnd_1272223 < baseStart_1272223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272226 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_1272226 : Nat := 118140960795 + 1272226 * 2 ^ 59
def prefixEnd_1272226 : Nat := 4983230072969 + 3 ^ 40 * 1272226 * 2
def baseEnd_1272226 : Nat := 217754479715681547874715

theorem tailTrace_1272226 : CollatzResearch.WordTrace tailWord_1272226 prefixEnd_1272226 217754479715681547874715 := by
  unfold tailWord_1272226
  simp only [CollatzResearch.WordTrace]
  refine ⟨11600473572237488936863133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30934596192633303831635021 11600473572237488936863133)
  ·
    refine ⟨4350177589589058351323675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11600473572237488936863133 4350177589589058351323675)
    ·
      refine ⟨6525266384383587526985513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4350177589589058351323675 6525266384383587526985513)
      ·
        refine ⟨4893949788287690645239135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6525266384383587526985513 4893949788287690645239135)
        ·
          refine ⟨7340924682431535967858703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893949788287690645239135 7340924682431535967858703)
          ·
            refine ⟨11011387023647303951788055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7340924682431535967858703 11011387023647303951788055)
            ·
              refine ⟨16517080535470955927682083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11011387023647303951788055 16517080535470955927682083)
              ·
                refine ⟨24775620803206433891523125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16517080535470955927682083 24775620803206433891523125)
                ·
                  refine ⟨2322714450300603177330293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24775620803206433891523125 2322714450300603177330293)
                  ·
                    refine ⟨217754479715681547874715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2322714450300603177330293 217754479715681547874715)
                    ·
                      rfl

theorem cell23_1272226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_1272226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272226 prefixEnd_1272226 := by exact prefixLift 1272226
  have htrace : WordTrace (prefixWord ++ tailWord_1272226) baseStart_1272226 baseEnd_1272226 := by
    simpa [prefixWord, tailWord_1272226, baseEnd_1272226] using wordTrace_append hprefix tailTrace_1272226
  have hstable : (prefixWord ++ tailWord_1272226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272226).length < 2 ^ (prefixWord ++ tailWord_1272226).sum := by decide
  have hdescent : baseEnd_1272226 < baseStart_1272226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272244 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1272244 : Nat := 118140960795 + 1272244 * 2 ^ 59
def prefixEnd_1272244 : Nat := 4983230072969 + 3 ^ 40 * 1272244 * 2
def baseEnd_1272244 : Nat := 653272681798825573199063

theorem tailTrace_1272244 : CollatzResearch.WordTrace tailWord_1272244 prefixEnd_1272244 653272681798825573199063 := by
  unfold tailWord_1272244
  simp only [CollatzResearch.WordTrace]
  refine ⟨23201275401442372410803893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30935033868589829881071857 23201275401442372410803893)
  ·
    refine ⟨2175119568885222413512865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23201275401442372410803893 2175119568885222413512865)
    ·
      refine ⟨1631339676663916810134649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2175119568885222413512865 1631339676663916810134649)
      ·
        refine ⟨1223504757497937607600987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1631339676663916810134649 1223504757497937607600987)
        ·
          refine ⟨1835257136246906411401481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223504757497937607600987 1835257136246906411401481)
          ·
            refine ⟨1376442852185179808551111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1835257136246906411401481 1376442852185179808551111)
            ·
              refine ⟨2064664278277769712826667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376442852185179808551111 2064664278277769712826667)
              ·
                refine ⟨3096996417416654569240001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2064664278277769712826667 3096996417416654569240001)
                ·
                  refine ⟨2322747313062490926930001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3096996417416654569240001 2322747313062490926930001)
                  ·
                    refine ⟨1742060484796868195197501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2322747313062490926930001 1742060484796868195197501)
                    ·
                      refine ⟨653272681798825573199063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1742060484796868195197501 653272681798825573199063)
                      ·
                        rfl

theorem cell23_1272244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1272244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272244 prefixEnd_1272244 := by exact prefixLift 1272244
  have htrace : WordTrace (prefixWord ++ tailWord_1272244) baseStart_1272244 baseEnd_1272244 := by
    simpa [prefixWord, tailWord_1272244, baseEnd_1272244] using wordTrace_append hprefix tailTrace_1272244
  have hstable : (prefixWord ++ tailWord_1272244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272244).length < 2 ^ (prefixWord ++ tailWord_1272244).sum := by decide
  have hdescent : baseEnd_1272244 < baseStart_1272244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272256 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 4, 4]
def baseStart_1272256 : Nat := 118140960795 + 1272256 * 2 ^ 59
def prefixEnd_1272256 : Nat := 4983230072969 + 3 ^ 40 * 1272256 * 2
def baseEnd_1272256 : Nat := 217759614522226508749669

theorem tailTrace_1272256 : CollatzResearch.WordTrace tailWord_1272256 prefixEnd_1272256 217759614522226508749669 := by
  unfold tailWord_1272256
  simp only [CollatzResearch.WordTrace]
  refine ⟨23201494239420635435522311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30935325652560847247363081 23201494239420635435522311)
  ·
    refine ⟨34802241359130953153283467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23201494239420635435522311 34802241359130953153283467)
    ·
      refine ⟨52203362038696429729925201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34802241359130953153283467 52203362038696429729925201)
      ·
        refine ⟨39152521529022322297443901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52203362038696429729925201 39152521529022322297443901)
        ·
          refine ⟨14682195573383370861541463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39152521529022322297443901 14682195573383370861541463)
          ·
            refine ⟨22023293360075056292312195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14682195573383370861541463 22023293360075056292312195)
            ·
              refine ⟨33034940040112584438468293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22023293360075056292312195 33034940040112584438468293)
              ·
                refine ⟨6194051257521109582212805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33034940040112584438468293 6194051257521109582212805)
                ·
                  refine ⟨1161384610785208046664901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6194051257521109582212805 1161384610785208046664901)
                  ·
                    refine ⟨217759614522226508749669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1161384610785208046664901 217759614522226508749669)
                    ·
                      rfl

theorem cell23_1272256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 4, 4].length) (baseStart_1272256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272256 prefixEnd_1272256 := by exact prefixLift 1272256
  have htrace : WordTrace (prefixWord ++ tailWord_1272256) baseStart_1272256 baseEnd_1272256 := by
    simpa [prefixWord, tailWord_1272256, baseEnd_1272256] using wordTrace_append hprefix tailTrace_1272256
  have hstable : (prefixWord ++ tailWord_1272256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272256).length < 2 ^ (prefixWord ++ tailWord_1272256).sum := by decide
  have hdescent : baseEnd_1272256 < baseStart_1272256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272259 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 6]
def baseStart_1272259 : Nat := 118140960795 + 1272259 * 2 ^ 59
def prefixEnd_1272259 : Nat := 4983230072969 + 3 ^ 40 * 1272259 * 2
def baseEnd_1272259 : Nat := 653280384008643014511493

theorem tailTrace_1272259 : CollatzResearch.WordTrace tailWord_1272259 prefixEnd_1272259 653280384008643014511493 := by
  unfold tailWord_1272259
  simp only [CollatzResearch.WordTrace]
  refine ⟨46403097897830402383403831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30935398598553601588935887 46403097897830402383403831)
  ·
    refine ⟨69604646846745603575105747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46403097897830402383403831 69604646846745603575105747)
    ·
      refine ⟨104406970270118405362658621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69604646846745603575105747 104406970270118405362658621)
      ·
        refine ⟨39152613851294402010996983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104406970270118405362658621 39152613851294402010996983)
        ·
          refine ⟨58728920776941603016495475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39152613851294402010996983 58728920776941603016495475)
          ·
            refine ⟨88093381165412404524743213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58728920776941603016495475 88093381165412404524743213)
            ·
              refine ⟨33035017937029651696778705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88093381165412404524743213 33035017937029651696778705)
              ·
                refine ⟨24776263452772238772584029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33035017937029651696778705 24776263452772238772584029)
                ·
                  refine ⟨9291098794789589539719011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24776263452772238772584029 9291098794789589539719011)
                  ·
                    refine ⟨13936648192184384309578517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9291098794789589539719011 13936648192184384309578517)
                    ·
                      refine ⟨653280384008643014511493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13936648192184384309578517 653280384008643014511493)
                      ·
                        rfl

theorem cell23_1272259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_1272259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272259 prefixEnd_1272259 := by exact prefixLift 1272259
  have htrace : WordTrace (prefixWord ++ tailWord_1272259) baseStart_1272259 baseEnd_1272259 := by
    simpa [prefixWord, tailWord_1272259, baseEnd_1272259] using wordTrace_append hprefix tailTrace_1272259
  have hstable : (prefixWord ++ tailWord_1272259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272259).length < 2 ^ (prefixWord ++ tailWord_1272259).sum := by decide
  have hdescent : baseEnd_1272259 < baseStart_1272259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272260 : List Nat := [2, 3, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_1272260 : Nat := 118140960795 + 1272260 * 2 ^ 59
def prefixEnd_1272260 : Nat := 4983230072969 + 3 ^ 40 * 1272260 * 2
def baseEnd_1272260 : Nat := 217760299163099170199663

theorem tailTrace_1272260 : CollatzResearch.WordTrace tailWord_1272260 prefixEnd_1272260 217760299163099170199663 := by
  unfold tailWord_1272260
  simp only [CollatzResearch.WordTrace]
  refine ⟨23201567185413389777095117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30935422913884519702793489 23201567185413389777095117)
  ·
    refine ⟨8700587694530021166410669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23201567185413389777095117 8700587694530021166410669)
    ·
      refine ⟨3262720385448757937404001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8700587694530021166410669 3262720385448757937404001)
      ·
        refine ⟨2447040289086568453053001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3262720385448757937404001 2447040289086568453053001)
        ·
          refine ⟨1835280216814926339789751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2447040289086568453053001 1835280216814926339789751)
          ·
            refine ⟨2752920325222389509684627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835280216814926339789751 2752920325222389509684627)
            ·
              refine ⟨4129380487833584264526941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2752920325222389509684627 4129380487833584264526941)
              ·
                refine ⟨1548517682937594099197603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4129380487833584264526941 1548517682937594099197603)
                ·
                  refine ⟨2322776524406391148796405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548517682937594099197603 2322776524406391148796405)
                  ·
                    refine ⟨217760299163099170199663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2322776524406391148796405 217760299163099170199663)
                    ·
                      rfl

theorem cell23_1272260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_1272260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272260 prefixEnd_1272260 := by exact prefixLift 1272260
  have htrace : WordTrace (prefixWord ++ tailWord_1272260) baseStart_1272260 baseEnd_1272260 := by
    simpa [prefixWord, tailWord_1272260, baseEnd_1272260] using wordTrace_append hprefix tailTrace_1272260
  have hstable : (prefixWord ++ tailWord_1272260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272260).length < 2 ^ (prefixWord ++ tailWord_1272260).sum := by decide
  have hdescent : baseEnd_1272260 < baseStart_1272260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272263 : List Nat := [1, 1, 4, 1, 1, 5, 1, 3, 1, 1, 4]
def baseStart_1272263 : Nat := 118140960795 + 1272263 * 2 ^ 59
def prefixEnd_1272263 : Nat := 4983230072969 + 3 ^ 40 * 1272263 * 2
def baseEnd_1272263 : Nat := 653282437931260998861475

theorem tailTrace_1272263 : CollatzResearch.WordTrace tailWord_1272263 prefixEnd_1272263 653282437931260998861475 := by
  unfold tailWord_1272263
  simp only [CollatzResearch.WordTrace]
  refine ⟨46403243789815911066549443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30935495859877274044366295 46403243789815911066549443)
  ·
    refine ⟨69604865684723866599824165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46403243789815911066549443 69604865684723866599824165)
    ·
      refine ⟨13050912315885724987467031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69604865684723866599824165 13050912315885724987467031)
      ·
        refine ⟨19576368473828587481200547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13050912315885724987467031 19576368473828587481200547)
        ·
          refine ⟨29364552710742881221800821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19576368473828587481200547 29364552710742881221800821)
          ·
            refine ⟨2752926816632145114543827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29364552710742881221800821 2752926816632145114543827)
            ·
              refine ⟨4129390224948217671815741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2752926816632145114543827 4129390224948217671815741)
              ·
                refine ⟨1548521334355581626930903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4129390224948217671815741 1548521334355581626930903)
                ·
                  refine ⟨2322782001533372440396355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548521334355581626930903 2322782001533372440396355)
                  ·
                    refine ⟨3484173002300058660594533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2322782001533372440396355 3484173002300058660594533)
                    ·
                      refine ⟨653282437931260998861475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3484173002300058660594533 653282437931260998861475)
                      ·
                        rfl

theorem cell23_1272263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_1272263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272263 prefixEnd_1272263 := by exact prefixLift 1272263
  have htrace : WordTrace (prefixWord ++ tailWord_1272263) baseStart_1272263 baseEnd_1272263 := by
    simpa [prefixWord, tailWord_1272263, baseEnd_1272263] using wordTrace_append hprefix tailTrace_1272263
  have hstable : (prefixWord ++ tailWord_1272263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272263).length < 2 ^ (prefixWord ++ tailWord_1272263).sum := by decide
  have hdescent : baseEnd_1272263 < baseStart_1272263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272266 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_1272266 : Nat := 118140960795 + 1272266 * 2 ^ 59
def prefixEnd_1272266 : Nat := 4983230072969 + 3 ^ 40 * 1272266 * 2
def baseEnd_1272266 : Nat := 653283978373224487123961

theorem tailTrace_1272266 : CollatzResearch.WordTrace tailWord_1272266 prefixEnd_1272266 653283978373224487123961 := by
  unfold tailWord_1272266
  simp only [CollatzResearch.WordTrace]
  refine ⟨11600838302201260644727163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30935568805870028385939101 11600838302201260644727163)
  ·
    refine ⟨17401257453301890967090745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11600838302201260644727163 17401257453301890967090745)
    ·
      refine ⟨13050943089976418225318059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17401257453301890967090745 13050943089976418225318059)
      ·
        refine ⟨19576414634964627337977089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13050943089976418225318059 19576414634964627337977089)
        ·
          refine ⟨14682310976223470503482817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19576414634964627337977089 14682310976223470503482817)
          ·
            refine ⟨11011733232167602877612113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14682310976223470503482817 11011733232167602877612113)
            ·
              refine ⟨8258799924125702158209085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11011733232167602877612113 8258799924125702158209085)
              ·
                refine ⟨3097049971547138309328407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8258799924125702158209085 3097049971547138309328407)
                ·
                  refine ⟨4645574957320707463992611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3097049971547138309328407 4645574957320707463992611)
                  ·
                    refine ⟨6968362435981061195988917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4645574957320707463992611 6968362435981061195988917)
                    ·
                      refine ⟨653283978373224487123961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6968362435981061195988917 653283978373224487123961)
                      ·
                        rfl

theorem cell23_1272266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_1272266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272266 prefixEnd_1272266 := by exact prefixLift 1272266
  have htrace : WordTrace (prefixWord ++ tailWord_1272266) baseStart_1272266 baseEnd_1272266 := by
    simpa [prefixWord, tailWord_1272266, baseEnd_1272266] using wordTrace_append hprefix tailTrace_1272266
  have hstable : (prefixWord ++ tailWord_1272266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272266).length < 2 ^ (prefixWord ++ tailWord_1272266).sum := by decide
  have hdescent : baseEnd_1272266 < baseStart_1272266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272279 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_1272279 : Nat := 118140960795 + 1272279 * 2 ^ 59
def prefixEnd_1272279 : Nat := 4983230072969 + 3 ^ 40 * 1272279 * 2
def baseEnd_1272279 : Nat := 653290653621732936261401

theorem tailTrace_1272279 : CollatzResearch.WordTrace tailWord_1272279 prefixEnd_1272279 653290653621732936261401 := by
  unfold tailWord_1272279
  simp only [CollatzResearch.WordTrace]
  refine ⟨46403827357757945799131891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30935884905171963866087927 46403827357757945799131891)
  ·
    refine ⟨69605741036636918698697837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46403827357757945799131891 69605741036636918698697837)
    ·
      refine ⟨26102152888738844512011689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69605741036636918698697837 26102152888738844512011689)
      ·
        refine ⟨19576614666554133384008767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26102152888738844512011689 19576614666554133384008767)
        ·
          refine ⟨29364921999831200076013151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19576614666554133384008767 29364921999831200076013151)
          ·
            refine ⟨44047382999746800114019727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29364921999831200076013151 44047382999746800114019727)
            ·
              refine ⟨66071074499620200171029591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44047382999746800114019727 66071074499620200171029591)
              ·
                refine ⟨99106611749430300256544387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66071074499620200171029591 99106611749430300256544387)
                ·
                  refine ⟨148659917624145450384816581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99106611749430300256544387 148659917624145450384816581)
                  ·
                    refine ⟨27873734554527271947153109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148659917624145450384816581 27873734554527271947153109)
                    ·
                      refine ⟨653290653621732936261401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27873734554527271947153109 653290653621732936261401)
                      ·
                        rfl

theorem cell23_1272279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_1272279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272279 prefixEnd_1272279 := by exact prefixLift 1272279
  have htrace : WordTrace (prefixWord ++ tailWord_1272279) baseStart_1272279 baseEnd_1272279 := by
    simpa [prefixWord, tailWord_1272279, baseEnd_1272279] using wordTrace_append hprefix tailTrace_1272279
  have hstable : (prefixWord ++ tailWord_1272279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272279).length < 2 ^ (prefixWord ++ tailWord_1272279).sum := by decide
  have hdescent : baseEnd_1272279 < baseStart_1272279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272293 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1272293 : Nat := 118140960795 + 1272293 * 2 ^ 59
def prefixEnd_1272293 : Nat := 4983230072969 + 3 ^ 40 * 1272293 * 2
def baseEnd_1272293 : Nat := 653297842350895881486337

theorem tailTrace_1272293 : CollatzResearch.WordTrace tailWord_1272293 prefixEnd_1272293 653297842350895881486337 := by
  unfold tailWord_1272293
  simp only [CollatzResearch.WordTrace]
  refine ⟨46404337979707226190141533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30936225319804817460094355 46404337979707226190141533)
  ·
    refine ⟨17401626742390209821303075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46404337979707226190141533 17401626742390209821303075)
    ·
      refine ⟨26102440113585314731954613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17401626742390209821303075 26102440113585314731954613)
      ·
        refine ⟨2447103760648623256120745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26102440113585314731954613 2447103760648623256120745)
        ·
          refine ⟨1835327820486467442090559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2447103760648623256120745 1835327820486467442090559)
          ·
            refine ⟨2752991730729701163135839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835327820486467442090559 2752991730729701163135839)
            ·
              refine ⟨4129487596094551744703759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2752991730729701163135839 4129487596094551744703759)
              ·
                refine ⟨6194231394141827617055639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4129487596094551744703759 6194231394141827617055639)
                ·
                  refine ⟨9291347091212741425583459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6194231394141827617055639 9291347091212741425583459)
                  ·
                    refine ⟨13937020636819112138375189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9291347091212741425583459 13937020636819112138375189)
                    ·
                      refine ⟨653297842350895881486337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13937020636819112138375189 653297842350895881486337)
                      ·
                        rfl

theorem cell23_1272293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1272293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272293 prefixEnd_1272293 := by exact prefixLift 1272293
  have htrace : WordTrace (prefixWord ++ tailWord_1272293) baseStart_1272293 baseEnd_1272293 := by
    simpa [prefixWord, tailWord_1272293, baseEnd_1272293] using wordTrace_append hprefix tailTrace_1272293
  have hstable : (prefixWord ++ tailWord_1272293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272293).length < 2 ^ (prefixWord ++ tailWord_1272293).sum := by decide
  have hdescent : baseEnd_1272293 < baseStart_1272293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272313 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 4, 1, 3]
def baseStart_1272313 : Nat := 118140960795 + 1272313 * 2 ^ 59
def prefixEnd_1272313 : Nat := 4983230072969 + 3 ^ 40 * 1272313 * 2
def baseEnd_1272313 : Nat := 653308111963985803236245

theorem tailTrace_1272313 : CollatzResearch.WordTrace tailWord_1272313 prefixEnd_1272313 653308111963985803236245 := by
  unfold tailWord_1272313
  simp only [CollatzResearch.WordTrace]
  refine ⟨46405067439634769605869593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30936711626423179737246395 46405067439634769605869593)
  ·
    refine ⟨34803800579726077204402195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46405067439634769605869593 34803800579726077204402195)
    ·
      refine ⟨52205700869589115806603293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34803800579726077204402195 52205700869589115806603293)
      ·
        refine ⟨19577137826095918427476235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52205700869589115806603293 19577137826095918427476235)
        ·
          refine ⟨29365706739143877641214353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19577137826095918427476235 29365706739143877641214353)
          ·
            refine ⟨22024280054357908230910765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29365706739143877641214353 22024280054357908230910765)
            ·
              refine ⟨8259105020384215586591537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22024280054357908230910765 8259105020384215586591537)
              ·
                refine ⟨6194328765288161689943653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8259105020384215586591537 6194328765288161689943653)
                ·
                  refine ⟨1161436643491530316864435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6194328765288161689943653 1161436643491530316864435)
                  ·
                    refine ⟨1742154965237295475296653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1161436643491530316864435 1742154965237295475296653)
                    ·
                      refine ⟨653308111963985803236245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1742154965237295475296653 653308111963985803236245)
                      ·
                        rfl

theorem cell23_1272313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_1272313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272313 prefixEnd_1272313 := by exact prefixLift 1272313
  have htrace : WordTrace (prefixWord ++ tailWord_1272313) baseStart_1272313 baseEnd_1272313 := by
    simpa [prefixWord, tailWord_1272313, baseEnd_1272313] using wordTrace_append hprefix tailTrace_1272313
  have hstable : (prefixWord ++ tailWord_1272313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272313).length < 2 ^ (prefixWord ++ tailWord_1272313).sum := by decide
  have hdescent : baseEnd_1272313 < baseStart_1272313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272330 : List Nat := [3, 1, 2, 2, 2, 1, 2, 4, 2, 1, 3]
def baseStart_1272330 : Nat := 118140960795 + 1272330 * 2 ^ 59
def prefixEnd_1272330 : Nat := 4983230072969 + 3 ^ 40 * 1272330 * 2
def baseEnd_1272330 : Nat := 653316841135112236723667

theorem tailTrace_1272330 : CollatzResearch.WordTrace tailWord_1272330 prefixEnd_1272330 653316841135112236723667 := by
  unfold tailWord_1272330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11601421870143295377309611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30937124987048787672825629 11601421870143295377309611)
  ·
    refine ⟨17402132805214943065964417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11601421870143295377309611 17402132805214943065964417)
    ·
      refine ⟨13051599603911207299473313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17402132805214943065964417 13051599603911207299473313)
      ·
        refine ⟨9788699702933405474604985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13051599603911207299473313 9788699702933405474604985)
        ·
          refine ⟨7341524777200054105953739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9788699702933405474604985 7341524777200054105953739)
          ·
            refine ⟨11012287165800081158930609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7341524777200054105953739 11012287165800081158930609)
            ·
              refine ⟨8259215374350060869197957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11012287165800081158930609 8259215374350060869197957)
              ·
                refine ⟨1548602882690636412974617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8259215374350060869197957 1548602882690636412974617)
                ·
                  refine ⟨1161452162017977309730963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1548602882690636412974617 1161452162017977309730963)
                  ·
                    refine ⟨1742178243026965964596445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1161452162017977309730963 1742178243026965964596445)
                    ·
                      refine ⟨653316841135112236723667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1742178243026965964596445 653316841135112236723667)
                      ·
                        rfl

theorem cell23_1272330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_1272330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272330 prefixEnd_1272330 := by exact prefixLift 1272330
  have htrace : WordTrace (prefixWord ++ tailWord_1272330) baseStart_1272330 baseEnd_1272330 := by
    simpa [prefixWord, tailWord_1272330, baseEnd_1272330] using wordTrace_append hprefix tailTrace_1272330
  have hstable : (prefixWord ++ tailWord_1272330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272330).length < 2 ^ (prefixWord ++ tailWord_1272330).sum := by decide
  have hdescent : baseEnd_1272330 < baseStart_1272330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272346 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 2, 6]
def baseStart_1272346 : Nat := 118140960795 + 1272346 * 2 ^ 59
def prefixEnd_1272346 : Nat := 4983230072969 + 3 ^ 40 * 1272346 * 2
def baseEnd_1272346 : Nat := 217775018941861391374531

theorem tailTrace_1272346 : CollatzResearch.WordTrace tailWord_1272346 prefixEnd_1272346 217775018941861391374531 := by
  unfold tailWord_1272346
  simp only [CollatzResearch.WordTrace]
  refine ⟨11601567762128804060455223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30937514032343477494547261 11601567762128804060455223)
  ·
    refine ⟨17402351643193206090682835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11601567762128804060455223 17402351643193206090682835)
    ·
      refine ⟨26103527464789809136024253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17402351643193206090682835 26103527464789809136024253)
      ·
        refine ⟨9788822799296178426009095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26103527464789809136024253 9788822799296178426009095)
        ·
          refine ⟨14683234198944267639013643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9788822799296178426009095 14683234198944267639013643)
          ·
            refine ⟨22024851298416401458520465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14683234198944267639013643 22024851298416401458520465)
            ·
              refine ⟨16518638473812301093890349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22024851298416401458520465 16518638473812301093890349)
              ·
                refine ⟨6194489427679612910208881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16518638473812301093890349 6194489427679612910208881)
                ·
                  refine ⟨4645867070759709682656661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6194489427679612910208881 4645867070759709682656661)
                  ·
                    refine ⟨217775018941861391374531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4645867070759709682656661 217775018941861391374531)
                    ·
                      rfl

theorem cell23_1272346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_1272346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272346 prefixEnd_1272346 := by exact prefixLift 1272346
  have htrace : WordTrace (prefixWord ++ tailWord_1272346) baseStart_1272346 baseEnd_1272346 := by
    simpa [prefixWord, tailWord_1272346, baseEnd_1272346] using wordTrace_append hprefix tailTrace_1272346
  have hstable : (prefixWord ++ tailWord_1272346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272346).length < 2 ^ (prefixWord ++ tailWord_1272346).sum := by decide
  have hdescent : baseEnd_1272346 < baseStart_1272346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272370 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2]
def baseStart_1272370 : Nat := 118140960795 + 1272370 * 2 ^ 59
def prefixEnd_1272370 : Nat := 4983230072969 + 3 ^ 40 * 1272370 * 2
def baseEnd_1272370 : Nat := 653337380361292080223483

theorem tailTrace_1272370 : CollatzResearch.WordTrace tailWord_1272370 prefixEnd_1272370 653337380361292080223483 := by
  unfold tailWord_1272370
  simp only [CollatzResearch.WordTrace]
  refine ⟨11601786600107067085173641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30938097600285512227129709 11601786600107067085173641)
  ·
    refine ⟨8701339950080300313880231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11601786600107067085173641 8701339950080300313880231)
    ·
      refine ⟨13052009925120450470820347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8701339950080300313880231 13052009925120450470820347)
      ·
        refine ⟨19578014887680675706230521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13052009925120450470820347 19578014887680675706230521)
        ·
          refine ⟨14683511165760506779672891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19578014887680675706230521 14683511165760506779672891)
          ·
            refine ⟨22025266748640760169509337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14683511165760506779672891 22025266748640760169509337)
            ·
              refine ⟨16518950061480570127132003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22025266748640760169509337 16518950061480570127132003)
              ·
                refine ⟨24778425092220855190698005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16518950061480570127132003 24778425092220855190698005)
                ·
                  refine ⟨1161488676197852587063969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24778425092220855190698005 1161488676197852587063969)
                  ·
                    refine ⟨871116507148389440297977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1161488676197852587063969 871116507148389440297977)
                    ·
                      refine ⟨653337380361292080223483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871116507148389440297977 653337380361292080223483)
                      ·
                        rfl

theorem cell23_1272370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_1272370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272370 prefixEnd_1272370 := by exact prefixLift 1272370
  have htrace : WordTrace (prefixWord ++ tailWord_1272370) baseStart_1272370 baseEnd_1272370 := by
    simpa [prefixWord, tailWord_1272370, baseEnd_1272370] using wordTrace_append hprefix tailTrace_1272370
  have hstable : (prefixWord ++ tailWord_1272370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272370).length < 2 ^ (prefixWord ++ tailWord_1272370).sum := by decide
  have hdescent : baseEnd_1272370 < baseStart_1272370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272416 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 7]
def baseStart_1272416 : Nat := 118140960795 + 1272416 * 2 ^ 59
def prefixEnd_1272416 : Nat := 4983230072969 + 3 ^ 40 * 1272416 * 2
def baseEnd_1272416 : Nat := 653361000471398900248271

theorem tailTrace_1272416 : CollatzResearch.WordTrace tailWord_1272416 prefixEnd_1272416 653361000471398900248271 := by
  unfold tailWord_1272416
  simp only [CollatzResearch.WordTrace]
  refine ⟨23204412079130809098434551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30939216105507745464579401 23204412079130809098434551)
  ·
    refine ⟨34806618118696213647651827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23204412079130809098434551 34806618118696213647651827)
    ·
      refine ⟨52209927178044320471477741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34806618118696213647651827 52209927178044320471477741)
      ·
        refine ⟨19578722691766620176804153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52209927178044320471477741 19578722691766620176804153)
        ·
          refine ⟨14684042018824965132603115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19578722691766620176804153 14684042018824965132603115)
          ·
            refine ⟨22026063028237447698904673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14684042018824965132603115 22026063028237447698904673)
            ·
              refine ⟨16519547271178085774178505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22026063028237447698904673 16519547271178085774178505)
              ·
                refine ⟨12389660453383564330633879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16519547271178085774178505 12389660453383564330633879)
                ·
                  refine ⟨18584490680075346495950819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12389660453383564330633879 18584490680075346495950819)
                  ·
                    refine ⟨27876736020113019743926229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18584490680075346495950819 27876736020113019743926229)
                    ·
                      refine ⟨653361000471398900248271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27876736020113019743926229 653361000471398900248271)
                      ·
                        rfl

theorem cell23_1272416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_1272416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272416 prefixEnd_1272416 := by exact prefixLift 1272416
  have htrace : WordTrace (prefixWord ++ tailWord_1272416) baseStart_1272416 baseEnd_1272416 := by
    simpa [prefixWord, tailWord_1272416, baseEnd_1272416] using wordTrace_append hprefix tailTrace_1272416
  have hstable : (prefixWord ++ tailWord_1272416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272416).length < 2 ^ (prefixWord ++ tailWord_1272416).sum := by decide
  have hdescent : baseEnd_1272416 < baseStart_1272416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272438 : List Nat := [5, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_1272438 : Nat := 118140960795 + 1272438 * 2 ^ 59
def prefixEnd_1272438 : Nat := 4983230072969 + 3 ^ 40 * 1272438 * 2
def baseEnd_1272438 : Nat := 653372297045797814173171

theorem tailTrace_1272438 : CollatzResearch.WordTrace tailWord_1272438 prefixEnd_1272438 653372297045797814173171 := by
  unfold tailWord_1272438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2900601660261369747135623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30939751042787943969446645 2900601660261369747135623)
  ·
    refine ⟨4350902490392054620703435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2900601660261369747135623 4350902490392054620703435)
    ·
      refine ⟨6526353735588081931055153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4350902490392054620703435 6526353735588081931055153)
      ·
        refine ⟨4894765301691061448291365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6526353735588081931055153 4894765301691061448291365)
        ·
          refine ⟨917768494067074021554631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4894765301691061448291365 917768494067074021554631)
          ·
            refine ⟨1376652741100611032331947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917768494067074021554631 1376652741100611032331947)
            ·
              refine ⟨2064979111650916548497921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376652741100611032331947 2064979111650916548497921)
              ·
                refine ⟨1548734333738187411373441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2064979111650916548497921 1548734333738187411373441)
                ·
                  refine ⟨1161550750303640558530081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1548734333738187411373441 1161550750303640558530081)
                  ·
                    refine ⟨871163062727730418897561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1161550750303640558530081 871163062727730418897561)
                    ·
                      refine ⟨653372297045797814173171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871163062727730418897561 653372297045797814173171)
                      ·
                        rfl

theorem cell23_1272438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_1272438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272438 prefixEnd_1272438 := by exact prefixLift 1272438
  have htrace : WordTrace (prefixWord ++ tailWord_1272438) baseStart_1272438 baseEnd_1272438 := by
    simpa [prefixWord, tailWord_1272438, baseEnd_1272438] using wordTrace_append hprefix tailTrace_1272438
  have hstable : (prefixWord ++ tailWord_1272438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272438).length < 2 ^ (prefixWord ++ tailWord_1272438).sum := by decide
  have hdescent : baseEnd_1272438 < baseStart_1272438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272463 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 3]
def baseStart_1272463 : Nat := 118140960795 + 1272463 * 2 ^ 59
def prefixEnd_1272463 : Nat := 4983230072969 + 3 ^ 40 * 1272463 * 2
def baseEnd_1272463 : Nat := 653385134062160216360555

theorem tailTrace_1272463 : CollatzResearch.WordTrace tailWord_1272463 prefixEnd_1272463 653385134062160216360555 := by
  unfold tailWord_1272463
  simp only [CollatzResearch.WordTrace]
  refine ⟨46410538389091345223830043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30940358926060896815886695 46410538389091345223830043)
  ·
    refine ⟨69615807583637017835745065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46410538389091345223830043 69615807583637017835745065)
    ·
      refine ⟨52211855687727763376808799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69615807583637017835745065 52211855687727763376808799)
      ·
        refine ⟨78317783531591645065213199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52211855687727763376808799 78317783531591645065213199)
        ·
          refine ⟨117476675297387467597819799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78317783531591645065213199 117476675297387467597819799)
          ·
            refine ⟨176215012946081201396729699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117476675297387467597819799 176215012946081201396729699)
            ·
              refine ⟨264322519419121802095094549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176215012946081201396729699 264322519419121802095094549)
              ·
                refine ⟨12390118097771334473207557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 264322519419121802095094549 12390118097771334473207557)
                ·
                  refine ⟨2323147143332125213726417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12390118097771334473207557 2323147143332125213726417)
                  ·
                    refine ⟨1742360357499093910294813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2323147143332125213726417 1742360357499093910294813)
                    ·
                      refine ⟨653385134062160216360555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1742360357499093910294813 653385134062160216360555)
                      ·
                        rfl

theorem cell23_1272463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 3].length) (baseStart_1272463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272463 prefixEnd_1272463 := by exact prefixLift 1272463
  have htrace : WordTrace (prefixWord ++ tailWord_1272463) baseStart_1272463 baseEnd_1272463 := by
    simpa [prefixWord, tailWord_1272463, baseEnd_1272463] using wordTrace_append hprefix tailTrace_1272463
  have hstable : (prefixWord ++ tailWord_1272463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272463).length < 2 ^ (prefixWord ++ tailWord_1272463).sum := by decide
  have hdescent : baseEnd_1272463 < baseStart_1272463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272537 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 2, 3, 2]
def baseStart_1272537 : Nat := 118140960795 + 1272537 * 2 ^ 59
def prefixEnd_1272537 : Nat := 4983230072969 + 3 ^ 40 * 1272537 * 2
def baseEnd_1272537 : Nat := 653423131630592926835215

theorem tailTrace_1272537 : CollatzResearch.WordTrace tailWord_1272537 prefixEnd_1272537 653423131630592926835215 := by
  unfold tailWord_1272537
  simp only [CollatzResearch.WordTrace]
  refine ⟨46413237390823255862023865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30942158260548837241349243 46413237390823255862023865)
  ·
    refine ⟨34809928043117441896517899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46413237390823255862023865 34809928043117441896517899)
    ·
      refine ⟨52214892064676162844776849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34809928043117441896517899 52214892064676162844776849)
      ·
        refine ⟨39161169048507122133582637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52214892064676162844776849 39161169048507122133582637)
        ·
          refine ⟨14685438393190170800093489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39161169048507122133582637 14685438393190170800093489)
          ·
            refine ⟨11014078794892628100070117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14685438393190170800093489 11014078794892628100070117)
            ·
              refine ⟨2065139774042367768763147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11014078794892628100070117 2065139774042367768763147)
              ·
                refine ⟨3097709661063551653144721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065139774042367768763147 3097709661063551653144721)
                ·
                  refine ⟨2323282245797663739858541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3097709661063551653144721 2323282245797663739858541)
                  ·
                    refine ⟨871230842174123902446953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2323282245797663739858541 871230842174123902446953)
                    ·
                      refine ⟨653423131630592926835215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871230842174123902446953 653423131630592926835215)
                      ·
                        rfl

theorem cell23_1272537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 3, 2].length) (baseStart_1272537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272537 prefixEnd_1272537 := by exact prefixLift 1272537
  have htrace : WordTrace (prefixWord ++ tailWord_1272537) baseStart_1272537 baseEnd_1272537 := by
    simpa [prefixWord, tailWord_1272537, baseEnd_1272537] using wordTrace_append hprefix tailTrace_1272537
  have hstable : (prefixWord ++ tailWord_1272537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272537).length < 2 ^ (prefixWord ++ tailWord_1272537).sum := by decide
  have hdescent : baseEnd_1272537 < baseStart_1272537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272543 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 3, 6]
def baseStart_1272543 : Nat := 118140960795 + 1272543 * 2 ^ 59
def prefixEnd_1272543 : Nat := 4983230072969 + 3 ^ 40 * 1272543 * 2
def baseEnd_1272543 : Nat := 217808737504839967786729

theorem tailTrace_1272543 : CollatzResearch.WordTrace tailWord_1272543 prefixEnd_1272543 217808737504839967786729 := by
  unfold tailWord_1272543
  simp only [CollatzResearch.WordTrace]
  refine ⟨46413456228801518886742283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30942304152534345924494855 46413456228801518886742283)
  ·
    refine ⟨69620184343202278330113425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46413456228801518886742283 69620184343202278330113425)
    ·
      refine ⟨52215138257401708747585069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69620184343202278330113425 52215138257401708747585069)
      ·
        refine ⟨19580676846525640780344401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52215138257401708747585069 19580676846525640780344401)
        ·
          refine ⟨14685507634894230585258301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19580676846525640780344401 14685507634894230585258301)
          ·
            refine ⟨5507065363085336469471863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14685507634894230585258301 5507065363085336469471863)
            ·
              refine ⟨8260598044628004704207795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5507065363085336469471863 8260598044628004704207795)
              ·
                refine ⟨12390897066942007056311693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8260598044628004704207795 12390897066942007056311693)
                ·
                  refine ⟨4646586400103252646116885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12390897066942007056311693 4646586400103252646116885)
                  ·
                    refine ⟨217808737504839967786729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4646586400103252646116885 217808737504839967786729)
                    ·
                      rfl

theorem cell23_1272543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 6].length) (baseStart_1272543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272543 prefixEnd_1272543 := by exact prefixLift 1272543
  have htrace : WordTrace (prefixWord ++ tailWord_1272543) baseStart_1272543 baseEnd_1272543 := by
    simpa [prefixWord, tailWord_1272543, baseEnd_1272543] using wordTrace_append hprefix tailTrace_1272543
  have hstable : (prefixWord ++ tailWord_1272543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272543).length < 2 ^ (prefixWord ++ tailWord_1272543).sum := by decide
  have hdescent : baseEnd_1272543 < baseStart_1272543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272563 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 4]
def baseStart_1272563 : Nat := 118140960795 + 1272563 * 2 ^ 59
def prefixEnd_1272563 : Nat := 4983230072969 + 3 ^ 40 * 1272563 * 2
def baseEnd_1272563 : Nat := 653436482127609825110095

theorem tailTrace_1272563 : CollatzResearch.WordTrace tailWord_1272563 prefixEnd_1272563 653436482127609825110095 := by
  unfold tailWord_1272563
  simp only [CollatzResearch.WordTrace]
  refine ⟨46414185688729062302470343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30942790459152708201646895 46414185688729062302470343)
  ·
    refine ⟨69621278533093593453705515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46414185688729062302470343 69621278533093593453705515)
    ·
      refine ⟨104431917799640390180558273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69621278533093593453705515 104431917799640390180558273)
      ·
        refine ⟨78323938349730292635418705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104431917799640390180558273 78323938349730292635418705)
        ·
          refine ⟨58742953762297719476564029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78323938349730292635418705 58742953762297719476564029)
          ·
            refine ⟨22028607660861644803711511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58742953762297719476564029 22028607660861644803711511)
            ·
              refine ⟨33042911491292467205567267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22028607660861644803711511 33042911491292467205567267)
              ·
                refine ⟨49564367236938700808350901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33042911491292467205567267 49564367236938700808350901)
                ·
                  refine ⟨4646659428463003200782897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49564367236938700808350901 4646659428463003200782897)
                  ·
                    refine ⟨3484994571347252400587173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4646659428463003200782897 3484994571347252400587173)
                    ·
                      refine ⟨653436482127609825110095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3484994571347252400587173 653436482127609825110095)
                      ·
                        rfl

theorem cell23_1272563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_1272563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272563 prefixEnd_1272563 := by exact prefixLift 1272563
  have htrace : WordTrace (prefixWord ++ tailWord_1272563) baseStart_1272563 baseEnd_1272563 := by
    simpa [prefixWord, tailWord_1272563, baseEnd_1272563] using wordTrace_append hprefix tailTrace_1272563
  have hstable : (prefixWord ++ tailWord_1272563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272563).length < 2 ^ (prefixWord ++ tailWord_1272563).sum := by decide
  have hdescent : baseEnd_1272563 < baseStart_1272563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272567 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 3, 2, 2]
def baseStart_1272567 : Nat := 118140960795 + 1272567 * 2 ^ 59
def prefixEnd_1272567 : Nat := 4983230072969 + 3 ^ 40 * 1272567 * 2
def baseEnd_1272567 : Nat := 653438536050227809460077

theorem tailTrace_1272567 : CollatzResearch.WordTrace tailWord_1272567 prefixEnd_1272567 653438536050227809460077 := by
  unfold tailWord_1272567
  simp only [CollatzResearch.WordTrace]
  refine ⟨46414331580714570985615955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30942887720476380657077303 46414331580714570985615955)
  ·
    refine ⟨69621497371071856478423933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46414331580714570985615955 69621497371071856478423933)
    ·
      refine ⟨26108061514151946179408975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69621497371071856478423933 26108061514151946179408975)
      ·
        refine ⟨39162092271227919269113463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26108061514151946179408975 39162092271227919269113463)
        ·
          refine ⟨58743138406841878903670195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39162092271227919269113463 58743138406841878903670195)
          ·
            refine ⟨88114707610262818355505293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58743138406841878903670195 88114707610262818355505293)
            ·
              refine ⟨33043015353848556883314485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88114707610262818355505293 33043015353848556883314485)
              ·
                refine ⟨3097782689423302207810733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33043015353848556883314485 3097782689423302207810733)
                ·
                  refine ⟨1161668508533738327929025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3097782689423302207810733 1161668508533738327929025)
                  ·
                    refine ⟨871251381400303745946769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1161668508533738327929025 871251381400303745946769)
                    ·
                      refine ⟨653438536050227809460077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871251381400303745946769 653438536050227809460077)
                      ·
                        rfl

theorem cell23_1272567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 2, 2].length) (baseStart_1272567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272567 prefixEnd_1272567 := by exact prefixLift 1272567
  have htrace : WordTrace (prefixWord ++ tailWord_1272567) baseStart_1272567 baseEnd_1272567 := by
    simpa [prefixWord, tailWord_1272567, baseEnd_1272567] using wordTrace_append hprefix tailTrace_1272567
  have hstable : (prefixWord ++ tailWord_1272567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272567).length < 2 ^ (prefixWord ++ tailWord_1272567).sum := by decide
  have hdescent : baseEnd_1272567 < baseStart_1272567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272570 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3]
def baseStart_1272570 : Nat := 118140960795 + 1272570 * 2 ^ 59
def prefixEnd_1272570 : Nat := 4983230072969 + 3 ^ 40 * 1272570 * 2
def baseEnd_1272570 : Nat := 653440076492191297722563

theorem tailTrace_1272570 : CollatzResearch.WordTrace tailWord_1272570 prefixEnd_1272570 653440076492191297722563 := by
  unfold tailWord_1272570
  simp only [CollatzResearch.WordTrace]
  refine ⟨11603610249925925624493791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30942960666469134998650109 11603610249925925624493791)
  ·
    refine ⟨17405415374888888436740687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11603610249925925624493791 17405415374888888436740687)
    ·
      refine ⟨26108123062333332655111031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17405415374888888436740687 26108123062333332655111031)
      ·
        refine ⟨39162184593499998982666547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26108123062333332655111031 39162184593499998982666547)
        ·
          refine ⟨58743276890249998473999821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39162184593499998982666547 58743276890249998473999821)
          ·
            refine ⟨22028728833843749427749933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58743276890249998473999821 22028728833843749427749933)
            ·
              refine ⟨8260773312691406035406225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22028728833843749427749933 8260773312691406035406225)
              ·
                refine ⟨6195579984518554526554669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8260773312691406035406225 6195579984518554526554669)
                ·
                  refine ⟨2323342494194457947458001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6195579984518554526554669 2323342494194457947458001)
                  ·
                    refine ⟨1742506870645843460593501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2323342494194457947458001 1742506870645843460593501)
                    ·
                      refine ⟨653440076492191297722563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1742506870645843460593501 653440076492191297722563)
                      ·
                        rfl

theorem cell23_1272570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_1272570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272570 prefixEnd_1272570 := by exact prefixLift 1272570
  have htrace : WordTrace (prefixWord ++ tailWord_1272570) baseStart_1272570 baseEnd_1272570 := by
    simpa [prefixWord, tailWord_1272570, baseEnd_1272570] using wordTrace_append hprefix tailTrace_1272570
  have hstable : (prefixWord ++ tailWord_1272570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272570).length < 2 ^ (prefixWord ++ tailWord_1272570).sum := by decide
  have hdescent : baseEnd_1272570 < baseStart_1272570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272584 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 3, 2, 2]
def baseStart_1272584 : Nat := 118140960795 + 1272584 * 2 ^ 59
def prefixEnd_1272584 : Nat := 4983230072969 + 3 ^ 40 * 1272584 * 2
def baseEnd_1272584 : Nat := 653447265221354242947499

theorem tailTrace_1272584 : CollatzResearch.WordTrace tailWord_1272584 prefixEnd_1272584 653447265221354242947499 := by
  unfold tailWord_1272584
  simp only [CollatzResearch.WordTrace]
  refine ⟨23207475810826491444492403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30943301081101988592656537 23207475810826491444492403)
  ·
    refine ⟨34811213716239737166738605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23207475810826491444492403 34811213716239737166738605)
    ·
      refine ⟨13054205143589901437526977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34811213716239737166738605 13054205143589901437526977)
      ·
        refine ⟨9790653857692426078145233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13054205143589901437526977 9790653857692426078145233)
        ·
          refine ⟨7342990393269319558608925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9790653857692426078145233 7342990393269319558608925)
          ·
            refine ⟨2753621397475994834478347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7342990393269319558608925 2753621397475994834478347)
            ·
              refine ⟨4130432096213992251717521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753621397475994834478347 4130432096213992251717521)
              ·
                refine ⟨3097824072160494188788141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4130432096213992251717521 3097824072160494188788141)
                ·
                  refine ⟨1161684027060185320795553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3097824072160494188788141 1161684027060185320795553)
                  ·
                    refine ⟨871263020295138990596665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1161684027060185320795553 871263020295138990596665)
                    ·
                      refine ⟨653447265221354242947499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871263020295138990596665 653447265221354242947499)
                      ·
                        rfl

theorem cell23_1272584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_1272584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272584 prefixEnd_1272584 := by exact prefixLift 1272584
  have htrace : WordTrace (prefixWord ++ tailWord_1272584) baseStart_1272584 baseEnd_1272584 := by
    simpa [prefixWord, tailWord_1272584, baseEnd_1272584] using wordTrace_append hprefix tailTrace_1272584
  have hstable : (prefixWord ++ tailWord_1272584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272584).length < 2 ^ (prefixWord ++ tailWord_1272584).sum := by decide
  have hdescent : baseEnd_1272584 < baseStart_1272584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272604 : List Nat := [2, 2, 3, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_1272604 : Nat := 118140960795 + 1272604 * 2 ^ 59
def prefixEnd_1272604 : Nat := 4983230072969 + 3 ^ 40 * 1272604 * 2
def baseEnd_1272604 : Nat := 653457534834444164697407

theorem tailTrace_1272604 : CollatzResearch.WordTrace tailWord_1272604 prefixEnd_1272604 653457534834444164697407 := by
  unfold tailWord_1272604
  simp only [CollatzResearch.WordTrace]
  refine ⟨23207840540790263152356433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30943787387720350869808577 23207840540790263152356433)
  ·
    refine ⟨17405880405592697364267325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23207840540790263152356433 17405880405592697364267325)
    ·
      refine ⟨6527205152097261511600247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17405880405592697364267325 6527205152097261511600247)
      ·
        refine ⟨9790807728145892267400371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6527205152097261511600247 9790807728145892267400371)
        ·
          refine ⟨14686211592218838401100557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9790807728145892267400371 14686211592218838401100557)
          ·
            refine ⟨5507329347082064400412709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14686211592218838401100557 5507329347082064400412709)
            ·
              refine ⟨1032624252577887075077383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5507329347082064400412709 1032624252577887075077383)
              ·
                refine ⟨1548936378866830612616075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032624252577887075077383 1548936378866830612616075)
                ·
                  refine ⟨2323404568300245918924113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548936378866830612616075 2323404568300245918924113)
                  ·
                    refine ⟨1742553426225184439193085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2323404568300245918924113 1742553426225184439193085)
                    ·
                      refine ⟨653457534834444164697407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1742553426225184439193085 653457534834444164697407)
                      ·
                        rfl

theorem cell23_1272604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_1272604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272604 prefixEnd_1272604 := by exact prefixLift 1272604
  have htrace : WordTrace (prefixWord ++ tailWord_1272604) baseStart_1272604 baseEnd_1272604 := by
    simpa [prefixWord, tailWord_1272604, baseEnd_1272604] using wordTrace_append hprefix tailTrace_1272604
  have hstable : (prefixWord ++ tailWord_1272604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272604).length < 2 ^ (prefixWord ++ tailWord_1272604).sum := by decide
  have hdescent : baseEnd_1272604 < baseStart_1272604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272618 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1272618 : Nat := 118140960795 + 1272618 * 2 ^ 59
def prefixEnd_1272618 : Nat := 4983230072969 + 3 ^ 40 * 1272618 * 2
def baseEnd_1272618 : Nat := 653464723563607109922343

theorem tailTrace_1272618 : CollatzResearch.WordTrace tailWord_1272618 prefixEnd_1272618 653464723563607109922343 := by
  unfold tailWord_1272618
  simp only [CollatzResearch.WordTrace]
  refine ⟨11604047925882451673930627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30944127802353204463815005 11604047925882451673930627)
  ·
    refine ⟨17406071888823677510895941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11604047925882451673930627 17406071888823677510895941)
    ·
      refine ⟨3263638479154439533292989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17406071888823677510895941 3263638479154439533292989)
      ·
        refine ⟨1223864429682914824984871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3263638479154439533292989 1223864429682914824984871)
        ·
          refine ⟨1835796644524372237477307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223864429682914824984871 1835796644524372237477307)
          ·
            refine ⟨2753694966786558356215961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835796644524372237477307 2753694966786558356215961)
            ·
              refine ⟨2065271225089918767161971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2753694966786558356215961 2065271225089918767161971)
              ·
                refine ⟨3097906837634878150742957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065271225089918767161971 3097906837634878150742957)
                ·
                  refine ⟨1161715064113079306528609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3097906837634878150742957 1161715064113079306528609)
                  ·
                    refine ⟨871286298084809479896457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1161715064113079306528609 871286298084809479896457)
                    ·
                      refine ⟨653464723563607109922343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871286298084809479896457 653464723563607109922343)
                      ·
                        rfl

theorem cell23_1272618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1272618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272618 prefixEnd_1272618 := by exact prefixLift 1272618
  have htrace : WordTrace (prefixWord ++ tailWord_1272618) baseStart_1272618 baseEnd_1272618 := by
    simpa [prefixWord, tailWord_1272618, baseEnd_1272618] using wordTrace_append hprefix tailTrace_1272618
  have hstable : (prefixWord ++ tailWord_1272618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272618).length < 2 ^ (prefixWord ++ tailWord_1272618).sum := by decide
  have hdescent : baseEnd_1272618 < baseStart_1272618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272634 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3]
def baseStart_1272634 : Nat := 118140960795 + 1272634 * 2 ^ 59
def prefixEnd_1272634 : Nat := 4983230072969 + 3 ^ 40 * 1272634 * 2
def baseEnd_1272634 : Nat := 653472939254079047322269

theorem tailTrace_1272634 : CollatzResearch.WordTrace tailWord_1272634 prefixEnd_1272634 653472939254079047322269 := by
  unfold tailWord_1272634
  simp only [CollatzResearch.WordTrace]
  refine ⟨11604193817867960357076239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30944516847647894285536637 11604193817867960357076239)
  ·
    refine ⟨17406290726801940535614359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11604193817867960357076239 17406290726801940535614359)
    ·
      refine ⟨26109436090202910803421539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17406290726801940535614359 26109436090202910803421539)
      ·
        refine ⟨39164154135304366205132309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26109436090202910803421539 39164154135304366205132309)
        ·
          refine ⟨1835819725092392165865577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39164154135304366205132309 1835819725092392165865577)
          ·
            refine ⟨1376864793819294124399183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1835819725092392165865577 1376864793819294124399183)
            ·
              refine ⟨2065297190728941186598775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376864793819294124399183 2065297190728941186598775)
              ·
                refine ⟨3097945786093411779898163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065297190728941186598775 3097945786093411779898163)
                ·
                  refine ⟨4646918679140117669847245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3097945786093411779898163 4646918679140117669847245)
                  ·
                    refine ⟨1742594504677544126192717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4646918679140117669847245 1742594504677544126192717)
                    ·
                      refine ⟨653472939254079047322269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1742594504677544126192717 653472939254079047322269)
                      ·
                        rfl

theorem cell23_1272634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_1272634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272634 prefixEnd_1272634 := by exact prefixLift 1272634
  have htrace : WordTrace (prefixWord ++ tailWord_1272634) baseStart_1272634 baseEnd_1272634 := by
    simpa [prefixWord, tailWord_1272634, baseEnd_1272634] using wordTrace_append hprefix tailTrace_1272634
  have hstable : (prefixWord ++ tailWord_1272634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272634).length < 2 ^ (prefixWord ++ tailWord_1272634).sum := by decide
  have hdescent : baseEnd_1272634 < baseStart_1272634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272641 : List Nat := [1, 2, 5, 3, 2, 1, 2, 7]
def baseStart_1272641 : Nat := 118140960795 + 1272641 * 2 ^ 59
def prefixEnd_1272641 : Nat := 4983230072969 + 3 ^ 40 * 1272641 * 2
def baseEnd_1272641 : Nat := 24202834578468908145731

theorem tailTrace_1272641 : CollatzResearch.WordTrace tailWord_1272641 prefixEnd_1272641 24202834578468908145731 := by
  unfold tailWord_1272641
  simp only [CollatzResearch.WordTrace]
  refine ⟨46417030582446481623809777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30944687054964321082539851 46417030582446481623809777)
  ·
    refine ⟨34812772936834861217857333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46417030582446481623809777 34812772936834861217857333)
    ·
      refine ⟨3263697462828268239174125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34812772936834861217857333 3263697462828268239174125)
      ·
        refine ⟨1223886548560600589690297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3263697462828268239174125 1223886548560600589690297)
        ·
          refine ⟨917914911420450442267723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1223886548560600589690297 917914911420450442267723)
          ·
            refine ⟨1376872367130675663401585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917914911420450442267723 1376872367130675663401585)
            ·
              refine ⟨1032654275348006747551189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376872367130675663401585 1032654275348006747551189)
              ·
                refine ⟨24202834578468908145731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1032654275348006747551189 24202834578468908145731)
                ·
                  rfl

theorem cell23_1272641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 7].length) (baseStart_1272641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272641 prefixEnd_1272641 := by exact prefixLift 1272641
  have htrace : WordTrace (prefixWord ++ tailWord_1272641) baseStart_1272641 baseEnd_1272641 := by
    simpa [prefixWord, tailWord_1272641, baseEnd_1272641] using wordTrace_append hprefix tailTrace_1272641
  have hstable : (prefixWord ++ tailWord_1272641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272641).length < 2 ^ (prefixWord ++ tailWord_1272641).sum := by decide
  have hdescent : baseEnd_1272641 < baseStart_1272641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272691 : List Nat := [1, 1, 1, 2, 2, 1, 8, 1, 2, 2, 2]
def baseStart_1272691 : Nat := 118140960795 + 1272691 * 2 ^ 59
def prefixEnd_1272691 : Nat := 4983230072969 + 3 ^ 40 * 1272691 * 2
def baseEnd_1272691 : Nat := 653502207651385324309507

theorem tailTrace_1272691 : CollatzResearch.WordTrace tailWord_1272691 prefixEnd_1272691 653502207651385324309507 := by
  unfold tailWord_1272691
  simp only [CollatzResearch.WordTrace]
  refine ⟨46418854232265340163129927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30945902821510226775419951 46418854232265340163129927)
  ·
    refine ⟨69628281348398010244694891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46418854232265340163129927 69628281348398010244694891)
    ·
      refine ⟨104442422022597015367042337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69628281348398010244694891 104442422022597015367042337)
      ·
        refine ⟨78331816516947761525281753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104442422022597015367042337 78331816516947761525281753)
        ·
          refine ⟨58748862387710821143961315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78331816516947761525281753 58748862387710821143961315)
          ·
            refine ⟨88123293581566231715941973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58748862387710821143961315 88123293581566231715941973)
            ·
              refine ⟨1032694846658979277921195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 88123293581566231715941973 1032694846658979277921195)
              ·
                refine ⟨1549042269988468916881793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032694846658979277921195 1549042269988468916881793)
                ·
                  refine ⟨1161781702491351687661345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1549042269988468916881793 1161781702491351687661345)
                  ·
                    refine ⟨871336276868513765746009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1161781702491351687661345 871336276868513765746009)
                    ·
                      refine ⟨653502207651385324309507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871336276868513765746009 653502207651385324309507)
                      ·
                        rfl

theorem cell23_1272691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 2, 2, 2].length) (baseStart_1272691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272691 prefixEnd_1272691 := by exact prefixLift 1272691
  have htrace : WordTrace (prefixWord ++ tailWord_1272691) baseStart_1272691 baseEnd_1272691 := by
    simpa [prefixWord, tailWord_1272691, baseEnd_1272691] using wordTrace_append hprefix tailTrace_1272691
  have hstable : (prefixWord ++ tailWord_1272691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272691).length < 2 ^ (prefixWord ++ tailWord_1272691).sum := by decide
  have hdescent : baseEnd_1272691 < baseStart_1272691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272737 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1272737 : Nat := 118140960795 + 1272737 * 2 ^ 59
def prefixEnd_1272737 : Nat := 4983230072969 + 3 ^ 40 * 1272737 * 2
def baseEnd_1272737 : Nat := 653525827761492144334295

theorem tailTrace_1272737 : CollatzResearch.WordTrace tailWord_1272737 prefixEnd_1272737 653525827761492144334295 := by
  unfold tailWord_1272737
  simp only [CollatzResearch.WordTrace]
  refine ⟨46420531990098690019304465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30947021326732460012869643 46420531990098690019304465)
  ·
    refine ⟨34815398992574017514478349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46420531990098690019304465 34815398992574017514478349)
    ·
      refine ⟨13055774622215256567929381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34815398992574017514478349 13055774622215256567929381)
      ·
        refine ⟨2447957741665360606486759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13055774622215256567929381 2447957741665360606486759)
        ·
          refine ⟨3671936612498040909730139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447957741665360606486759 3671936612498040909730139)
          ·
            refine ⟨5507904918747061364595209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3671936612498040909730139 5507904918747061364595209)
            ·
              refine ⟨4130928689060296023446407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5507904918747061364595209 4130928689060296023446407)
              ·
                refine ⟨6196393033590444035169611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4130928689060296023446407 6196393033590444035169611)
                ·
                  refine ⟨9294589550385666052754417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6196393033590444035169611 9294589550385666052754417)
                  ·
                    refine ⟨6970942162789249539565813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9294589550385666052754417 6970942162789249539565813)
                    ·
                      refine ⟨653525827761492144334295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6970942162789249539565813 653525827761492144334295)
                      ·
                        rfl

theorem cell23_1272737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1272737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272737 prefixEnd_1272737 := by exact prefixLift 1272737
  have htrace : WordTrace (prefixWord ++ tailWord_1272737) baseStart_1272737 baseEnd_1272737 := by
    simpa [prefixWord, tailWord_1272737, baseEnd_1272737] using wordTrace_append hprefix tailTrace_1272737
  have hstable : (prefixWord ++ tailWord_1272737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272737).length < 2 ^ (prefixWord ++ tailWord_1272737).sum := by decide
  have hdescent : baseEnd_1272737 < baseStart_1272737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272747 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 2, 4, 2]
def baseStart_1272747 : Nat := 118140960795 + 1272747 * 2 ^ 59
def prefixEnd_1272747 : Nat := 4983230072969 + 3 ^ 40 * 1272747 * 2
def baseEnd_1272747 : Nat := 653530962568037105209249

theorem tailTrace_1272747 : CollatzResearch.WordTrace tailWord_1272747 prefixEnd_1272747 653530962568037105209249 := by
  unfold tailWord_1272747
  simp only [CollatzResearch.WordTrace]
  refine ⟨46420896720062461727168495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30947264480041641151445663 46420896720062461727168495)
  ·
    refine ⟨69631345080093692590752743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46420896720062461727168495 69631345080093692590752743)
    ·
      refine ⟨104447017620140538886129115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69631345080093692590752743 104447017620140538886129115)
      ·
        refine ⟨156670526430210808329193673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104447017620140538886129115 156670526430210808329193673)
        ·
          refine ⟨117502894822658106246895255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156670526430210808329193673 117502894822658106246895255)
          ·
            refine ⟨176254342233987159370342883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117502894822658106246895255 176254342233987159370342883)
            ·
              refine ⟨264381513350980739055514325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176254342233987159370342883 264381513350980739055514325)
              ·
                refine ⟨6196441719163611071613617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 264381513350980739055514325 6196441719163611071613617)
                ·
                  refine ⟨4647331289372708303710213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6196441719163611071613617 4647331289372708303710213)
                  ·
                    refine ⟨871374616757382806945665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4647331289372708303710213 871374616757382806945665)
                    ·
                      refine ⟨653530962568037105209249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871374616757382806945665 653530962568037105209249)
                      ·
                        rfl

theorem cell23_1272747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 4, 2].length) (baseStart_1272747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272747 prefixEnd_1272747 := by exact prefixLift 1272747
  have htrace : WordTrace (prefixWord ++ tailWord_1272747) baseStart_1272747 baseEnd_1272747 := by
    simpa [prefixWord, tailWord_1272747, baseEnd_1272747] using wordTrace_append hprefix tailTrace_1272747
  have hstable : (prefixWord ++ tailWord_1272747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272747).length < 2 ^ (prefixWord ++ tailWord_1272747).sum := by decide
  have hdescent : baseEnd_1272747 < baseStart_1272747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272767 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 3]
def baseStart_1272767 : Nat := 118140960795 + 1272767 * 2 ^ 59
def prefixEnd_1272767 : Nat := 4983230072969 + 3 ^ 40 * 1272767 * 2
def baseEnd_1272767 : Nat := 653541232181127026959157

theorem tailTrace_1272767 : CollatzResearch.WordTrace tailWord_1272767 prefixEnd_1272767 653541232181127026959157 := by
  unfold tailWord_1272767
  simp only [CollatzResearch.WordTrace]
  refine ⟨46421626179990005142896555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30947750786660003428597703 46421626179990005142896555)
  ·
    refine ⟨69632439269985007714344833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46421626179990005142896555 69632439269985007714344833)
    ·
      refine ⟨52224329452488755785758625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69632439269985007714344833 52224329452488755785758625)
      ·
        refine ⟨39168247089366566839318969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52224329452488755785758625 39168247089366566839318969)
        ·
          refine ⟨29376185317024925129489227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39168247089366566839318969 29376185317024925129489227)
          ·
            refine ⟨44064277975537387694233841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29376185317024925129489227 44064277975537387694233841)
            ·
              refine ⟨33048208481653040770675381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44064277975537387694233841 33048208481653040770675381)
              ·
                refine ⟨3098269545154972572250817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33048208481653040770675381 3098269545154972572250817)
                ·
                  refine ⟨2323702158866229429188113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3098269545154972572250817 2323702158866229429188113)
                  ·
                    refine ⟨1742776619149672071891085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2323702158866229429188113 1742776619149672071891085)
                    ·
                      refine ⟨653541232181127026959157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1742776619149672071891085 653541232181127026959157)
                      ·
                        rfl

theorem cell23_1272767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_1272767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272767 prefixEnd_1272767 := by exact prefixLift 1272767
  have htrace : WordTrace (prefixWord ++ tailWord_1272767) baseStart_1272767 baseEnd_1272767 := by
    simpa [prefixWord, tailWord_1272767, baseEnd_1272767] using wordTrace_append hprefix tailTrace_1272767
  have hstable : (prefixWord ++ tailWord_1272767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272767).length < 2 ^ (prefixWord ++ tailWord_1272767).sum := by decide
  have hdescent : baseEnd_1272767 < baseStart_1272767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272824 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 2, 3, 2]
def baseStart_1272824 : Nat := 118140960795 + 1272824 * 2 ^ 59
def prefixEnd_1272824 : Nat := 4983230072969 + 3 ^ 40 * 1272824 * 2
def baseEnd_1272824 : Nat := 653570500578433303946395

theorem tailTrace_1272824 : CollatzResearch.WordTrace tailWord_1272824 prefixEnd_1272824 653570500578433303946395 := by
  unfold tailWord_1272824
  simp only [CollatzResearch.WordTrace]
  refine ⟨23211852570391751938860763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30949136760522335918481017 23211852570391751938860763)
  ·
    refine ⟨34817778855587627908291145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23211852570391751938860763 34817778855587627908291145)
    ·
      refine ⟨26113334141690720931218359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34817778855587627908291145 26113334141690720931218359)
      ·
        refine ⟨39170001212536081396827539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26113334141690720931218359 39170001212536081396827539)
        ·
          refine ⟨58755001818804122095241309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39170001212536081396827539 58755001818804122095241309)
          ·
            refine ⟨22033125682051545785715491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58755001818804122095241309 22033125682051545785715491)
            ·
              refine ⟨33049688523077318678573237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22033125682051545785715491 33049688523077318678573237)
              ·
                refine ⟨3098408299038498626116241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33049688523077318678573237 3098408299038498626116241)
                ·
                  refine ⟨2323806224278873969587181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3098408299038498626116241 2323806224278873969587181)
                  ·
                    refine ⟨871427334104577738595193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2323806224278873969587181 871427334104577738595193)
                    ·
                      refine ⟨653570500578433303946395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871427334104577738595193 653570500578433303946395)
                      ·
                        rfl

theorem cell23_1272824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 2, 3, 2].length) (baseStart_1272824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272824 prefixEnd_1272824 := by exact prefixLift 1272824
  have htrace : WordTrace (prefixWord ++ tailWord_1272824) baseStart_1272824 baseEnd_1272824 := by
    simpa [prefixWord, tailWord_1272824, baseEnd_1272824] using wordTrace_append hprefix tailTrace_1272824
  have hstable : (prefixWord ++ tailWord_1272824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272824).length < 2 ^ (prefixWord ++ tailWord_1272824).sum := by decide
  have hdescent : baseEnd_1272824 < baseStart_1272824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272857 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 1, 1, 5]
def baseStart_1272857 : Nat := 118140960795 + 1272857 * 2 ^ 59
def prefixEnd_1272857 : Nat := 4983230072969 + 3 ^ 40 * 1272857 * 2
def baseEnd_1272857 : Nat := 653587445440031674833743

theorem tailTrace_1272857 : CollatzResearch.WordTrace tailWord_1272857 prefixEnd_1272857 653587445440031674833743 := by
  unfold tailWord_1272857
  simp only [CollatzResearch.WordTrace]
  refine ⟨46424908749663950513672825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30949939166442633675781883 46424908749663950513672825)
  ·
    refine ⟨34818681562247962885254619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46424908749663950513672825 34818681562247962885254619)
    ·
      refine ⟨52228022343371944327881929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34818681562247962885254619 52228022343371944327881929)
      ·
        refine ⟨39171016757528958245911447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52228022343371944327881929 39171016757528958245911447)
        ·
          refine ⟨58756525136293437368867171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39171016757528958245911447 58756525136293437368867171)
          ·
            refine ⟨88134787704440156053300757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58756525136293437368867171 88134787704440156053300757)
            ·
              refine ⟨4131318173645632314998473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 88134787704440156053300757 4131318173645632314998473)
              ·
                refine ⟨3098488630234224236248855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4131318173645632314998473 3098488630234224236248855)
                ·
                  refine ⟨4647732945351336354373283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3098488630234224236248855 4647732945351336354373283)
                  ·
                    refine ⟨6971599418027004531559925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4647732945351336354373283 6971599418027004531559925)
                    ·
                      refine ⟨653587445440031674833743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6971599418027004531559925 653587445440031674833743)
                      ·
                        rfl

theorem cell23_1272857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_1272857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272857 prefixEnd_1272857 := by exact prefixLift 1272857
  have htrace : WordTrace (prefixWord ++ tailWord_1272857) baseStart_1272857 baseEnd_1272857 := by
    simpa [prefixWord, tailWord_1272857, baseEnd_1272857] using wordTrace_append hprefix tailTrace_1272857
  have hstable : (prefixWord ++ tailWord_1272857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272857).length < 2 ^ (prefixWord ++ tailWord_1272857).sum := by decide
  have hdescent : baseEnd_1272857 < baseStart_1272857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272867 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 6]
def baseStart_1272867 : Nat := 118140960795 + 1272867 * 2 ^ 59
def prefixEnd_1272867 : Nat := 4983230072969 + 3 ^ 40 * 1272867 * 2
def baseEnd_1272867 : Nat := 653592580246576635708697

theorem tailTrace_1272867 : CollatzResearch.WordTrace tailWord_1272867 prefixEnd_1272867 653592580246576635708697 := by
  unfold tailWord_1272867
  simp only [CollatzResearch.WordTrace]
  refine ⟨46425273479627722221536855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30950182319751814814357903 46425273479627722221536855)
  ·
    refine ⟨69637910219441583332305283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46425273479627722221536855 69637910219441583332305283)
    ·
      refine ⟨104456865329162374998457925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69637910219441583332305283 104456865329162374998457925)
      ·
        refine ⟨19585662249217945312210861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104456865329162374998457925 19585662249217945312210861)
        ·
          refine ⟨7344623343456729492079073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19585662249217945312210861 7344623343456729492079073)
          ·
            refine ⟨5508467507592547119059305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7344623343456729492079073 5508467507592547119059305)
            ·
              refine ⟨4131350630694410339294479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5508467507592547119059305 4131350630694410339294479)
              ·
                refine ⟨6197025946041615508941719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4131350630694410339294479 6197025946041615508941719)
                ·
                  refine ⟨9295538919062423263412579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6197025946041615508941719 9295538919062423263412579)
                  ·
                    refine ⟨13943308378593634895118869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9295538919062423263412579 13943308378593634895118869)
                    ·
                      refine ⟨653592580246576635708697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13943308378593634895118869 653592580246576635708697)
                      ·
                        rfl

theorem cell23_1272867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_1272867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272867 prefixEnd_1272867 := by exact prefixLift 1272867
  have htrace : WordTrace (prefixWord ++ tailWord_1272867) baseStart_1272867 baseEnd_1272867 := by
    simpa [prefixWord, tailWord_1272867, baseEnd_1272867] using wordTrace_append hprefix tailTrace_1272867
  have hstable : (prefixWord ++ tailWord_1272867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272867).length < 2 ^ (prefixWord ++ tailWord_1272867).sum := by decide
  have hdescent : baseEnd_1272867 < baseStart_1272867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272871 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1272871 : Nat := 118140960795 + 1272871 * 2 ^ 59
def prefixEnd_1272871 : Nat := 4983230072969 + 3 ^ 40 * 1272871 * 2
def baseEnd_1272871 : Nat := 653594634169194620058679

theorem tailTrace_1272871 : CollatzResearch.WordTrace tailWord_1272871 prefixEnd_1272871 653594634169194620058679 := by
  unfold tailWord_1272871
  simp only [CollatzResearch.WordTrace]
  refine ⟨46425419371613230904682467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30950279581075487269788311 46425419371613230904682467)
  ·
    refine ⟨69638129057419846357023701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46425419371613230904682467 69638129057419846357023701)
    ·
      refine ⟨1632143649783277648992743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 69638129057419846357023701 1632143649783277648992743)
      ·
        refine ⟨2448215474674916473489115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632143649783277648992743 2448215474674916473489115)
        ·
          refine ⟨3672323212012374710233673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2448215474674916473489115 3672323212012374710233673)
          ·
            refine ⟨2754242409009281032675255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3672323212012374710233673 2754242409009281032675255)
            ·
              refine ⟨4131363613513921549012883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754242409009281032675255 4131363613513921549012883)
              ·
                refine ⟨6197045420270882323519325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4131363613513921549012883 6197045420270882323519325)
                ·
                  refine ⟨2323892032601580871319747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6197045420270882323519325 2323892032601580871319747)
                  ·
                    refine ⟨3485838048902371306979621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2323892032601580871319747 3485838048902371306979621)
                    ·
                      refine ⟨653594634169194620058679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3485838048902371306979621 653594634169194620058679)
                      ·
                        rfl

theorem cell23_1272871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1272871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272871 prefixEnd_1272871 := by exact prefixLift 1272871
  have htrace : WordTrace (prefixWord ++ tailWord_1272871) baseStart_1272871 baseEnd_1272871 := by
    simpa [prefixWord, tailWord_1272871, baseEnd_1272871] using wordTrace_append hprefix tailTrace_1272871
  have hstable : (prefixWord ++ tailWord_1272871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272871).length < 2 ^ (prefixWord ++ tailWord_1272871).sum := by decide
  have hdescent : baseEnd_1272871 < baseStart_1272871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272927 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 4]
def baseStart_1272927 : Nat := 118140960795 + 1272927 * 2 ^ 59
def prefixEnd_1272927 : Nat := 4983230072969 + 3 ^ 40 * 1272927 * 2
def baseEnd_1272927 : Nat := 653623389085846400958421

theorem tailTrace_1272927 : CollatzResearch.WordTrace tailWord_1272927 prefixEnd_1272927 653623389085846400958421 := by
  unfold tailWord_1272927
  simp only [CollatzResearch.WordTrace]
  refine ⟨46427461859410352468721035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30951641239606901645814023 46427461859410352468721035)
  ·
    refine ⟨69641192789115528703081553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46427461859410352468721035 69641192789115528703081553)
    ·
      refine ⟨52230894591836646527311165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69641192789115528703081553 52230894591836646527311165)
      ·
        refine ⟨19586585471938742447741687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52230894591836646527311165 19586585471938742447741687)
        ·
          refine ⟨29379878207908113671612531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19586585471938742447741687 29379878207908113671612531)
          ·
            refine ⟨44069817311862170507418797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29379878207908113671612531 44069817311862170507418797)
            ·
              refine ⟨16526181491948313940282049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44069817311862170507418797 16526181491948313940282049)
              ·
                refine ⟨12394636118961235455211537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16526181491948313940282049 12394636118961235455211537)
                ·
                  refine ⟨9295977089220926591408653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12394636118961235455211537 9295977089220926591408653)
                  ·
                    refine ⟨3485991408457847471778245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9295977089220926591408653 3485991408457847471778245)
                    ·
                      refine ⟨653623389085846400958421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3485991408457847471778245 653623389085846400958421)
                      ·
                        rfl

theorem cell23_1272927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_1272927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272927 prefixEnd_1272927 := by exact prefixLift 1272927
  have htrace : WordTrace (prefixWord ++ tailWord_1272927) baseStart_1272927 baseEnd_1272927 := by
    simpa [prefixWord, tailWord_1272927, baseEnd_1272927] using wordTrace_append hprefix tailTrace_1272927
  have hstable : (prefixWord ++ tailWord_1272927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272927).length < 2 ^ (prefixWord ++ tailWord_1272927).sum := by decide
  have hdescent : baseEnd_1272927 < baseStart_1272927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272931 : List Nat := [1, 1, 1, 5, 1, 1, 1, 6, 1, 3, 2]
def baseStart_1272931 : Nat := 118140960795 + 1272931 * 2 ^ 59
def prefixEnd_1272931 : Nat := 4983230072969 + 3 ^ 40 * 1272931 * 2
def baseEnd_1272931 : Nat := 653625443008464385308403

theorem tailTrace_1272931 : CollatzResearch.WordTrace tailWord_1272931 prefixEnd_1272931 653625443008464385308403 := by
  unfold tailWord_1272931
  simp only [CollatzResearch.WordTrace]
  refine ⟨46427607751395861151866647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30951738500930574101244431 46427607751395861151866647)
  ·
    refine ⟨69641411627093791727799971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46427607751395861151866647 69641411627093791727799971)
    ·
      refine ⟨104462117440640687591699957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69641411627093791727799971 104462117440640687591699957)
      ·
        refine ⟨9793323510060064461721871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104462117440640687591699957 9793323510060064461721871)
        ·
          refine ⟨14689985265090096692582807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9793323510060064461721871 14689985265090096692582807)
          ·
            refine ⟨22034977897635145038874211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14689985265090096692582807 22034977897635145038874211)
            ·
              refine ⟨33052466846452717558311317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22034977897635145038874211 33052466846452717558311317)
              ·
                refine ⟨1549334383427471135545843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33052466846452717558311317 1549334383427471135545843)
                ·
                  refine ⟨2324001575141206703318765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1549334383427471135545843 2324001575141206703318765)
                  ·
                    refine ⟨871500590677952513744537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2324001575141206703318765 871500590677952513744537)
                    ·
                      refine ⟨653625443008464385308403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871500590677952513744537 653625443008464385308403)
                      ·
                        rfl

theorem cell23_1272931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_1272931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272931 prefixEnd_1272931 := by exact prefixLift 1272931
  have htrace : WordTrace (prefixWord ++ tailWord_1272931) baseStart_1272931 baseEnd_1272931 := by
    simpa [prefixWord, tailWord_1272931, baseEnd_1272931] using wordTrace_append hprefix tailTrace_1272931
  have hstable : (prefixWord ++ tailWord_1272931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272931).length < 2 ^ (prefixWord ++ tailWord_1272931).sum := by decide
  have hdescent : baseEnd_1272931 < baseStart_1272931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272978 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_1272978 : Nat := 118140960795 + 1272978 * 2 ^ 59
def prefixEnd_1272978 : Nat := 4983230072969 + 3 ^ 40 * 1272978 * 2
def baseEnd_1272978 : Nat := 653649576599225701420687

theorem tailTrace_1272978 : CollatzResearch.WordTrace tailWord_1272978 prefixEnd_1272978 653649576599225701420687 := by
  unfold tailWord_1272978
  simp only [CollatzResearch.WordTrace]
  refine ⟨11607330495556397044706897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30952881321483725452551725 11607330495556397044706897)
  ·
    refine ⟨8705497871667297783530173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11607330495556397044706897 8705497871667297783530173)
    ·
      refine ⟨3264561701875236668823815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8705497871667297783530173 3264561701875236668823815)
      ·
        refine ⟨4896842552812855003235723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3264561701875236668823815 4896842552812855003235723)
        ·
          refine ⟨7345263829219282504853585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4896842552812855003235723 7345263829219282504853585)
          ·
            refine ⟨5508947871914461878640189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7345263829219282504853585 5508947871914461878640189)
            ·
              refine ⟨2065855451967923204490071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5508947871914461878640189 2065855451967923204490071)
              ·
                refine ⟨3098783177951884806735107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065855451967923204490071 3098783177951884806735107)
                ·
                  refine ⟨4648174766927827210102661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3098783177951884806735107 4648174766927827210102661)
                  ·
                    refine ⟨871532768798967601894249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4648174766927827210102661 871532768798967601894249)
                    ·
                      refine ⟨653649576599225701420687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871532768798967601894249 653649576599225701420687)
                      ·
                        rfl

theorem cell23_1272978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_1272978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272978 prefixEnd_1272978 := by exact prefixLift 1272978
  have htrace : WordTrace (prefixWord ++ tailWord_1272978) baseStart_1272978 baseEnd_1272978 := by
    simpa [prefixWord, tailWord_1272978, baseEnd_1272978] using wordTrace_append hprefix tailTrace_1272978
  have hstable : (prefixWord ++ tailWord_1272978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272978).length < 2 ^ (prefixWord ++ tailWord_1272978).sum := by decide
  have hdescent : baseEnd_1272978 < baseStart_1272978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272984 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 7]
def baseStart_1272984 : Nat := 118140960795 + 1272984 * 2 ^ 59
def prefixEnd_1272984 : Nat := 4983230072969 + 3 ^ 40 * 1272984 * 2
def baseEnd_1272984 : Nat := 72628073053683630882851

theorem tailTrace_1272984 : CollatzResearch.WordTrace tailWord_1272984 prefixEnd_1272984 72628073053683630882851 := by
  unfold tailWord_1272984
  simp only [CollatzResearch.WordTrace]
  refine ⟨23214770410101925601773003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30953027213469234135697337 23214770410101925601773003)
  ·
    refine ⟨34822155615152888402659505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23214770410101925601773003 34822155615152888402659505)
    ·
      refine ⟨26116616711364666301994629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34822155615152888402659505 26116616711364666301994629)
      ·
        refine ⟨4896865633380874931623993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26116616711364666301994629 4896865633380874931623993)
        ·
          refine ⟨3672649225035656198717995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4896865633380874931623993 3672649225035656198717995)
          ·
            refine ⟨5508973837553484298076993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3672649225035656198717995 5508973837553484298076993)
            ·
              refine ⟨4131730378165113223557745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5508973837553484298076993 4131730378165113223557745)
              ·
                refine ⟨3098797783623834917668309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4131730378165113223557745 3098797783623834917668309)
                ·
                  refine ⟨72628073053683630882851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3098797783623834917668309 72628073053683630882851)
                  ·
                    rfl

theorem cell23_1272984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 7].length) (baseStart_1272984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1272984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1272984 prefixEnd_1272984 := by exact prefixLift 1272984
  have htrace : WordTrace (prefixWord ++ tailWord_1272984) baseStart_1272984 baseEnd_1272984 := by
    simpa [prefixWord, tailWord_1272984, baseEnd_1272984] using wordTrace_append hprefix tailTrace_1272984
  have hstable : (prefixWord ++ tailWord_1272984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272984).length < 2 ^ (prefixWord ++ tailWord_1272984).sum := by decide
  have hdescent : baseEnd_1272984 < baseStart_1272984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273027 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 2, 8]
def baseStart_1273027 : Nat := 118140960795 + 1273027 * 2 ^ 59
def prefixEnd_1273027 : Nat := 4983230072969 + 3 ^ 40 * 1273027 * 2
def baseEnd_1273027 : Nat := 217891579050432003235987

theorem tailTrace_1273027 : CollatzResearch.WordTrace tailWord_1273027 prefixEnd_1273027 217891579050432003235987 := by
  unfold tailWord_1273027
  simp only [CollatzResearch.WordTrace]
  refine ⟨46431109159048069547361335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30954072772698713031574223 46431109159048069547361335)
  ·
    refine ⟨69646663738572104321042003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46431109159048069547361335 69646663738572104321042003)
    ·
      refine ⟨104469995607858156481563005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69646663738572104321042003 104469995607858156481563005)
      ·
        refine ⟨39176248352946808680586127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104469995607858156481563005 39176248352946808680586127)
        ·
          refine ⟨58764372529420213020879191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39176248352946808680586127 58764372529420213020879191)
          ·
            refine ⟨88146558794130319531318787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58764372529420213020879191 88146558794130319531318787)
            ·
              refine ⟨132219838191195479296978181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88146558794130319531318787 132219838191195479296978181)
              ·
                refine ⟨24791219660849152368183409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132219838191195479296978181 24791219660849152368183409)
                ·
                  refine ⟨18593414745636864276137557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24791219660849152368183409 18593414745636864276137557)
                  ·
                    refine ⟨217891579050432003235987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18593414745636864276137557 217891579050432003235987)
                    ·
                      rfl

theorem cell23_1273027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 8].length) (baseStart_1273027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273027 prefixEnd_1273027 := by exact prefixLift 1273027
  have htrace : WordTrace (prefixWord ++ tailWord_1273027) baseStart_1273027 baseEnd_1273027 := by
    simpa [prefixWord, tailWord_1273027, baseEnd_1273027] using wordTrace_append hprefix tailTrace_1273027
  have hstable : (prefixWord ++ tailWord_1273027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273027).length < 2 ^ (prefixWord ++ tailWord_1273027).sum := by decide
  have hdescent : baseEnd_1273027 < baseStart_1273027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273064 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_1273064 : Nat := 118140960795 + 1273064 * 2 ^ 59
def prefixEnd_1273064 : Nat := 4983230072969 + 3 ^ 40 * 1273064 * 2
def baseEnd_1273064 : Nat := 653693735935512364945291

theorem tailTrace_1273064 : CollatzResearch.WordTrace tailWord_1273064 prefixEnd_1273064 653693735935512364945291 := by
  unfold tailWord_1273064
  simp only [CollatzResearch.WordTrace]
  refine ⟨23216229329957012433229123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30954972439942683244305497 23216229329957012433229123)
  ·
    refine ⟨34824343994935518649843685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23216229329957012433229123 34824343994935518649843685)
    ·
      refine ⟨6529564499050409746845691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34824343994935518649843685 6529564499050409746845691)
      ·
        refine ⟨9794346748575614620268537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6529564499050409746845691 9794346748575614620268537)
        ·
          refine ⟨7345760061431710965201403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9794346748575614620268537 7345760061431710965201403)
          ·
            refine ⟨11018640092147566447802105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7345760061431710965201403 11018640092147566447802105)
            ·
              refine ⟨8263980069110674835851579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11018640092147566447802105 8263980069110674835851579)
              ·
                refine ⟨12395970103666012253777369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8263980069110674835851579 12395970103666012253777369)
                ·
                  refine ⟨9296977577749509190333027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12395970103666012253777369 9296977577749509190333027)
                  ·
                    refine ⟨13945466366624263785499541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9296977577749509190333027 13945466366624263785499541)
                    ·
                      refine ⟨653693735935512364945291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13945466366624263785499541 653693735935512364945291)
                      ·
                        rfl

theorem cell23_1273064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_1273064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273064 prefixEnd_1273064 := by exact prefixLift 1273064
  have htrace : WordTrace (prefixWord ++ tailWord_1273064) baseStart_1273064 baseEnd_1273064 := by
    simpa [prefixWord, tailWord_1273064, baseEnd_1273064] using wordTrace_append hprefix tailTrace_1273064
  have hstable : (prefixWord ++ tailWord_1273064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273064).length < 2 ^ (prefixWord ++ tailWord_1273064).sum := by decide
  have hdescent : baseEnd_1273064 < baseStart_1273064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273142 : List Nat := [5, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_1273142 : Nat := 118140960795 + 1273142 * 2 ^ 59
def prefixEnd_1273142 : Nat := 4983230072969 + 3 ^ 40 * 1273142 * 2
def baseEnd_1273142 : Nat := 72637087491840339974437

theorem tailTrace_1273142 : CollatzResearch.WordTrace tailWord_1273142 prefixEnd_1273142 72637087491840339974437 := by
  unfold tailWord_1273142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2902206472101965261737355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30956869035754296125198453 2902206472101965261737355)
  ·
    refine ⟨4353309708152947892606033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2902206472101965261737355 4353309708152947892606033)
    ·
      refine ⟨3264982281114710919454525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4353309708152947892606033 3264982281114710919454525)
      ·
        refine ⟨1224368355418016594795447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3264982281114710919454525 1224368355418016594795447)
        ·
          refine ⟨1836552533127024892193171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1224368355418016594795447 1836552533127024892193171)
          ·
            refine ⟨2754828799690537338289757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1836552533127024892193171 2754828799690537338289757)
            ·
              refine ⟨1033060799883951501858659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2754828799690537338289757 1033060799883951501858659)
              ·
                refine ⟨1549591199825927252787989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1033060799883951501858659 1549591199825927252787989)
                ·
                  refine ⟨72637087491840339974437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1549591199825927252787989 72637087491840339974437)
                  ·
                    rfl

theorem cell23_1273142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_1273142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273142 prefixEnd_1273142 := by exact prefixLift 1273142
  have htrace : WordTrace (prefixWord ++ tailWord_1273142) baseStart_1273142 baseEnd_1273142 := by
    simpa [prefixWord, tailWord_1273142, baseEnd_1273142] using wordTrace_append hprefix tailTrace_1273142
  have hstable : (prefixWord ++ tailWord_1273142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273142).length < 2 ^ (prefixWord ++ tailWord_1273142).sum := by decide
  have hdescent : baseEnd_1273142 < baseStart_1273142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273151 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 1, 6]
def baseStart_1273151 : Nat := 118140960795 + 1273151 * 2 ^ 59
def prefixEnd_1273151 : Nat := 4983230072969 + 3 ^ 40 * 1273151 * 2
def baseEnd_1273151 : Nat := 217912802917484508185797

theorem tailTrace_1273151 : CollatzResearch.WordTrace tailWord_1273151 prefixEnd_1273151 217912802917484508185797 := by
  unfold tailWord_1273151
  simp only [CollatzResearch.WordTrace]
  refine ⟨46435631810598838724875307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30957087873732559149916871 46435631810598838724875307)
  ·
    refine ⟨69653447715898258087312961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46435631810598838724875307 69653447715898258087312961)
    ·
      refine ⟨52240085786923693565484721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69653447715898258087312961 52240085786923693565484721)
      ·
        refine ⟨39180064340192770174113541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52240085786923693565484721 39180064340192770174113541)
        ·
          refine ⟨7346262063786144407646289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39180064340192770174113541 7346262063786144407646289)
          ·
            refine ⟨5509696547839608305734717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7346262063786144407646289 5509696547839608305734717)
            ·
              refine ⟨2066136205439853114650519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5509696547839608305734717 2066136205439853114650519)
              ·
                refine ⟨3099204308159779671975779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066136205439853114650519 3099204308159779671975779)
                ·
                  refine ⟨4648806462239669507963669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099204308159779671975779 4648806462239669507963669)
                  ·
                    refine ⟨217912802917484508185797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4648806462239669507963669 217912802917484508185797)
                    ·
                      rfl

theorem cell23_1273151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 6].length) (baseStart_1273151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273151 prefixEnd_1273151 := by exact prefixLift 1273151
  have htrace : WordTrace (prefixWord ++ tailWord_1273151) baseStart_1273151 baseEnd_1273151 := by
    simpa [prefixWord, tailWord_1273151, baseEnd_1273151] using wordTrace_append hprefix tailTrace_1273151
  have hstable : (prefixWord ++ tailWord_1273151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273151).length < 2 ^ (prefixWord ++ tailWord_1273151).sum := by decide
  have hdescent : baseEnd_1273151 < baseStart_1273151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273161 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 3, 2, 3]
def baseStart_1273161 : Nat := 118140960795 + 1273161 * 2 ^ 59
def prefixEnd_1273161 : Nat := 4983230072969 + 3 ^ 40 * 1273161 * 2
def baseEnd_1273161 : Nat := 653743543558998485432345

theorem tailTrace_1273161 : CollatzResearch.WordTrace tailWord_1273161 prefixEnd_1273161 653743543558998485432345 := by
  unfold tailWord_1273161
  simp only [CollatzResearch.WordTrace]
  refine ⟨46435996540562610432739337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30957331027041740288492891 46435996540562610432739337)
  ·
    refine ⟨34826997405421957824554503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46435996540562610432739337 34826997405421957824554503)
    ·
      refine ⟨52240496108132936736831755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34826997405421957824554503 52240496108132936736831755)
      ·
        refine ⟨78360744162199405105247633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52240496108132936736831755 78360744162199405105247633)
        ·
          refine ⟨58770558121649553828935725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78360744162199405105247633 58770558121649553828935725)
          ·
            refine ⟨22038959295618582685850897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58770558121649553828935725 22038959295618582685850897)
            ·
              refine ⟨16529219471713937014388173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22038959295618582685850897 16529219471713937014388173)
              ·
                refine ⟨6198457301892726380395565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16529219471713937014388173 6198457301892726380395565)
                ·
                  refine ⟨2324421488209772392648337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6198457301892726380395565 2324421488209772392648337)
                  ·
                    refine ⟨1743316116157329294486253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2324421488209772392648337 1743316116157329294486253)
                    ·
                      refine ⟨653743543558998485432345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1743316116157329294486253 653743543558998485432345)
                      ·
                        rfl

theorem cell23_1273161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 2, 3].length) (baseStart_1273161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273161 prefixEnd_1273161 := by exact prefixLift 1273161
  have htrace : WordTrace (prefixWord ++ tailWord_1273161) baseStart_1273161 baseEnd_1273161 := by
    simpa [prefixWord, tailWord_1273161, baseEnd_1273161] using wordTrace_append hprefix tailTrace_1273161
  have hstable : (prefixWord ++ tailWord_1273161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273161).length < 2 ^ (prefixWord ++ tailWord_1273161).sum := by decide
  have hdescent : baseEnd_1273161 < baseStart_1273161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273178 : List Nat := [3, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3]
def baseStart_1273178 : Nat := 118140960795 + 1273178 * 2 ^ 59
def prefixEnd_1273178 : Nat := 4983230072969 + 3 ^ 40 * 1273178 * 2
def baseEnd_1273178 : Nat := 653752272730124918919767

theorem tailTrace_1273178 : CollatzResearch.WordTrace tailWord_1273178 prefixEnd_1273178 653752272730124918919767 := by
  unfold tailWord_1273178
  simp only [CollatzResearch.WordTrace]
  refine ⟨11609154145375255584027047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30957744387667348224072125 11609154145375255584027047)
  ·
    refine ⟨17413731218062883376040571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11609154145375255584027047 17413731218062883376040571)
    ·
      refine ⟨26120596827094325064060857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17413731218062883376040571 26120596827094325064060857)
      ·
        refine ⟨19590447620320743798045643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26120596827094325064060857 19590447620320743798045643)
        ·
          refine ⟨29385671430481115697068465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19590447620320743798045643 29385671430481115697068465)
          ·
            refine ⟨22039253572860836772801349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29385671430481115697068465 22039253572860836772801349)
            ·
              refine ⟨4132360044911406894900253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22039253572860836772801349 4132360044911406894900253)
              ·
                refine ⟨1549635016841777585587595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4132360044911406894900253 1549635016841777585587595)
                ·
                  refine ⟨2324452525262666378381393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1549635016841777585587595 2324452525262666378381393)
                  ·
                    refine ⟨1743339393946999783786045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2324452525262666378381393 1743339393946999783786045)
                    ·
                      refine ⟨653752272730124918919767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1743339393946999783786045 653752272730124918919767)
                      ·
                        rfl

theorem cell23_1273178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_1273178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273178 prefixEnd_1273178 := by exact prefixLift 1273178
  have htrace : WordTrace (prefixWord ++ tailWord_1273178) baseStart_1273178 baseEnd_1273178 := by
    simpa [prefixWord, tailWord_1273178, baseEnd_1273178] using wordTrace_append hprefix tailTrace_1273178
  have hstable : (prefixWord ++ tailWord_1273178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273178).length < 2 ^ (prefixWord ++ tailWord_1273178).sum := by decide
  have hdescent : baseEnd_1273178 < baseStart_1273178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273248 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 3, 4, 2]
def baseStart_1273248 : Nat := 118140960795 + 1273248 * 2 ^ 59
def prefixEnd_1273248 : Nat := 4983230072969 + 3 ^ 40 * 1273248 * 2
def baseEnd_1273248 : Nat := 653788216375939645044445

theorem tailTrace_1273248 : CollatzResearch.WordTrace tailWord_1273248 prefixEnd_1273248 653788216375939645044445 := by
  unfold tailWord_1273248
  simp only [CollatzResearch.WordTrace]
  refine ⟨23219584845623712145578199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30959446460831616194104265 23219584845623712145578199)
  ·
    refine ⟨34829377268435568218367299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23219584845623712145578199 34829377268435568218367299)
    ·
      refine ⟨52244065902653352327550949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34829377268435568218367299 52244065902653352327550949)
      ·
        refine ⟨9795762356747503561415803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52244065902653352327550949 9795762356747503561415803)
        ·
          refine ⟨14693643535121255342123705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9795762356747503561415803 14693643535121255342123705)
          ·
            refine ⟨11020232651340941506592779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14693643535121255342123705 11020232651340941506592779)
            ·
              refine ⟨16530348977011412259889169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11020232651340941506592779 16530348977011412259889169)
              ·
                refine ⟨12397761732758559194916877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16530348977011412259889169 12397761732758559194916877)
                ·
                  refine ⟨4649160649784459698093829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12397761732758559194916877 4649160649784459698093829)
                  ·
                    refine ⟨871717621834586193392593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4649160649784459698093829 871717621834586193392593)
                    ·
                      refine ⟨653788216375939645044445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871717621834586193392593 653788216375939645044445)
                      ·
                        rfl

theorem cell23_1273248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_1273248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273248 prefixEnd_1273248 := by exact prefixLift 1273248
  have htrace : WordTrace (prefixWord ++ tailWord_1273248) baseStart_1273248 baseEnd_1273248 := by
    simpa [prefixWord, tailWord_1273248, baseEnd_1273248] using wordTrace_append hprefix tailTrace_1273248
  have hstable : (prefixWord ++ tailWord_1273248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273248).length < 2 ^ (prefixWord ++ tailWord_1273248).sum := by decide
  have hdescent : baseEnd_1273248 < baseStart_1273248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273251 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 3]
def baseStart_1273251 : Nat := 118140960795 + 1273251 * 2 ^ 59
def prefixEnd_1273251 : Nat := 4983230072969 + 3 ^ 40 * 1273251 * 2
def baseEnd_1273251 : Nat := 653789756817903133306931

theorem tailTrace_1273251 : CollatzResearch.WordTrace tailWord_1273251 prefixEnd_1273251 653789756817903133306931 := by
  unfold tailWord_1273251
  simp only [CollatzResearch.WordTrace]
  refine ⟨46439279110236555803515607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30959519406824370535677071 46439279110236555803515607)
  ·
    refine ⟨69658918665354833705273411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46439279110236555803515607 69658918665354833705273411)
    ·
      refine ⟨104488377998032250557910117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69658918665354833705273411 104488377998032250557910117)
      ·
        refine ⟨19591570874631046979608147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104488377998032250557910117 19591570874631046979608147)
        ·
          refine ⟨29387356311946570469412221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19591570874631046979608147 29387356311946570469412221)
          ·
            refine ⟨11020258616979963926029583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29387356311946570469412221 11020258616979963926029583)
            ·
              refine ⟨16530387925469945889044375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11020258616979963926029583 16530387925469945889044375)
              ·
                refine ⟨24795581888204918833566563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16530387925469945889044375 24795581888204918833566563)
                ·
                  refine ⟨37193372832307378250349845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24795581888204918833566563 37193372832307378250349845)
                  ·
                    refine ⟨1743439351514408355485149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37193372832307378250349845 1743439351514408355485149)
                    ·
                      refine ⟨653789756817903133306931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1743439351514408355485149 653789756817903133306931)
                      ·
                        rfl

theorem cell23_1273251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_1273251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273251 prefixEnd_1273251 := by exact prefixLift 1273251
  have htrace : WordTrace (prefixWord ++ tailWord_1273251) baseStart_1273251 baseEnd_1273251 := by
    simpa [prefixWord, tailWord_1273251, baseEnd_1273251] using wordTrace_append hprefix tailTrace_1273251
  have hstable : (prefixWord ++ tailWord_1273251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273251).length < 2 ^ (prefixWord ++ tailWord_1273251).sum := by decide
  have hdescent : baseEnd_1273251 < baseStart_1273251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273265 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 1, 4, 2]
def baseStart_1273265 : Nat := 118140960795 + 1273265 * 2 ^ 59
def prefixEnd_1273265 : Nat := 4983230072969 + 3 ^ 40 * 1273265 * 2
def baseEnd_1273265 : Nat := 653796945547066078531867

theorem tailTrace_1273265 : CollatzResearch.WordTrace tailWord_1273265 prefixEnd_1273265 653796945547066078531867 := by
  unfold tailWord_1273265
  simp only [CollatzResearch.WordTrace]
  refine ⟨46439789732185836194525249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30959859821457224129683499 46439789732185836194525249)
  ·
    refine ⟨34829842299139377145893937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46439789732185836194525249 34829842299139377145893937)
    ·
      refine ⟨26122381724354532859420453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34829842299139377145893937 26122381724354532859420453)
      ·
        refine ⟨4897946573316474911141335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26122381724354532859420453 4897946573316474911141335)
        ·
          refine ⟨7346919859974712366712003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4897946573316474911141335 7346919859974712366712003)
          ·
            refine ⟨11020379789962068550068005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7346919859974712366712003 11020379789962068550068005)
            ·
              refine ⟨2066321210617887853137751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11020379789962068550068005 2066321210617887853137751)
              ·
                refine ⟨3099481815926831779706627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066321210617887853137751 3099481815926831779706627)
                ·
                  refine ⟨4649222723890247669559941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099481815926831779706627 4649222723890247669559941)
                  ·
                    refine ⟨871729260729421438042489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4649222723890247669559941 871729260729421438042489)
                    ·
                      refine ⟨653796945547066078531867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871729260729421438042489 653796945547066078531867)
                      ·
                        rfl

theorem cell23_1273265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_1273265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273265 prefixEnd_1273265 := by exact prefixLift 1273265
  have htrace : WordTrace (prefixWord ++ tailWord_1273265) baseStart_1273265 baseEnd_1273265 := by
    simpa [prefixWord, tailWord_1273265, baseEnd_1273265] using wordTrace_append hprefix tailTrace_1273265
  have hstable : (prefixWord ++ tailWord_1273265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273265).length < 2 ^ (prefixWord ++ tailWord_1273265).sum := by decide
  have hdescent : baseEnd_1273265 < baseStart_1273265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273271 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 7]
def baseStart_1273271 : Nat := 118140960795 + 1273271 * 2 ^ 59
def prefixEnd_1273271 : Nat := 4983230072969 + 3 ^ 40 * 1273271 * 2
def baseEnd_1273271 : Nat := 72644447381221450561871

theorem tailTrace_1273271 : CollatzResearch.WordTrace tailWord_1273271 prefixEnd_1273271 72644447381221450561871 := by
  unfold tailWord_1273271
  simp only [CollatzResearch.WordTrace]
  refine ⟨46440008570164099219243667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30960005713442732812829111 46440008570164099219243667)
  ·
    refine ⟨69660012855246148828865501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46440008570164099219243667 69660012855246148828865501)
    ·
      refine ⟨26122504820717305810824563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69660012855246148828865501 26122504820717305810824563)
      ·
        refine ⟨39183757231075958716236845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26122504820717305810824563 39183757231075958716236845)
        ·
          refine ⟨14693908961653484518588817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39183757231075958716236845 14693908961653484518588817)
          ·
            refine ⟨11020431721240113388941613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14693908961653484518588817 11020431721240113388941613)
            ·
              refine ⟨4132661895465042520853105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11020431721240113388941613 4132661895465042520853105)
              ·
                refine ⟨3099496421598781890639829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4132661895465042520853105 3099496421598781890639829)
                ·
                  refine ⟨72644447381221450561871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3099496421598781890639829 72644447381221450561871)
                  ·
                    rfl

theorem cell23_1273271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 7].length) (baseStart_1273271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273271 prefixEnd_1273271 := by exact prefixLift 1273271
  have htrace : WordTrace (prefixWord ++ tailWord_1273271) baseStart_1273271 baseEnd_1273271 := by
    simpa [prefixWord, tailWord_1273271, baseEnd_1273271] using wordTrace_append hprefix tailTrace_1273271
  have hstable : (prefixWord ++ tailWord_1273271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273271).length < 2 ^ (prefixWord ++ tailWord_1273271).sum := by decide
  have hdescent : baseEnd_1273271 < baseStart_1273271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273311 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 7]
def baseStart_1273311 : Nat := 118140960795 + 1273311 * 2 ^ 59
def prefixEnd_1273311 : Nat := 4983230072969 + 3 ^ 40 * 1273311 * 2
def baseEnd_1273311 : Nat := 653820565657172898556655

theorem tailTrace_1273311 : CollatzResearch.WordTrace tailWord_1273311 prefixEnd_1273311 653820565657172898556655 := by
  unfold tailWord_1273311
  simp only [CollatzResearch.WordTrace]
  refine ⟨46441467490019186050699787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30960978326679457367133191 46441467490019186050699787)
  ·
    refine ⟨69662201235028779076049681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46441467490019186050699787 69662201235028779076049681)
    ·
      refine ⟨52246650926271584307037261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69662201235028779076049681 52246650926271584307037261)
      ·
        refine ⟨19592494097351844115138973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52246650926271584307037261 19592494097351844115138973)
        ·
          refine ⟨7347185286506941543177115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19592494097351844115138973 7347185286506941543177115)
          ·
            refine ⟨11020777929760412314765673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7347185286506941543177115 11020777929760412314765673)
            ·
              refine ⟨8265583447320309236074255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11020777929760412314765673 8265583447320309236074255)
              ·
                refine ⟨12398375170980463854111383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8265583447320309236074255 12398375170980463854111383)
                ·
                  refine ⟨18597562756470695781167075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12398375170980463854111383 18597562756470695781167075)
                  ·
                    refine ⟨27896344134706043671750613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18597562756470695781167075 27896344134706043671750613)
                    ·
                      refine ⟨653820565657172898556655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27896344134706043671750613 653820565657172898556655)
                      ·
                        rfl

theorem cell23_1273311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_1273311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273311 prefixEnd_1273311 := by exact prefixLift 1273311
  have htrace : WordTrace (prefixWord ++ tailWord_1273311) baseStart_1273311 baseEnd_1273311 := by
    simpa [prefixWord, tailWord_1273311, baseEnd_1273311] using wordTrace_append hprefix tailTrace_1273311
  have hstable : (prefixWord ++ tailWord_1273311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273311).length < 2 ^ (prefixWord ++ tailWord_1273311).sum := by decide
  have hdescent : baseEnd_1273311 < baseStart_1273311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273338 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4]
def baseStart_1273338 : Nat := 118140960795 + 1273338 * 2 ^ 59
def prefixEnd_1273338 : Nat := 4983230072969 + 3 ^ 40 * 1273338 * 2
def baseEnd_1273338 : Nat := 653834429634844292919031

theorem tailTrace_1273338 : CollatzResearch.WordTrace tailWord_1273338 prefixEnd_1273338 653834429634844292919031 := by
  unfold tailWord_1273338
  simp only [CollatzResearch.WordTrace]
  refine ⟨11610613065230342415483167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30961634840614246441288445 11610613065230342415483167)
  ·
    refine ⟨17415919597845513623224751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11610613065230342415483167 17415919597845513623224751)
    ·
      refine ⟨26123879396768270434837127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17415919597845513623224751 26123879396768270434837127)
      ·
        refine ⟨39185819095152405652255691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26123879396768270434837127 39185819095152405652255691)
        ·
          refine ⟨58778728642728608478383537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39185819095152405652255691 58778728642728608478383537)
          ·
            refine ⟨44084046482046456358787653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58778728642728608478383537 44084046482046456358787653)
            ·
              refine ⟨8265758715383710567272685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44084046482046456358787653 8265758715383710567272685)
              ·
                refine ⟨3099659518268891462727257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8265758715383710567272685 3099659518268891462727257)
                ·
                  refine ⟨2324744638701668597045443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3099659518268891462727257 2324744638701668597045443)
                  ·
                    refine ⟨3487116958052502895568165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2324744638701668597045443 3487116958052502895568165)
                    ·
                      refine ⟨653834429634844292919031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3487116958052502895568165 653834429634844292919031)
                      ·
                        rfl

theorem cell23_1273338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_1273338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273338 prefixEnd_1273338 := by exact prefixLift 1273338
  have htrace : WordTrace (prefixWord ++ tailWord_1273338) baseStart_1273338 baseEnd_1273338 := by
    simpa [prefixWord, tailWord_1273338, baseEnd_1273338] using wordTrace_append hprefix tailTrace_1273338
  have hstable : (prefixWord ++ tailWord_1273338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273338).length < 2 ^ (prefixWord ++ tailWord_1273338).sum := by decide
  have hdescent : baseEnd_1273338 < baseStart_1273338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273355 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 4]
def baseStart_1273355 : Nat := 118140960795 + 1273355 * 2 ^ 59
def prefixEnd_1273355 : Nat := 4983230072969 + 3 ^ 40 * 1273355 * 2
def baseEnd_1273355 : Nat := 653843158805970726406453

theorem tailTrace_1273355 : CollatzResearch.WordTrace tailWord_1273355 prefixEnd_1273355 653843158805970726406453 := by
  unfold tailWord_1273355
  simp only [CollatzResearch.WordTrace]
  refine ⟨46443072301859781565301519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30962048201239854376867679 46443072301859781565301519)
  ·
    refine ⟨69664608452789672347952279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46443072301859781565301519 69664608452789672347952279)
    ·
      refine ⟨104496912679184508521928419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69664608452789672347952279 104496912679184508521928419)
      ·
        refine ⟨156745369018776762782892629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104496912679184508521928419 156745369018776762782892629)
        ·
          refine ⟨1836859793188790188862023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 156745369018776762782892629 1836859793188790188862023)
          ·
            refine ⟨2755289689783185283293035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1836859793188790188862023 2755289689783185283293035)
            ·
              refine ⟨4132934534674777924939553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2755289689783185283293035 4132934534674777924939553)
              ·
                refine ⟨3099700901006083443704665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4132934534674777924939553 3099700901006083443704665)
                ·
                  refine ⟨2324775675754562582778499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3099700901006083443704665 2324775675754562582778499)
                  ·
                    refine ⟨3487163513631843874167749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2324775675754562582778499 3487163513631843874167749)
                    ·
                      refine ⟨653843158805970726406453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3487163513631843874167749 653843158805970726406453)
                      ·
                        rfl

theorem cell23_1273355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 4].length) (baseStart_1273355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273355 prefixEnd_1273355 := by exact prefixLift 1273355
  have htrace : WordTrace (prefixWord ++ tailWord_1273355) baseStart_1273355 baseEnd_1273355 := by
    simpa [prefixWord, tailWord_1273355, baseEnd_1273355] using wordTrace_append hprefix tailTrace_1273355
  have hstable : (prefixWord ++ tailWord_1273355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273355).length < 2 ^ (prefixWord ++ tailWord_1273355).sum := by decide
  have hdescent : baseEnd_1273355 < baseStart_1273355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273361 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 8]
def baseStart_1273361 : Nat := 118140960795 + 1273361 * 2 ^ 59
def prefixEnd_1273361 : Nat := 4983230072969 + 3 ^ 40 * 1273361 * 2
def baseEnd_1273361 : Nat := 72649582187766411436825

theorem tailTrace_1273361 : CollatzResearch.WordTrace tailWord_1273361 prefixEnd_1273361 72649582187766411436825 := by
  unfold tailWord_1273361
  simp only [CollatzResearch.WordTrace]
  refine ⟨46443291139838044590019937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30962194093225363060013291 46443291139838044590019937)
  ·
    refine ⟨34832468354878533442514953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46443291139838044590019937 34832468354878533442514953)
    ·
      refine ⟨26124351266158900081886215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34832468354878533442514953 26124351266158900081886215)
      ·
        refine ⟨39186526899238350122829323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26124351266158900081886215 39186526899238350122829323)
        ·
          refine ⟨58779790348857525184243985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39186526899238350122829323 58779790348857525184243985)
          ·
            refine ⟨44084842761643143888182989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58779790348857525184243985 44084842761643143888182989)
            ·
              refine ⟨16531816035616178958068621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44084842761643143888182989 16531816035616178958068621)
              ·
                refine ⟨6199431013356067109275733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16531816035616178958068621 6199431013356067109275733)
                ·
                  refine ⟨72649582187766411436825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6199431013356067109275733 72649582187766411436825)
                  ·
                    rfl

theorem cell23_1273361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 8].length) (baseStart_1273361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273361 prefixEnd_1273361 := by exact prefixLift 1273361
  have htrace : WordTrace (prefixWord ++ tailWord_1273361) baseStart_1273361 baseEnd_1273361 := by
    simpa [prefixWord, tailWord_1273361, baseEnd_1273361] using wordTrace_append hprefix tailTrace_1273361
  have hstable : (prefixWord ++ tailWord_1273361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273361).length < 2 ^ (prefixWord ++ tailWord_1273361).sum := by decide
  have hdescent : baseEnd_1273361 < baseStart_1273361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273365 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 3, 4]
def baseStart_1273365 : Nat := 118140960795 + 1273365 * 2 ^ 59
def prefixEnd_1273365 : Nat := 4983230072969 + 3 ^ 40 * 1273365 * 2
def baseEnd_1273365 : Nat := 217949431204171895760469

theorem tailTrace_1273365 : CollatzResearch.WordTrace tailWord_1273365 prefixEnd_1273365 217949431204171895760469 := by
  unfold tailWord_1273365
  simp only [CollatzResearch.WordTrace]
  refine ⟨46443437031823553273165549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30962291354549035515443699 46443437031823553273165549)
  ·
    refine ⟨17416288886933832477437081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46443437031823553273165549 17416288886933832477437081)
    ·
      refine ⟨13062216665200374358077811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17416288886933832477437081 13062216665200374358077811)
      ·
        refine ⟨19593324997800561537116717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13062216665200374358077811 19593324997800561537116717)
        ·
          refine ⟨7347496874175210576418769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19593324997800561537116717 7347496874175210576418769)
          ·
            refine ⟨5510622655631407932314077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7347496874175210576418769 5510622655631407932314077)
            ·
              refine ⟨2066483495861777974617779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5510622655631407932314077 2066483495861777974617779)
              ·
                refine ⟨3099725243792666961926669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066483495861777974617779 3099725243792666961926669)
                ·
                  refine ⟨1162396966422250110722501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3099725243792666961926669 1162396966422250110722501)
                  ·
                    refine ⟨217949431204171895760469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1162396966422250110722501 217949431204171895760469)
                    ·
                      rfl

theorem cell23_1273365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_1273365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273365 prefixEnd_1273365 := by exact prefixLift 1273365
  have htrace : WordTrace (prefixWord ++ tailWord_1273365) baseStart_1273365 baseEnd_1273365 := by
    simpa [prefixWord, tailWord_1273365, baseEnd_1273365] using wordTrace_append hprefix tailTrace_1273365
  have hstable : (prefixWord ++ tailWord_1273365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273365).length < 2 ^ (prefixWord ++ tailWord_1273365).sum := by decide
  have hdescent : baseEnd_1273365 < baseStart_1273365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273445 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 3, 1, 4]
def baseStart_1273445 : Nat := 118140960795 + 1273445 * 2 ^ 59
def prefixEnd_1273445 : Nat := 4983230072969 + 3 ^ 40 * 1273445 * 2
def baseEnd_1273445 : Nat := 653889372064875374281039

theorem tailTrace_1273445 : CollatzResearch.WordTrace tailWord_1273445 prefixEnd_1273445 653889372064875374281039 := by
  unfold tailWord_1273445
  simp only [CollatzResearch.WordTrace]
  refine ⟨46446354871533726936077789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30964236581022484624051859 46446354871533726936077789)
  ·
    refine ⟨17417383076825147601029171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46446354871533726936077789 17417383076825147601029171)
    ·
      refine ⟨26126074615237721401543757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17417383076825147601029171 26126074615237721401543757)
      ·
        refine ⟨9797277980714145525578909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26126074615237721401543757 9797277980714145525578909)
        ·
          refine ⟨3673979242767804572092091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9797277980714145525578909 3673979242767804572092091)
          ·
            refine ⟨5510968864151706858138137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3673979242767804572092091 5510968864151706858138137)
            ·
              refine ⟨4133226648113780143603603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5510968864151706858138137 4133226648113780143603603)
              ·
                refine ⟨6199839972170670215405405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4133226648113780143603603 6199839972170670215405405)
                ·
                  refine ⟨2324939989564001330777027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6199839972170670215405405 2324939989564001330777027)
                  ·
                    refine ⟨3487409984346001996165541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2324939989564001330777027 3487409984346001996165541)
                    ·
                      refine ⟨653889372064875374281039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3487409984346001996165541 653889372064875374281039)
                      ·
                        rfl

theorem cell23_1273445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_1273445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273445 prefixEnd_1273445 := by exact prefixLift 1273445
  have htrace : WordTrace (prefixWord ++ tailWord_1273445) baseStart_1273445 baseEnd_1273445 := by
    simpa [prefixWord, tailWord_1273445, baseEnd_1273445] using wordTrace_append hprefix tailTrace_1273445
  have hstable : (prefixWord ++ tailWord_1273445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273445).length < 2 ^ (prefixWord ++ tailWord_1273445).sum := by decide
  have hdescent : baseEnd_1273445 < baseStart_1273445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273479 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 3, 2, 2]
def baseStart_1273479 : Nat := 118140960795 + 1273479 * 2 ^ 59
def prefixEnd_1273479 : Nat := 4983230072969 + 3 ^ 40 * 1273479 * 2
def baseEnd_1273479 : Nat := 653906830407128241255883

theorem tailTrace_1273479 : CollatzResearch.WordTrace tailWord_1273479 prefixEnd_1273479 653906830407128241255883 := by
  unfold tailWord_1273479
  simp only [CollatzResearch.WordTrace]
  refine ⟨46447594953410550742815491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30965063302273700495210327 46447594953410550742815491)
  ·
    refine ⟨69671392430115826114223237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46447594953410550742815491 69671392430115826114223237)
    ·
      refine ⟨13063386080646717396416857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69671392430115826114223237 13063386080646717396416857)
      ·
        refine ⟨9797539560485038047312643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13063386080646717396416857 9797539560485038047312643)
        ·
          refine ⟨14696309340727557070968965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9797539560485038047312643 14696309340727557070968965)
          ·
            refine ⟨2755558001386416950806681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14696309340727557070968965 2755558001386416950806681)
            ·
              refine ⟨2066668501039812713105011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2755558001386416950806681 2066668501039812713105011)
              ·
                refine ⟨3100002751559719069657517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066668501039812713105011 3100002751559719069657517)
                ·
                  refine ⟨1162501031834894651121569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3100002751559719069657517 1162501031834894651121569)
                  ·
                    refine ⟨871875773876170988341177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1162501031834894651121569 871875773876170988341177)
                    ·
                      refine ⟨653906830407128241255883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871875773876170988341177 653906830407128241255883)
                      ·
                        rfl

theorem cell23_1273479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_1273479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273479 prefixEnd_1273479 := by exact prefixLift 1273479
  have htrace : WordTrace (prefixWord ++ tailWord_1273479) baseStart_1273479 baseEnd_1273479 := by
    simpa [prefixWord, tailWord_1273479, baseEnd_1273479] using wordTrace_append hprefix tailTrace_1273479
  have hstable : (prefixWord ++ tailWord_1273479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273479).length < 2 ^ (prefixWord ++ tailWord_1273479).sum := by decide
  have hdescent : baseEnd_1273479 < baseStart_1273479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273492 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1273492 : Nat := 118140960795 + 1273492 * 2 ^ 59
def prefixEnd_1273492 : Nat := 4983230072969 + 3 ^ 40 * 1273492 * 2
def baseEnd_1273492 : Nat := 653913505655636690393323

theorem tailTrace_1273492 : CollatzResearch.WordTrace tailWord_1273492 prefixEnd_1273492 653913505655636690393323 := by
  unfold tailWord_1273492
  simp only [CollatzResearch.WordTrace]
  refine ⟨23224034551181726981519365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30965379401575635975359153 23224034551181726981519365)
  ·
    refine ⟨4354506478346573809034881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23224034551181726981519365 4354506478346573809034881)
    ·
      refine ⟨3265879858759930356776161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4354506478346573809034881 3265879858759930356776161)
      ·
        refine ⟨2449409894069947767582121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3265879858759930356776161 2449409894069947767582121)
        ·
          refine ⟨1837057420552460825686591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2449409894069947767582121 1837057420552460825686591)
          ·
            refine ⟨2755586130828691238529887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837057420552460825686591 2755586130828691238529887)
            ·
              refine ⟨4133379196243036857794831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2755586130828691238529887 4133379196243036857794831)
              ·
                refine ⟨6200068794364555286692247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4133379196243036857794831 6200068794364555286692247)
                ·
                  refine ⟨9300103191546832930038371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6200068794364555286692247 9300103191546832930038371)
                  ·
                    refine ⟨13950154787320249395057557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9300103191546832930038371 13950154787320249395057557)
                    ·
                      refine ⟨653913505655636690393323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13950154787320249395057557 653913505655636690393323)
                      ·
                        rfl

theorem cell23_1273492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1273492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273492 prefixEnd_1273492 := by exact prefixLift 1273492
  have htrace : WordTrace (prefixWord ++ tailWord_1273492) baseStart_1273492 baseEnd_1273492 := by
    simpa [prefixWord, tailWord_1273492, baseEnd_1273492] using wordTrace_append hprefix tailTrace_1273492
  have hstable : (prefixWord ++ tailWord_1273492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273492).length < 2 ^ (prefixWord ++ tailWord_1273492).sum := by decide
  have hdescent : baseEnd_1273492 < baseStart_1273492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273502 : List Nat := [4, 3, 1, 1, 1, 2, 4, 7]
def baseStart_1273502 : Nat := 118140960795 + 1273502 * 2 ^ 59
def prefixEnd_1273502 : Nat := 4983230072969 + 3 ^ 40 * 1273502 * 2
def baseEnd_1273502 : Nat := 24219208906006727824751

theorem tailTrace_1273502 : CollatzResearch.WordTrace tailWord_1273502 prefixEnd_1273502 24219208906006727824751 := by
  unfold tailWord_1273502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5806054229040903208862845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30965622554884817113935173 5806054229040903208862845)
  ·
    refine ⟨2177270335890338703323567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5806054229040903208862845 2177270335890338703323567)
    ·
      refine ⟨3265905503835508054985351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2177270335890338703323567 3265905503835508054985351)
      ·
        refine ⟨4898858255753262082478027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3265905503835508054985351 4898858255753262082478027)
        ·
          refine ⟨7348287383629893123717041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4898858255753262082478027 7348287383629893123717041)
          ·
            refine ⟨5511215537722419842787781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7348287383629893123717041 5511215537722419842787781)
            ·
              refine ⟨1033352913322953720522709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5511215537722419842787781 1033352913322953720522709)
              ·
                refine ⟨24219208906006727824751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1033352913322953720522709 24219208906006727824751)
                ·
                  rfl

theorem cell23_1273502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_1273502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273502 prefixEnd_1273502 := by exact prefixLift 1273502
  have htrace : WordTrace (prefixWord ++ tailWord_1273502) baseStart_1273502 baseEnd_1273502 := by
    simpa [prefixWord, tailWord_1273502, baseEnd_1273502] using wordTrace_append hprefix tailTrace_1273502
  have hstable : (prefixWord ++ tailWord_1273502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273502).length < 2 ^ (prefixWord ++ tailWord_1273502).sum := by decide
  have hdescent : baseEnd_1273502 < baseStart_1273502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273528 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 4, 6]
def baseStart_1273528 : Nat := 118140960795 + 1273528 * 2 ^ 59
def prefixEnd_1273528 : Nat := 4983230072969 + 3 ^ 40 * 1273528 * 2
def baseEnd_1273528 : Nat := 217977330319732849847719

theorem tailTrace_1273528 : CollatzResearch.WordTrace tailWord_1273528 prefixEnd_1273528 217977330319732849847719 := by
  unfold tailWord_1273528
  simp only [CollatzResearch.WordTrace]
  refine ⟨23224691065116516055674619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30966254753488688074232825 23224691065116516055674619)
  ·
    refine ⟨34837036597674774083511929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23224691065116516055674619 34837036597674774083511929)
    ·
      refine ⟨26127777448256080562633947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34837036597674774083511929 26127777448256080562633947)
      ·
        refine ⟨39191666172384120843950921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26127777448256080562633947 39191666172384120843950921)
        ·
          refine ⟨29393749629288090632963191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39191666172384120843950921 29393749629288090632963191)
          ·
            refine ⟨44090624443932135949444787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29393749629288090632963191 44090624443932135949444787)
            ·
              refine ⟨66135936665898203924167181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44090624443932135949444787 66135936665898203924167181)
              ·
                refine ⟨24800976249711826471562693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66135936665898203924167181 24800976249711826471562693)
                ·
                  refine ⟨4650183046820967463418005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24800976249711826471562693 4650183046820967463418005)
                  ·
                    refine ⟨217977330319732849847719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4650183046820967463418005 217977330319732849847719)
                    ·
                      rfl

theorem cell23_1273528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_1273528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273528 prefixEnd_1273528 := by exact prefixLift 1273528
  have htrace : WordTrace (prefixWord ++ tailWord_1273528) baseStart_1273528 baseEnd_1273528 := by
    simpa [prefixWord, tailWord_1273528, baseEnd_1273528] using wordTrace_append hprefix tailTrace_1273528
  have hstable : (prefixWord ++ tailWord_1273528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273528).length < 2 ^ (prefixWord ++ tailWord_1273528).sum := by decide
  have hdescent : baseEnd_1273528 < baseStart_1273528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273552 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 6, 2, 2]
def baseStart_1273552 : Nat := 118140960795 + 1273552 * 2 ^ 59
def prefixEnd_1273552 : Nat := 4983230072969 + 3 ^ 40 * 1273552 * 2
def baseEnd_1273552 : Nat := 653944314494906455643047

theorem tailTrace_1273552 : CollatzResearch.WordTrace tailWord_1273552 prefixEnd_1273552 653944314494906455643047 := by
  unfold tailWord_1273552
  simp only [CollatzResearch.WordTrace]
  refine ⟨23225128741073042105111455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30966838321430722806815273 23225128741073042105111455)
  ·
    refine ⟨34837693111609563157667183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23225128741073042105111455 34837693111609563157667183)
    ·
      refine ⟨52256539667414344736500775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34837693111609563157667183 52256539667414344736500775)
      ·
        refine ⟨78384809501121517104751163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52256539667414344736500775 78384809501121517104751163)
        ·
          refine ⟨117577214251682275657126745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78384809501121517104751163 117577214251682275657126745)
          ·
            refine ⟨88182910688761706742845059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117577214251682275657126745 88182910688761706742845059)
            ·
              refine ⟨132274366033142560114267589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88182910688761706742845059 132274366033142560114267589)
              ·
                refine ⟨24801443631214230021425173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132274366033142560114267589 24801443631214230021425173)
                ·
                  refine ⟨1162567670213167032254305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24801443631214230021425173 1162567670213167032254305)
                  ·
                    refine ⟨871925752659875274190729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1162567670213167032254305 871925752659875274190729)
                    ·
                      refine ⟨653944314494906455643047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871925752659875274190729 653944314494906455643047)
                      ·
                        rfl

theorem cell23_1273552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 6, 2, 2].length) (baseStart_1273552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273552 prefixEnd_1273552 := by exact prefixLift 1273552
  have htrace : WordTrace (prefixWord ++ tailWord_1273552) baseStart_1273552 baseEnd_1273552 := by
    simpa [prefixWord, tailWord_1273552, baseEnd_1273552] using wordTrace_append hprefix tailTrace_1273552
  have hstable : (prefixWord ++ tailWord_1273552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273552).length < 2 ^ (prefixWord ++ tailWord_1273552).sum := by decide
  have hdescent : baseEnd_1273552 < baseStart_1273552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273556 : List Nat := [2, 4, 1, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_1273556 : Nat := 118140960795 + 1273556 * 2 ^ 59
def prefixEnd_1273556 : Nat := 4983230072969 + 3 ^ 40 * 1273556 * 2
def baseEnd_1273556 : Nat := 653946368417524439993029

theorem tailTrace_1273556 : CollatzResearch.WordTrace tailWord_1273556 prefixEnd_1273556 653946368417524439993029 := by
  unfold tailWord_1273556
  simp only [CollatzResearch.WordTrace]
  refine ⟨23225201687065796446684261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30966935582754395262245681 23225201687065796446684261)
  ·
    refine ⟨4354725316324836833753299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23225201687065796446684261 4354725316324836833753299)
    ·
      refine ⟨6532087974487255250629949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4354725316324836833753299 6532087974487255250629949)
      ·
        refine ⟨2449532990432720718986231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6532087974487255250629949 2449532990432720718986231)
        ·
          refine ⟨3674299485649081078479347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2449532990432720718986231 3674299485649081078479347)
          ·
            refine ⟨5511449228473621617719021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674299485649081078479347 5511449228473621617719021)
            ·
              refine ⟨2066793460677608106644633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5511449228473621617719021 2066793460677608106644633)
              ·
                refine ⟨1550095095508206079983475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2066793460677608106644633 1550095095508206079983475)
                ·
                  refine ⟨2325142643262309119975213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550095095508206079983475 2325142643262309119975213)
                  ·
                    refine ⟨871928491223365919990705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2325142643262309119975213 871928491223365919990705)
                    ·
                      refine ⟨653946368417524439993029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871928491223365919990705 653946368417524439993029)
                      ·
                        rfl

theorem cell23_1273556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_1273556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273556 prefixEnd_1273556 := by exact prefixLift 1273556
  have htrace : WordTrace (prefixWord ++ tailWord_1273556) baseStart_1273556 baseEnd_1273556 := by
    simpa [prefixWord, tailWord_1273556, baseEnd_1273556] using wordTrace_append hprefix tailTrace_1273556
  have hstable : (prefixWord ++ tailWord_1273556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273556).length < 2 ^ (prefixWord ++ tailWord_1273556).sum := by decide
  have hdescent : baseEnd_1273556 < baseStart_1273556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273569 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 1, 4, 2]
def baseStart_1273569 : Nat := 118140960795 + 1273569 * 2 ^ 59
def prefixEnd_1273569 : Nat := 4983230072969 + 3 ^ 40 * 1273569 * 2
def baseEnd_1273569 : Nat := 653953043666032889130469

theorem tailTrace_1273569 : CollatzResearch.WordTrace tailWord_1273569 prefixEnd_1273569 653953043666032889130469 := by
  unfold tailWord_1273569
  simp only [CollatzResearch.WordTrace]
  refine ⟨46450877523084496113591761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30967251682056330742394507 46450877523084496113591761)
  ·
    refine ⟨34838158142313372085193821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46450877523084496113591761 34838158142313372085193821)
    ·
      refine ⟨13064309303367514531947683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34838158142313372085193821 13064309303367514531947683)
      ·
        refine ⟨19596463955051271797921525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13064309303367514531947683 19596463955051271797921525)
        ·
          refine ⟨1837168495786056731055143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19596463955051271797921525 1837168495786056731055143)
          ·
            refine ⟨2755752743679085096582715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837168495786056731055143 2755752743679085096582715)
            ·
              refine ⟨4133629115518627644874073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2755752743679085096582715 4133629115518627644874073)
              ·
                refine ⟨3100221836638970733655555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4133629115518627644874073 3100221836638970733655555)
                ·
                  refine ⟨4650332754958456100483333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100221836638970733655555 4650332754958456100483333)
                  ·
                    refine ⟨871937391554710518840625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4650332754958456100483333 871937391554710518840625)
                    ·
                      refine ⟨653953043666032889130469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871937391554710518840625 653953043666032889130469)
                      ·
                        rfl

theorem cell23_1273569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_1273569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273569 prefixEnd_1273569 := by exact prefixLift 1273569
  have htrace : WordTrace (prefixWord ++ tailWord_1273569) baseStart_1273569 baseEnd_1273569 := by
    simpa [prefixWord, tailWord_1273569, baseEnd_1273569] using wordTrace_append hprefix tailTrace_1273569
  have hstable : (prefixWord ++ tailWord_1273569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273569).length < 2 ^ (prefixWord ++ tailWord_1273569).sum := by decide
  have hdescent : baseEnd_1273569 < baseStart_1273569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273586 : List Nat := [3, 2, 1, 3, 1, 1, 4, 2, 2, 2, 2]
def baseStart_1273586 : Nat := 118140960795 + 1273586 * 2 ^ 59
def prefixEnd_1273586 : Nat := 4983230072969 + 3 ^ 40 * 1273586 * 2
def baseEnd_1273586 : Nat := 653961772837159322617891

theorem tailTrace_1273586 : CollatzResearch.WordTrace tailWord_1273586 prefixEnd_1273586 653961772837159322617891 := by
  unfold tailWord_1273586
  simp only [CollatzResearch.WordTrace]
  refine ⟨11612874391005727004240153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30967665042681938677973741 11612874391005727004240153)
  ·
    refine ⟨8709655793254295253180115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11612874391005727004240153 8709655793254295253180115)
    ·
      refine ⟨13064483689881442879770173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8709655793254295253180115 13064483689881442879770173)
      ·
        refine ⟨4899181383705541079913815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13064483689881442879770173 4899181383705541079913815)
        ·
          refine ⟨7348772075558311619870723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4899181383705541079913815 7348772075558311619870723)
          ·
            refine ⟨11023158113337467429806085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7348772075558311619870723 11023158113337467429806085)
            ·
              refine ⟨2066842146250775143088641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11023158113337467429806085 2066842146250775143088641)
              ·
                refine ⟨1550131609688081357316481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2066842146250775143088641 1550131609688081357316481)
                ·
                  refine ⟨1162598707266061017987361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1550131609688081357316481 1162598707266061017987361)
                  ·
                    refine ⟨871949030449545763490521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1162598707266061017987361 871949030449545763490521)
                    ·
                      refine ⟨653961772837159322617891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 871949030449545763490521 653961772837159322617891)
                      ·
                        rfl

theorem cell23_1273586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_1273586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273586 prefixEnd_1273586 := by exact prefixLift 1273586
  have htrace : WordTrace (prefixWord ++ tailWord_1273586) baseStart_1273586 baseEnd_1273586 := by
    simpa [prefixWord, tailWord_1273586, baseEnd_1273586] using wordTrace_append hprefix tailTrace_1273586
  have hstable : (prefixWord ++ tailWord_1273586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273586).length < 2 ^ (prefixWord ++ tailWord_1273586).sum := by decide
  have hdescent : baseEnd_1273586 < baseStart_1273586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273715 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 4]
def baseStart_1273715 : Nat := 118140960795 + 1273715 * 2 ^ 59
def prefixEnd_1273715 : Nat := 4983230072969 + 3 ^ 40 * 1273715 * 2
def baseEnd_1273715 : Nat := 654028011841589317904797

theorem tailTrace_1273715 : CollatzResearch.WordTrace tailWord_1273715 prefixEnd_1273715 654028011841589317904797 := by
  unfold tailWord_1273715
  simp only [CollatzResearch.WordTrace]
  refine ⟨46456202580555563048406599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30970801720370375365604399 46456202580555563048406599)
  ·
    refine ⟨69684303870833344572609899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46456202580555563048406599 69684303870833344572609899)
    ·
      refine ⟨104526455806250016858914849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69684303870833344572609899 104526455806250016858914849)
      ·
        refine ⟨78394841854687512644186137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104526455806250016858914849 78394841854687512644186137)
        ·
          refine ⟨58796131391015634483139603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78394841854687512644186137 58796131391015634483139603)
          ·
            refine ⟨88194197086523451724709405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58796131391015634483139603 88194197086523451724709405)
            ·
              refine ⟨33072823907446294396766027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88194197086523451724709405 33072823907446294396766027)
              ·
                refine ⟨49609235861169441595149041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33072823907446294396766027 49609235861169441595149041)
                ·
                  refine ⟨37206926895877081196361781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49609235861169441595149041 37206926895877081196361781)
                  ·
                    refine ⟨3488149396488476362158917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37206926895877081196361781 3488149396488476362158917)
                    ·
                      refine ⟨654028011841589317904797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3488149396488476362158917 654028011841589317904797)
                      ·
                        rfl

theorem cell23_1273715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_1273715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273715 prefixEnd_1273715 := by exact prefixLift 1273715
  have htrace : WordTrace (prefixWord ++ tailWord_1273715) baseStart_1273715 baseEnd_1273715 := by
    simpa [prefixWord, tailWord_1273715, baseEnd_1273715] using wordTrace_append hprefix tailTrace_1273715
  have hstable : (prefixWord ++ tailWord_1273715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273715).length < 2 ^ (prefixWord ++ tailWord_1273715).sum := by decide
  have hdescent : baseEnd_1273715 < baseStart_1273715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273789 : List Nat := [1, 4, 1, 2, 3, 2, 3, 7]
def baseStart_1273789 : Nat := 118140960795 + 1273789 * 2 ^ 59
def prefixEnd_1273789 : Nat := 4983230072969 + 3 ^ 40 * 1273789 * 2
def baseEnd_1273789 : Nat := 24224667015186001051091

theorem tailTrace_1273789 : CollatzResearch.WordTrace tailWord_1273789 prefixEnd_1273789 24224667015186001051091 := by
  unfold tailWord_1273789
  simp only [CollatzResearch.WordTrace]
  refine ⟨46458901582287473686600421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30972601054858315791066947 46458901582287473686600421)
  ·
    refine ⟨8711044046678901316237579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46458901582287473686600421 8711044046678901316237579)
    ·
      refine ⟨13066566070018351974356369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8711044046678901316237579 13066566070018351974356369)
      ·
        refine ⟨9799924552513763980767277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13066566070018351974356369 9799924552513763980767277)
        ·
          refine ⟨3674971707192661492787729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9799924552513763980767277 3674971707192661492787729)
          ·
            refine ⟨2756228780394496119590797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3674971707192661492787729 2756228780394496119590797)
            ·
              refine ⟨1033585792647936044846549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2756228780394496119590797 1033585792647936044846549)
              ·
                refine ⟨24224667015186001051091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1033585792647936044846549 24224667015186001051091)
                ·
                  rfl

theorem cell23_1273789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 7].length) (baseStart_1273789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273789 prefixEnd_1273789 := by exact prefixLift 1273789
  have htrace : WordTrace (prefixWord ++ tailWord_1273789) baseStart_1273789 baseEnd_1273789 := by
    simpa [prefixWord, tailWord_1273789, baseEnd_1273789] using wordTrace_append hprefix tailTrace_1273789
  have hstable : (prefixWord ++ tailWord_1273789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273789).length < 2 ^ (prefixWord ++ tailWord_1273789).sum := by decide
  have hdescent : baseEnd_1273789 < baseStart_1273789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273799 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 4, 1, 3]
def baseStart_1273799 : Nat := 118140960795 + 1273799 * 2 ^ 59
def prefixEnd_1273799 : Nat := 4983230072969 + 3 ^ 40 * 1273799 * 2
def baseEnd_1273799 : Nat := 654071144216566989254411

theorem tailTrace_1273799 : CollatzResearch.WordTrace tailWord_1273799 prefixEnd_1273799 654071144216566989254411 := by
  unfold tailWord_1273799
  simp only [CollatzResearch.WordTrace]
  refine ⟨46459266312251245394464451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30972844208167496929642967 46459266312251245394464451)
  ·
    refine ⟨69688899468376868091696677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46459266312251245394464451 69688899468376868091696677)
    ·
      refine ⟨13066668650320662767193127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69688899468376868091696677 13066668650320662767193127)
      ·
        refine ⟨19600002975480994150789691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13066668650320662767193127 19600002975480994150789691)
        ·
          refine ⟨29400004463221491226184537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19600002975480994150789691 29400004463221491226184537)
          ·
            refine ⟨22050003347416118419638403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29400004463221491226184537 22050003347416118419638403)
            ·
              refine ⟨33075005021124177629457605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22050003347416118419638403 33075005021124177629457605)
              ·
                refine ⟨6201563441460783305523301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33075005021124177629457605 6201563441460783305523301)
                ·
                  refine ⟨1162793145273896869785619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6201563441460783305523301 1162793145273896869785619)
                  ·
                    refine ⟨1744189717910845304678429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1162793145273896869785619 1744189717910845304678429)
                    ·
                      refine ⟨654071144216566989254411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1744189717910845304678429 654071144216566989254411)
                      ·
                        rfl

theorem cell23_1273799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_1273799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273799 prefixEnd_1273799 := by exact prefixLift 1273799
  have htrace : WordTrace (prefixWord ++ tailWord_1273799) baseStart_1273799 baseEnd_1273799 := by
    simpa [prefixWord, tailWord_1273799, baseEnd_1273799] using wordTrace_append hprefix tailTrace_1273799
  have hstable : (prefixWord ++ tailWord_1273799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273799).length < 2 ^ (prefixWord ++ tailWord_1273799).sum := by decide
  have hdescent : baseEnd_1273799 < baseStart_1273799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273800 : List Nat := [2, 1, 3, 1, 4, 2, 2, 3, 1, 2, 2]
def baseStart_1273800 : Nat := 118140960795 + 1273800 * 2 ^ 59
def prefixEnd_1273800 : Nat := 4983230072969 + 3 ^ 40 * 1273800 * 2
def baseEnd_1273800 : Nat := 654071657697221485341907

theorem tailTrace_1273800 : CollatzResearch.WordTrace tailWord_1273800 prefixEnd_1273800 654071657697221485341907 := by
  unfold tailWord_1273800
  simp only [CollatzResearch.WordTrace]
  refine ⟨23229651392623811282625427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30972868523498415043500569 23229651392623811282625427)
  ·
    refine ⟨34844477088935716923938141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23229651392623811282625427 34844477088935716923938141)
    ·
      refine ⟨13066678908350893846476803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34844477088935716923938141 13066678908350893846476803)
      ·
        refine ⟨19600018362526340769715205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13066678908350893846476803 19600018362526340769715205)
        ·
          refine ⟨3675003442973688894321601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19600018362526340769715205 3675003442973688894321601)
          ·
            refine ⟨2756252582230266670741201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3675003442973688894321601 2756252582230266670741201)
            ·
              refine ⟨2067189436672700003055901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2756252582230266670741201 2067189436672700003055901)
              ·
                refine ⟨775196038752262501145963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2067189436672700003055901 775196038752262501145963)
                ·
                  refine ⟨1162794058128393751718945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 775196038752262501145963 1162794058128393751718945)
                  ·
                    refine ⟨872095543596295313789209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1162794058128393751718945 872095543596295313789209)
                    ·
                      refine ⟨654071657697221485341907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 872095543596295313789209 654071657697221485341907)
                      ·
                        rfl

theorem cell23_1273800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_1273800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273800 prefixEnd_1273800 := by exact prefixLift 1273800
  have htrace : WordTrace (prefixWord ++ tailWord_1273800) baseStart_1273800 baseEnd_1273800 := by
    simpa [prefixWord, tailWord_1273800, baseEnd_1273800] using wordTrace_append hprefix tailTrace_1273800
  have hstable : (prefixWord ++ tailWord_1273800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273800).length < 2 ^ (prefixWord ++ tailWord_1273800).sum := by decide
  have hdescent : baseEnd_1273800 < baseStart_1273800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273809 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 5, 3, 2]
def baseStart_1273809 : Nat := 118140960795 + 1273809 * 2 ^ 59
def prefixEnd_1273809 : Nat := 4983230072969 + 3 ^ 40 * 1273809 * 2
def baseEnd_1273809 : Nat := 654076279023111950129365

theorem tailTrace_1273809 : CollatzResearch.WordTrace tailWord_1273809 prefixEnd_1273809 654076279023111950129365 := by
  unfold tailWord_1273809
  simp only [CollatzResearch.WordTrace]
  refine ⟨46459631042215017102328481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30973087361476678068218987 46459631042215017102328481)
  ·
    refine ⟨34844723281661262826746361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46459631042215017102328481 34844723281661262826746361)
    ·
      refine ⟨26133542461245947120059771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34844723281661262826746361 26133542461245947120059771)
      ·
        refine ⟨39200313691868920680089657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26133542461245947120059771 39200313691868920680089657)
        ·
          refine ⟨29400235268901690510067243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39200313691868920680089657 29400235268901690510067243)
          ·
            refine ⟨44100352903352535765100865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29400235268901690510067243 44100352903352535765100865)
            ·
              refine ⟨33075264677514401823825649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44100352903352535765100865 33075264677514401823825649)
              ·
                refine ⟨24806448508135801367869237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33075264677514401823825649 24806448508135801367869237)
                ·
                  refine ⟨2325604547637731378237741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24806448508135801367869237 2325604547637731378237741)
                  ·
                    refine ⟨872101705364149266839153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2325604547637731378237741 872101705364149266839153)
                    ·
                      refine ⟨654076279023111950129365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 872101705364149266839153 654076279023111950129365)
                      ·
                        rfl

theorem cell23_1273809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 3, 2].length) (baseStart_1273809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273809 prefixEnd_1273809 := by exact prefixLift 1273809
  have htrace : WordTrace (prefixWord ++ tailWord_1273809) baseStart_1273809 baseEnd_1273809 := by
    simpa [prefixWord, tailWord_1273809, baseEnd_1273809] using wordTrace_append hprefix tailTrace_1273809
  have hstable : (prefixWord ++ tailWord_1273809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273809).length < 2 ^ (prefixWord ++ tailWord_1273809).sum := by decide
  have hdescent : baseEnd_1273809 < baseStart_1273809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273810 : List Nat := [3, 2, 2, 3, 3, 1, 1, 2, 2, 4]
def baseStart_1273810 : Nat := 118140960795 + 1273810 * 2 ^ 59
def prefixEnd_1273810 : Nat := 4983230072969 + 3 ^ 40 * 1273810 * 2
def baseEnd_1273810 : Nat := 218025597501255482072287

theorem tailTrace_1273810 : CollatzResearch.WordTrace tailWord_1273810 prefixEnd_1273810 218025597501255482072287 := by
  unfold tailWord_1273810
  simp only [CollatzResearch.WordTrace]
  refine ⟨11614916878802848568278721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30973111676807596182076589 11614916878802848568278721)
  ·
    refine ⟨8711187659102136426209041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11614916878802848568278721 8711187659102136426209041)
    ·
      refine ⟨6533390744326602319656781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8711187659102136426209041 6533390744326602319656781)
      ·
        refine ⟨2450021529122475869871293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6533390744326602319656781 2450021529122475869871293)
        ·
          refine ⟨918758073420928451201735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2450021529122475869871293 918758073420928451201735)
          ·
            refine ⟨1378137110131392676802603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918758073420928451201735 1378137110131392676802603)
            ·
              refine ⟨2067205665197089015203905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378137110131392676802603 2067205665197089015203905)
              ·
                refine ⟨1550404248897816761402929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067205665197089015203905 1550404248897816761402929)
                ·
                  refine ⟨1162803186673362571052197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1550404248897816761402929 1162803186673362571052197)
                  ·
                    refine ⟨218025597501255482072287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1162803186673362571052197 218025597501255482072287)
                    ·
                      rfl

theorem cell23_1273810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_1273810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273810 prefixEnd_1273810 := by exact prefixLift 1273810
  have htrace : WordTrace (prefixWord ++ tailWord_1273810) baseStart_1273810 baseEnd_1273810 := by
    simpa [prefixWord, tailWord_1273810, baseEnd_1273810] using wordTrace_append hprefix tailTrace_1273810
  have hstable : (prefixWord ++ tailWord_1273810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273810).length < 2 ^ (prefixWord ++ tailWord_1273810).sum := by decide
  have hdescent : baseEnd_1273810 < baseStart_1273810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273899 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 4, 5, 2]
def baseStart_1273899 : Nat := 118140960795 + 1273899 * 2 ^ 59
def prefixEnd_1273899 : Nat := 4983230072969 + 3 ^ 40 * 1273899 * 2
def baseEnd_1273899 : Nat := 654122492282016598003951

theorem tailTrace_1273899 : CollatzResearch.WordTrace tailWord_1273899 prefixEnd_1273899 654122492282016598003951 := by
  unfold tailWord_1273899
  simp only [CollatzResearch.WordTrace]
  refine ⟨46462913611888962473104751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30975275741259308315403167 46462913611888962473104751)
  ·
    refine ⟨69694370417833443709657127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46462913611888962473104751 69694370417833443709657127)
    ·
      refine ⟨104541555626750165564485691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69694370417833443709657127 104541555626750165564485691)
      ·
        refine ⟨156812333440125248346728537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104541555626750165564485691 156812333440125248346728537)
        ·
          refine ⟨117609250080093936260046403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156812333440125248346728537 117609250080093936260046403)
          ·
            refine ⟨176413875120140904390069605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117609250080093936260046403 176413875120140904390069605)
            ·
              refine ⟨33077601585026419573138051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176413875120140904390069605 33077601585026419573138051)
              ·
                refine ⟨49616402377539629359707077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33077601585026419573138051 49616402377539629359707077)
                ·
                  refine ⟨9303075445788680504945077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49616402377539629359707077 9303075445788680504945077)
                  ·
                    refine ⟨872163323042688797338601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9303075445788680504945077 872163323042688797338601)
                    ·
                      refine ⟨654122492282016598003951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 872163323042688797338601 654122492282016598003951)
                      ·
                        rfl

theorem cell23_1273899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 5, 2].length) (baseStart_1273899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273899 prefixEnd_1273899 := by exact prefixLift 1273899
  have htrace : WordTrace (prefixWord ++ tailWord_1273899) baseStart_1273899 baseEnd_1273899 := by
    simpa [prefixWord, tailWord_1273899, baseEnd_1273899] using wordTrace_append hprefix tailTrace_1273899
  have hstable : (prefixWord ++ tailWord_1273899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273899).length < 2 ^ (prefixWord ++ tailWord_1273899).sum := by decide
  have hdescent : baseEnd_1273899 < baseStart_1273899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273909 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 2, 5]
def baseStart_1273909 : Nat := 118140960795 + 1273909 * 2 ^ 59
def prefixEnd_1273909 : Nat := 4983230072969 + 3 ^ 40 * 1273909 * 2
def baseEnd_1273909 : Nat := 218042542362853852959635

theorem tailTrace_1273909 : CollatzResearch.WordTrace tailWord_1273909 prefixEnd_1273909 218042542362853852959635 := by
  unfold tailWord_1273909
  simp only [CollatzResearch.WordTrace]
  refine ⟨46463278341852734180968781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30975518894568489453979187 46463278341852734180968781)
  ·
    refine ⟨17423729378194775317863293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46463278341852734180968781 17423729378194775317863293)
    ·
      refine ⟨6533898516823040744198735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17423729378194775317863293 6533898516823040744198735)
      ·
        refine ⟨9800847775234561116298103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6533898516823040744198735 9800847775234561116298103)
        ·
          refine ⟨14701271662851841674447155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9800847775234561116298103 14701271662851841674447155)
          ·
            refine ⟨22051907494277762511670733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14701271662851841674447155 22051907494277762511670733)
            ·
              refine ⟨8269465310354160941876525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22051907494277762511670733 8269465310354160941876525)
              ·
                refine ⟨3101049491382810353203697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8269465310354160941876525 3101049491382810353203697)
                ·
                  refine ⟨2325787118537107764902773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3101049491382810353203697 2325787118537107764902773)
                  ·
                    refine ⟨218042542362853852959635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2325787118537107764902773 218042542362853852959635)
                    ·
                      rfl

theorem cell23_1273909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_1273909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273909 prefixEnd_1273909 := by exact prefixLift 1273909
  have htrace : WordTrace (prefixWord ++ tailWord_1273909) baseStart_1273909 baseEnd_1273909 := by
    simpa [prefixWord, tailWord_1273909, baseEnd_1273909] using wordTrace_append hprefix tailTrace_1273909
  have hstable : (prefixWord ++ tailWord_1273909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273909).length < 2 ^ (prefixWord ++ tailWord_1273909).sum := by decide
  have hdescent : baseEnd_1273909 < baseStart_1273909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273929 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 2, 1, 4]
def baseStart_1273929 : Nat := 118140960795 + 1273929 * 2 ^ 59
def prefixEnd_1273929 : Nat := 4983230072969 + 3 ^ 40 * 1273929 * 2
def baseEnd_1273929 : Nat := 654137896701651480628813

theorem tailTrace_1273929 : CollatzResearch.WordTrace tailWord_1273929 prefixEnd_1273929 654137896701651480628813 := by
  unfold tailWord_1273929
  simp only [CollatzResearch.WordTrace]
  refine ⟨46464007801780277596696841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30976005201186851731131227 46464007801780277596696841)
  ·
    refine ⟨34848005851335208197522631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46464007801780277596696841 34848005851335208197522631)
    ·
      refine ⟨52272008777002812296283947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34848005851335208197522631 52272008777002812296283947)
      ·
        refine ⟨78408013165504218444425921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52272008777002812296283947 78408013165504218444425921)
        ·
          refine ⟨58806009874128163833319441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78408013165504218444425921 58806009874128163833319441)
          ·
            refine ⟨44104507405596122874989581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58806009874128163833319441 44104507405596122874989581)
            ·
              refine ⟨16539190277098546078121093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44104507405596122874989581 16539190277098546078121093)
              ·
                refine ⟨3101098176955977389647705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16539190277098546078121093 3101098176955977389647705)
                ·
                  refine ⟨2325823632716983042235779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3101098176955977389647705 2325823632716983042235779)
                  ·
                    refine ⟨3488735449075474563353669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2325823632716983042235779 3488735449075474563353669)
                    ·
                      refine ⟨654137896701651480628813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3488735449075474563353669 654137896701651480628813)
                      ·
                        rfl

theorem cell23_1273929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_1273929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273929 prefixEnd_1273929 := by exact prefixLift 1273929
  have htrace : WordTrace (prefixWord ++ tailWord_1273929) baseStart_1273929 baseEnd_1273929 := by
    simpa [prefixWord, tailWord_1273929, baseEnd_1273929] using wordTrace_append hprefix tailTrace_1273929
  have hstable : (prefixWord ++ tailWord_1273929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273929).length < 2 ^ (prefixWord ++ tailWord_1273929).sum := by decide
  have hdescent : baseEnd_1273929 < baseStart_1273929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273946 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2]
def baseStart_1273946 : Nat := 118140960795 + 1273946 * 2 ^ 59
def prefixEnd_1273946 : Nat := 4983230072969 + 3 ^ 40 * 1273946 * 2
def baseEnd_1273946 : Nat := 654146625872777914116235

theorem tailTrace_1273946 : CollatzResearch.WordTrace tailWord_1273946 prefixEnd_1273946 654146625872777914116235 := by
  unfold tailWord_1273946
  simp only [CollatzResearch.WordTrace]
  refine ⟨11616156960679672375016423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30976418561812459666710461 11616156960679672375016423)
  ·
    refine ⟨17424235441019508562524635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11616156960679672375016423 17424235441019508562524635)
    ·
      refine ⟨26136353161529262843786953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17424235441019508562524635 26136353161529262843786953)
      ·
        refine ⟨19602264871146947132840215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26136353161529262843786953 19602264871146947132840215)
        ·
          refine ⟨29403397306720420699260323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19602264871146947132840215 29403397306720420699260323)
          ·
            refine ⟨44105095960080631048890485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29403397306720420699260323 44105095960080631048890485)
            ·
              refine ⟨4134852746257559160833483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44105095960080631048890485 4134852746257559160833483)
              ·
                refine ⟨6202279119386338741250225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4134852746257559160833483 6202279119386338741250225)
                ·
                  refine ⟨4651709339539754055937669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6202279119386338741250225 4651709339539754055937669)
                  ·
                    refine ⟨872195501163703885488313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4651709339539754055937669 872195501163703885488313)
                    ·
                      refine ⟨654146625872777914116235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 872195501163703885488313 654146625872777914116235)
                      ·
                        rfl

theorem cell23_1273946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_1273946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273946 prefixEnd_1273946 := by exact prefixLift 1273946
  have htrace : WordTrace (prefixWord ++ tailWord_1273946) baseStart_1273946 baseEnd_1273946 := by
    simpa [prefixWord, tailWord_1273946, baseEnd_1273946] using wordTrace_append hprefix tailTrace_1273946
  have hstable : (prefixWord ++ tailWord_1273946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273946).length < 2 ^ (prefixWord ++ tailWord_1273946).sum := by decide
  have hdescent : baseEnd_1273946 < baseStart_1273946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273966 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_1273966 : Nat := 118140960795 + 1273966 * 2 ^ 59
def prefixEnd_1273966 : Nat := 4983230072969 + 3 ^ 40 * 1273966 * 2
def baseEnd_1273966 : Nat := 654156895485867835866143

theorem tailTrace_1273966 : CollatzResearch.WordTrace tailWord_1273966 prefixEnd_1273966 654156895485867835866143 := by
  unfold tailWord_1273966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808169662830779114474219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30976904868430821943862501 5808169662830779114474219)
  ·
    refine ⟨8712254494246168671711329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5808169662830779114474219 8712254494246168671711329)
    ·
      refine ⟨6534190870684626503783497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8712254494246168671711329 6534190870684626503783497)
      ·
        refine ⟨4900643153013469877837623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6534190870684626503783497 4900643153013469877837623)
        ·
          refine ⟨7350964729520204816756435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4900643153013469877837623 7350964729520204816756435)
          ·
            refine ⟨11026447094280307225134653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7350964729520204816756435 11026447094280307225134653)
            ·
              refine ⟨4134917660355115209425495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11026447094280307225134653 4134917660355115209425495)
              ·
                refine ⟨6202376490532672814138243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4134917660355115209425495 6202376490532672814138243)
                ·
                  refine ⟨9303564735799009221207365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6202376490532672814138243 9303564735799009221207365)
                  ·
                    refine ⟨1744418387962314228976381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9303564735799009221207365 1744418387962314228976381)
                    ·
                      refine ⟨654156895485867835866143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1744418387962314228976381 654156895485867835866143)
                      ·
                        rfl

theorem cell23_1273966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_1273966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273966 prefixEnd_1273966 := by exact prefixLift 1273966
  have htrace : WordTrace (prefixWord ++ tailWord_1273966) baseStart_1273966 baseEnd_1273966 := by
    simpa [prefixWord, tailWord_1273966, baseEnd_1273966] using wordTrace_append hprefix tailTrace_1273966
  have hstable : (prefixWord ++ tailWord_1273966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273966).length < 2 ^ (prefixWord ++ tailWord_1273966).sum := by decide
  have hdescent : baseEnd_1273966 < baseStart_1273966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273989 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_1273989 : Nat := 118140960795 + 1273989 * 2 ^ 59
def prefixEnd_1273989 : Nat := 4983230072969 + 3 ^ 40 * 1273989 * 2
def baseEnd_1273989 : Nat := 654168705540921245878537

theorem tailTrace_1273989 : CollatzResearch.WordTrace tailWord_1273989 prefixEnd_1273989 654168705540921245878537 := by
  unfold tailWord_1273989
  simp only [CollatzResearch.WordTrace]
  refine ⟨46466196181562907843881021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30977464121041938562587347 46466196181562907843881021)
  ·
    refine ⟨17424823568086090441455383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46466196181562907843881021 17424823568086090441455383)
    ·
      refine ⟨26137235352129135662183075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17424823568086090441455383 26137235352129135662183075)
      ·
        refine ⟨39205853028193703493274613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26137235352129135662183075 39205853028193703493274613)
        ·
          refine ⟨3675548721393159702494495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39205853028193703493274613 3675548721393159702494495)
          ·
            refine ⟨5513323082089739553741743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3675548721393159702494495 5513323082089739553741743)
            ·
              refine ⟨8269984623134609330612615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5513323082089739553741743 8269984623134609330612615)
              ·
                refine ⟨12404976934701913995918923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8269984623134609330612615 12404976934701913995918923)
                ·
                  refine ⟨18607465402052870993878385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12404976934701913995918923 18607465402052870993878385)
                  ·
                    refine ⟨13955599051539653245408789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18607465402052870993878385 13955599051539653245408789)
                    ·
                      refine ⟨654168705540921245878537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13955599051539653245408789 654168705540921245878537)
                      ·
                        rfl

theorem cell23_1273989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_1273989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1273989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1273989 prefixEnd_1273989 := by exact prefixLift 1273989
  have htrace : WordTrace (prefixWord ++ tailWord_1273989) baseStart_1273989 baseEnd_1273989 := by
    simpa [prefixWord, tailWord_1273989, baseEnd_1273989] using wordTrace_append hprefix tailTrace_1273989
  have hstable : (prefixWord ++ tailWord_1273989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273989).length < 2 ^ (prefixWord ++ tailWord_1273989).sum := by decide
  have hdescent : baseEnd_1273989 < baseStart_1273989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274013 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_1274013 : Nat := 118140960795 + 1274013 * 2 ^ 59
def prefixEnd_1274013 : Nat := 4983230072969 + 3 ^ 40 * 1274013 * 2
def baseEnd_1274013 : Nat := 654181029076629151978427

theorem tailTrace_1274013 : CollatzResearch.WordTrace tailWord_1274013 prefixEnd_1274013 654181029076629151978427 := by
  unfold tailWord_1274013
  simp only [CollatzResearch.WordTrace]
  refine ⟨46467071533475959942754693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30978047688983973295169795 46467071533475959942754693)
  ·
    refine ⟨8712575912526742489266505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46467071533475959942754693 8712575912526742489266505)
    ·
      refine ⟨6534431934395056866949879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8712575912526742489266505 6534431934395056866949879)
      ·
        refine ⟨9801647901592585300424819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6534431934395056866949879 9801647901592585300424819)
        ·
          refine ⟨14702471852388877950637229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9801647901592585300424819 14702471852388877950637229)
          ·
            refine ⟨5513426944645829231488961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14702471852388877950637229 5513426944645829231488961)
            ·
              refine ⟨4135070208484371923616721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5513426944645829231488961 4135070208484371923616721)
              ·
                refine ⟨3101302656363278942712541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4135070208484371923616721 3101302656363278942712541)
                ·
                  refine ⟨1162988496136229603517203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3101302656363278942712541 1162988496136229603517203)
                  ·
                    refine ⟨1744482744204344405275805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1162988496136229603517203 1744482744204344405275805)
                    ·
                      refine ⟨654181029076629151978427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1744482744204344405275805 654181029076629151978427)
                      ·
                        rfl

theorem cell23_1274013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_1274013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274013 prefixEnd_1274013 := by exact prefixLift 1274013
  have htrace : WordTrace (prefixWord ++ tailWord_1274013) baseStart_1274013 baseEnd_1274013 := by
    simpa [prefixWord, tailWord_1274013, baseEnd_1274013] using wordTrace_append hprefix tailTrace_1274013
  have hstable : (prefixWord ++ tailWord_1274013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274013).length < 2 ^ (prefixWord ++ tailWord_1274013).sum := by decide
  have hdescent : baseEnd_1274013 < baseStart_1274013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274016 : List Nat := [2, 1, 1, 4, 2, 2, 1, 4, 1, 5]
def baseStart_1274016 : Nat := 118140960795 + 1274016 * 2 ^ 59
def prefixEnd_1274016 : Nat := 4983230072969 + 3 ^ 40 * 1274016 * 2
def baseEnd_1274016 : Nat := 218060856506197546746971

theorem tailTrace_1274016 : CollatzResearch.WordTrace tailWord_1274016 prefixEnd_1274016 218060856506197546746971 := by
  unfold tailWord_1274016
  simp only [CollatzResearch.WordTrace]
  refine ⟨23233590476232545727556951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30978120634976727636742601 23233590476232545727556951)
  ·
    refine ⟨34850385714348818591335427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23233590476232545727556951 34850385714348818591335427)
    ·
      refine ⟨52275578571523227887003141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34850385714348818591335427 52275578571523227887003141)
      ·
        refine ⟨9801670982160605228813089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52275578571523227887003141 9801670982160605228813089)
        ·
          refine ⟨7351253236620453921609817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9801670982160605228813089 7351253236620453921609817)
          ·
            refine ⟨5513439927465340441207363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7351253236620453921609817 5513439927465340441207363)
            ·
              refine ⟨8270159891198010661811045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5513439927465340441207363 8270159891198010661811045)
              ·
                refine ⟨1550654979599626999089571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8270159891198010661811045 1550654979599626999089571)
                ·
                  refine ⟨2325982469399440498634357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550654979599626999089571 2325982469399440498634357)
                  ·
                    refine ⟨218060856506197546746971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2325982469399440498634357 218060856506197546746971)
                    ·
                      rfl

theorem cell23_1274016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 1, 5].length) (baseStart_1274016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274016 prefixEnd_1274016 := by exact prefixLift 1274016
  have htrace : WordTrace (prefixWord ++ tailWord_1274016) baseStart_1274016 baseEnd_1274016 := by
    simpa [prefixWord, tailWord_1274016, baseEnd_1274016] using wordTrace_append hprefix tailTrace_1274016
  have hstable : (prefixWord ++ tailWord_1274016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274016).length < 2 ^ (prefixWord ++ tailWord_1274016).sum := by decide
  have hdescent : baseEnd_1274016 < baseStart_1274016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274056 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_1274056 : Nat := 118140960795 + 1274056 * 2 ^ 59
def prefixEnd_1274056 : Nat := 4983230072969 + 3 ^ 40 * 1274056 * 2
def baseEnd_1274056 : Nat := 654203108744772483740729

theorem tailTrace_1274056 : CollatzResearch.WordTrace tailWord_1274056 prefixEnd_1274056 654203108744772483740729 := by
  unfold tailWord_1274056
  simp only [CollatzResearch.WordTrace]
  refine ⟨23234319936160089143285011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30979093248213452191046681 23234319936160089143285011)
  ·
    refine ⟨34851479904240133714927517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23234319936160089143285011 34851479904240133714927517)
    ·
      refine ⟨13069304964090050143097819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34851479904240133714927517 13069304964090050143097819)
      ·
        refine ⟨19603957446135075214646729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13069304964090050143097819 19603957446135075214646729)
        ·
          refine ⟨14702968084601306410985047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19603957446135075214646729 14702968084601306410985047)
          ·
            refine ⟨22054452126901959616477571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14702968084601306410985047 22054452126901959616477571)
            ·
              refine ⟨33081678190352939424716357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22054452126901959616477571 33081678190352939424716357)
              ·
                refine ⟨6202814660691176142134317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33081678190352939424716357 6202814660691176142134317)
                ·
                  refine ⟨2326055497759191053300369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6202814660691176142134317 2326055497759191053300369)
                  ·
                    refine ⟨1744541623319393289975277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2326055497759191053300369 1744541623319393289975277)
                    ·
                      refine ⟨654203108744772483740729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1744541623319393289975277 654203108744772483740729)
                      ·
                        rfl

theorem cell23_1274056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_1274056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274056 prefixEnd_1274056 := by exact prefixLift 1274056
  have htrace : WordTrace (prefixWord ++ tailWord_1274056) baseStart_1274056 baseEnd_1274056 := by
    simpa [prefixWord, tailWord_1274056, baseEnd_1274056] using wordTrace_append hprefix tailTrace_1274056
  have hstable : (prefixWord ++ tailWord_1274056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274056).length < 2 ^ (prefixWord ++ tailWord_1274056).sum := by decide
  have hdescent : baseEnd_1274056 < baseStart_1274056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274059 : List Nat := [1, 1, 1, 1, 3, 2, 6, 8]
def baseStart_1274059 : Nat := 118140960795 + 1274059 * 2 ^ 59
def prefixEnd_1274059 : Nat := 4983230072969 + 3 ^ 40 * 1274059 * 2
def baseEnd_1274059 : Nat := 24229801821730961926045

theorem tailTrace_1274059 : CollatzResearch.WordTrace tailWord_1274059 prefixEnd_1274059 24229801821730961926045 := by
  unfold tailWord_1274059
  simp only [CollatzResearch.WordTrace]
  refine ⟨46468749291309309798929231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30979166194206206532619487 46468749291309309798929231)
  ·
    refine ⟨69703123936963964698393847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46468749291309309798929231 69703123936963964698393847)
    ·
      refine ⟨104554685905445947047590771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69703123936963964698393847 104554685905445947047590771)
      ·
        refine ⟨156832028858168920571386157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104554685905445947047590771 156832028858168920571386157)
        ·
          refine ⟨58812010821813345214269809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156832028858168920571386157 58812010821813345214269809)
          ·
            refine ⟨44109008116360008910702357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58812010821813345214269809 44109008116360008910702357)
            ·
              refine ⟨2067609755454375417689173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44109008116360008910702357 2067609755454375417689173)
              ·
                refine ⟨24229801821730961926045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2067609755454375417689173 24229801821730961926045)
                ·
                  rfl

theorem cell23_1274059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 8].length) (baseStart_1274059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274059 prefixEnd_1274059 := by exact prefixLift 1274059
  have htrace : WordTrace (prefixWord ++ tailWord_1274059) baseStart_1274059 baseEnd_1274059 := by
    simpa [prefixWord, tailWord_1274059, baseEnd_1274059] using wordTrace_append hprefix tailTrace_1274059
  have hstable : (prefixWord ++ tailWord_1274059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274059).length < 2 ^ (prefixWord ++ tailWord_1274059).sum := by decide
  have hdescent : baseEnd_1274059 < baseStart_1274059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274066 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1274066 : Nat := 118140960795 + 1274066 * 2 ^ 59
def prefixEnd_1274066 : Nat := 4983230072969 + 3 ^ 40 * 1274066 * 2
def baseEnd_1274066 : Nat := 654208243551317444615683

theorem tailTrace_1274066 : CollatzResearch.WordTrace tailWord_1274066 prefixEnd_1274066 654208243551317444615683 := by
  unfold tailWord_1274066
  simp only [CollatzResearch.WordTrace]
  refine ⟨11617251150570987498608513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30979336401522633329622701 11617251150570987498608513)
  ·
    refine ⟨8712938362928240623956385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11617251150570987498608513 8712938362928240623956385)
    ·
      refine ⟨6534703772196180467967289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8712938362928240623956385 6534703772196180467967289)
      ·
        refine ⟨4901027829147135350975467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6534703772196180467967289 4901027829147135350975467)
        ·
          refine ⟨7351541743720703026463201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4901027829147135350975467 7351541743720703026463201)
          ·
            refine ⟨5513656307790527269847401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7351541743720703026463201 5513656307790527269847401)
            ·
              refine ⟨4135242230842895452385551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5513656307790527269847401 4135242230842895452385551)
              ·
                refine ⟨6202863346264343178578327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4135242230842895452385551 6202863346264343178578327)
                ·
                  refine ⟨9304295019396514767867491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6202863346264343178578327 9304295019396514767867491)
                  ·
                    refine ⟨13956442529094772151801237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9304295019396514767867491 13956442529094772151801237)
                    ·
                      refine ⟨654208243551317444615683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13956442529094772151801237 654208243551317444615683)
                      ·
                        rfl

theorem cell23_1274066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1274066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274066 prefixEnd_1274066 := by exact prefixLift 1274066
  have htrace : WordTrace (prefixWord ++ tailWord_1274066) baseStart_1274066 baseEnd_1274066 := by
    simpa [prefixWord, tailWord_1274066, baseEnd_1274066] using wordTrace_append hprefix tailTrace_1274066
  have hstable : (prefixWord ++ tailWord_1274066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274066).length < 2 ^ (prefixWord ++ tailWord_1274066).sum := by decide
  have hdescent : baseEnd_1274066 < baseStart_1274066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274070 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_1274070 : Nat := 118140960795 + 1274070 * 2 ^ 59
def prefixEnd_1274070 : Nat := 4983230072969 + 3 ^ 40 * 1274070 * 2
def baseEnd_1274070 : Nat := 654210297473935428965665

theorem tailTrace_1274070 : CollatzResearch.WordTrace tailWord_1274070 prefixEnd_1274070 654210297473935428965665 := by
  unfold tailWord_1274070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2904321905891841167348729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30979433662846305785053109 2904321905891841167348729)
  ·
    refine ⟨2178241429418880875511547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2904321905891841167348729 2178241429418880875511547)
    ·
      refine ⟨3267362144128321313267321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2178241429418880875511547 3267362144128321313267321)
      ·
        refine ⟨2450521608096240984950491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3267362144128321313267321 2450521608096240984950491)
        ·
          refine ⟨3675782412144361477425737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2450521608096240984950491 3675782412144361477425737)
          ·
            refine ⟨2756836809108271108069303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3675782412144361477425737 2756836809108271108069303)
            ·
              refine ⟨4135255213662406662103955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756836809108271108069303 4135255213662406662103955)
              ·
                refine ⟨6202882820493609993155933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4135255213662406662103955 6202882820493609993155933)
                ·
                  refine ⟨2326081057685103747433475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6202882820493609993155933 2326081057685103747433475)
                  ·
                    refine ⟨3489121586527655621150213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2326081057685103747433475 3489121586527655621150213)
                    ·
                      refine ⟨654210297473935428965665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3489121586527655621150213 654210297473935428965665)
                      ·
                        rfl

theorem cell23_1274070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_1274070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274070 prefixEnd_1274070 := by exact prefixLift 1274070
  have htrace : WordTrace (prefixWord ++ tailWord_1274070) baseStart_1274070 baseEnd_1274070 := by
    simpa [prefixWord, tailWord_1274070, baseEnd_1274070] using wordTrace_append hprefix tailTrace_1274070
  have hstable : (prefixWord ++ tailWord_1274070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274070).length < 2 ^ (prefixWord ++ tailWord_1274070).sum := by decide
  have hdescent : baseEnd_1274070 < baseStart_1274070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274073 : List Nat := [1, 2, 1, 2, 3, 1, 5, 2, 1, 2, 3]
def baseStart_1274073 : Nat := 118140960795 + 1274073 * 2 ^ 59
def prefixEnd_1274073 : Nat := 4983230072969 + 3 ^ 40 * 1274073 * 2
def baseEnd_1274073 : Nat := 654211837915898917228151

theorem tailTrace_1274073 : CollatzResearch.WordTrace tailWord_1274073 prefixEnd_1274073 654211837915898917228151 := by
  unfold tailWord_1274073
  simp only [CollatzResearch.WordTrace]
  refine ⟨46469259913258590189938873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30979506608839060126625915 46469259913258590189938873)
  ·
    refine ⟨34851944934943942642454155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46469259913258590189938873 34851944934943942642454155)
    ·
      refine ⟨52277917402415913963681233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34851944934943942642454155 52277917402415913963681233)
      ·
        refine ⟨39208438051811935472760925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52277917402415913963681233 39208438051811935472760925)
        ·
          refine ⟨14703164269429475802285347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39208438051811935472760925 14703164269429475802285347)
          ·
            refine ⟨22054746404144213703428021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14703164269429475802285347 22054746404144213703428021)
            ·
              refine ⟨2067632475388520034696377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22054746404144213703428021 2067632475388520034696377)
              ·
                refine ⟨1550724356541390026022283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067632475388520034696377 1550724356541390026022283)
                ·
                  refine ⟨2326086534812085039033425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550724356541390026022283 2326086534812085039033425)
                  ·
                    refine ⟨1744564901109063779275069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2326086534812085039033425 1744564901109063779275069)
                    ·
                      refine ⟨654211837915898917228151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1744564901109063779275069 654211837915898917228151)
                      ·
                        rfl

theorem cell23_1274073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_1274073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274073 prefixEnd_1274073 := by exact prefixLift 1274073
  have htrace : WordTrace (prefixWord ++ tailWord_1274073) baseStart_1274073 baseEnd_1274073 := by
    simpa [prefixWord, tailWord_1274073, baseEnd_1274073] using wordTrace_append hprefix tailTrace_1274073
  have hstable : (prefixWord ++ tailWord_1274073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274073).length < 2 ^ (prefixWord ++ tailWord_1274073).sum := by decide
  have hdescent : baseEnd_1274073 < baseStart_1274073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274090 : List Nat := [3, 1, 3, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_1274090 : Nat := 118140960795 + 1274090 * 2 ^ 59
def prefixEnd_1274090 : Nat := 4983230072969 + 3 ^ 40 * 1274090 * 2
def baseEnd_1274090 : Nat := 654220567087025350715573

theorem tailTrace_1274090 : CollatzResearch.WordTrace tailWord_1274090 prefixEnd_1274090 654220567087025350715573 := by
  unfold tailWord_1274090
  simp only [CollatzResearch.WordTrace]
  refine ⟨11617469988549250523326931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30979919969464668062205149 11617469988549250523326931)
  ·
    refine ⟨17426204982823875784990397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11617469988549250523326931 17426204982823875784990397)
    ·
      refine ⟨6534826868558953419371399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17426204982823875784990397 6534826868558953419371399)
      ·
        refine ⟨9802240302838430129057099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6534826868558953419371399 9802240302838430129057099)
        ·
          refine ⟨14703360454257645193585649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9802240302838430129057099 14703360454257645193585649)
          ·
            refine ⟨11027520340693233895189237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14703360454257645193585649 11027520340693233895189237)
            ·
              refine ⟨1033830031939990677673991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11027520340693233895189237 1033830031939990677673991)
              ·
                refine ⟨1550745047909986016510987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1033830031939990677673991 1550745047909986016510987)
                ·
                  refine ⟨2326117571864979024766481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550745047909986016510987 2326117571864979024766481)
                  ·
                    refine ⟨1744588178898734268574861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2326117571864979024766481 1744588178898734268574861)
                    ·
                      refine ⟨654220567087025350715573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1744588178898734268574861 654220567087025350715573)
                      ·
                        rfl

theorem cell23_1274090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_1274090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274090 prefixEnd_1274090 := by exact prefixLift 1274090
  have htrace : WordTrace (prefixWord ++ tailWord_1274090) baseStart_1274090 baseEnd_1274090 := by
    simpa [prefixWord, tailWord_1274090, baseEnd_1274090] using wordTrace_append hprefix tailTrace_1274090
  have hstable : (prefixWord ++ tailWord_1274090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274090).length < 2 ^ (prefixWord ++ tailWord_1274090).sum := by decide
  have hdescent : baseEnd_1274090 < baseStart_1274090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274113 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_1274113 : Nat := 118140960795 + 1274113 * 2 ^ 59
def prefixEnd_1274113 : Nat := 4983230072969 + 3 ^ 40 * 1274113 * 2
def baseEnd_1274113 : Nat := 654232377142078760727967

theorem tailTrace_1274113 : CollatzResearch.WordTrace tailWord_1274113 prefixEnd_1274113 654232377142078760727967 := by
  unfold tailWord_1274113
  simp only [CollatzResearch.WordTrace]
  refine ⟨46470718833113677021394993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30980479222075784680929995 46470718833113677021394993)
  ·
    refine ⟨34853039124835257766046245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46470718833113677021394993 34853039124835257766046245)
    ·
      refine ⟨6534944835906610831133671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34853039124835257766046245 6534944835906610831133671)
      ·
        refine ⟨9802417253859916246700507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6534944835906610831133671 9802417253859916246700507)
        ·
          refine ⟨14703625880789874370050761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9802417253859916246700507 14703625880789874370050761)
          ·
            refine ⟨11027719410592405777538071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14703625880789874370050761 11027719410592405777538071)
            ·
              refine ⟨16541579115888608666307107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11027719410592405777538071 16541579115888608666307107)
              ·
                refine ⟨24812368673832912999460661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16541579115888608666307107 24812368673832912999460661)
                ·
                  refine ⟨2326159563171835593699437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24812368673832912999460661 2326159563171835593699437)
                  ·
                    refine ⟨872309836189438347637289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2326159563171835593699437 872309836189438347637289)
                    ·
                      refine ⟨654232377142078760727967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 872309836189438347637289 654232377142078760727967)
                      ·
                        rfl

theorem cell23_1274113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_1274113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274113 prefixEnd_1274113 := by exact prefixLift 1274113
  have htrace : WordTrace (prefixWord ++ tailWord_1274113) baseStart_1274113 baseEnd_1274113 := by
    simpa [prefixWord, tailWord_1274113, baseEnd_1274113] using wordTrace_append hprefix tailTrace_1274113
  have hstable : (prefixWord ++ tailWord_1274113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274113).length < 2 ^ (prefixWord ++ tailWord_1274113).sum := by decide
  have hdescent : baseEnd_1274113 < baseStart_1274113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274120 : List Nat := [2, 1, 3, 2, 3, 1, 2, 3, 2, 1, 3]
def baseStart_1274120 : Nat := 118140960795 + 1274120 * 2 ^ 59
def prefixEnd_1274120 : Nat := 4983230072969 + 3 ^ 40 * 1274120 * 2
def baseEnd_1274120 : Nat := 654235971506660233340435

theorem tailTrace_1274120 : CollatzResearch.WordTrace tailWord_1274120 prefixEnd_1274120 654235971506660233340435 := by
  unfold tailWord_1274120
  simp only [CollatzResearch.WordTrace]
  refine ⟨23235487072044158608449907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30980649429392211477933209 23235487072044158608449907)
  ·
    refine ⟨34853230608066237912674861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23235487072044158608449907 34853230608066237912674861)
    ·
      refine ⟨13069961478024839217253073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34853230608066237912674861 13069961478024839217253073)
      ·
        refine ⟨9802471108518629412939805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13069961478024839217253073 9802471108518629412939805)
        ·
          refine ⟨3675926665694486029852427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9802471108518629412939805 3675926665694486029852427)
          ·
            refine ⟨5513889998541729044778641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3675926665694486029852427 5513889998541729044778641)
            ·
              refine ⟨4135417498906296783583981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5513889998541729044778641 4135417498906296783583981)
              ·
                refine ⟨1550781562089861293843993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4135417498906296783583981 1550781562089861293843993)
                ·
                  refine ⟨1163086171567395970382995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1550781562089861293843993 1163086171567395970382995)
                  ·
                    refine ⟨1744629257351093955574493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1163086171567395970382995 1744629257351093955574493)
                    ·
                      refine ⟨654235971506660233340435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1744629257351093955574493 654235971506660233340435)
                      ·
                        rfl

theorem cell23_1274120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_1274120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274120 prefixEnd_1274120 := by exact prefixLift 1274120
  have htrace : WordTrace (prefixWord ++ tailWord_1274120) baseStart_1274120 baseEnd_1274120 := by
    simpa [prefixWord, tailWord_1274120, baseEnd_1274120] using wordTrace_append hprefix tailTrace_1274120
  have hstable : (prefixWord ++ tailWord_1274120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274120).length < 2 ^ (prefixWord ++ tailWord_1274120).sum := by decide
  have hdescent : baseEnd_1274120 < baseStart_1274120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274126 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1274126 : Nat := 118140960795 + 1274126 * 2 ^ 59
def prefixEnd_1274126 : Nat := 4983230072969 + 3 ^ 40 * 1274126 * 2
def baseEnd_1274126 : Nat := 654239052390587209865407

theorem tailTrace_1274126 : CollatzResearch.WordTrace tailWord_1274126 prefixEnd_1274126 654239052390587209865407 := by
  unfold tailWord_1274126
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808899122758322530202279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30980795321377720161078821 5808899122758322530202279)
  ·
    refine ⟨8713348684137483795303419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5808899122758322530202279 8713348684137483795303419)
    ·
      refine ⟨13070023026206225692955129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8713348684137483795303419 13070023026206225692955129)
      ·
        refine ⟨9802517269654669269716347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13070023026206225692955129 9802517269654669269716347)
        ·
          refine ⟨14703775904482003904574521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9802517269654669269716347 14703775904482003904574521)
          ·
            refine ⟨11027831928361502928430891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14703775904482003904574521 11027831928361502928430891)
            ·
              refine ⟨16541747892542254392646337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11027831928361502928430891 16541747892542254392646337)
              ·
                refine ⟨12406310919406690794484753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16541747892542254392646337 12406310919406690794484753)
                ·
                  refine ⟨9304733189555018095863565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12406310919406690794484753 9304733189555018095863565)
                  ·
                    refine ⟨3489274946083131785948837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9304733189555018095863565 3489274946083131785948837)
                    ·
                      refine ⟨654239052390587209865407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3489274946083131785948837 654239052390587209865407)
                      ·
                        rfl

theorem cell23_1274126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1274126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274126 prefixEnd_1274126 := by exact prefixLift 1274126
  have htrace : WordTrace (prefixWord ++ tailWord_1274126) baseStart_1274126 baseEnd_1274126 := by
    simpa [prefixWord, tailWord_1274126, baseEnd_1274126] using wordTrace_append hprefix tailTrace_1274126
  have hstable : (prefixWord ++ tailWord_1274126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274126).length < 2 ^ (prefixWord ++ tailWord_1274126).sum := by decide
  have hdescent : baseEnd_1274126 < baseStart_1274126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274154 : List Nat := [3, 1, 4, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1274154 : Nat := 118140960795 + 1274154 * 2 ^ 59
def prefixEnd_1274154 : Nat := 4983230072969 + 3 ^ 40 * 1274154 * 2
def baseEnd_1274154 : Nat := 654253429848913100315279

theorem tailTrace_1274154 : CollatzResearch.WordTrace tailWord_1274154 prefixEnd_1274154 654253429848913100315279 := by
  unfold tailWord_1274154
  simp only [CollatzResearch.WordTrace]
  refine ⟨11618053556491285255909379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30981476150643427349091677 11618053556491285255909379)
  ·
    refine ⟨17427080334736927883864069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11618053556491285255909379 17427080334736927883864069)
    ·
      refine ⟨3267577562763173978224513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17427080334736927883864069 3267577562763173978224513)
      ·
        refine ⟨2450683172072380483668385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3267577562763173978224513 2450683172072380483668385)
        ·
          refine ⟨1838012379054285362751289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2450683172072380483668385 1838012379054285362751289)
          ·
            refine ⟨1378509284290714022063467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1838012379054285362751289 1378509284290714022063467)
            ·
              refine ⟨2067763926436071033095201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378509284290714022063467 2067763926436071033095201)
              ·
                refine ⟨1550822944827053274821401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067763926436071033095201 1550822944827053274821401)
                ·
                  refine ⟨1163117208620289956116051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1550822944827053274821401 1163117208620289956116051)
                  ·
                    refine ⟨1744675812930434934174077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1163117208620289956116051 1744675812930434934174077)
                    ·
                      refine ⟨654253429848913100315279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1744675812930434934174077 654253429848913100315279)
                      ·
                        rfl

theorem cell23_1274154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1274154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274154 prefixEnd_1274154 := by exact prefixLift 1274154
  have htrace : WordTrace (prefixWord ++ tailWord_1274154) baseStart_1274154 baseEnd_1274154 := by
    simpa [prefixWord, tailWord_1274154, baseEnd_1274154] using wordTrace_append hprefix tailTrace_1274154
  have hstable : (prefixWord ++ tailWord_1274154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274154).length < 2 ^ (prefixWord ++ tailWord_1274154).sum := by decide
  have hdescent : baseEnd_1274154 < baseStart_1274154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274156 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_1274156 : Nat := 118140960795 + 1274156 * 2 ^ 59
def prefixEnd_1274156 : Nat := 4983230072969 + 3 ^ 40 * 1274156 * 2
def baseEnd_1274156 : Nat := 654254456810222092490269

theorem tailTrace_1274156 : CollatzResearch.WordTrace tailWord_1274156 prefixEnd_1274156 654254456810222092490269 := by
  unfold tailWord_1274156
  simp only [CollatzResearch.WordTrace]
  refine ⟨23236143585978947682605161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30981524781305263576806881 23236143585978947682605161)
  ·
    refine ⟨17427107689484210761953871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23236143585978947682605161 17427107689484210761953871)
    ·
      refine ⟨26140661534226316142930807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17427107689484210761953871 26140661534226316142930807)
      ·
        refine ⟨39210992301339474214396211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26140661534226316142930807 39210992301339474214396211)
        ·
          refine ⟨58816488452009211321594317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39210992301339474214396211 58816488452009211321594317)
          ·
            refine ⟨22056183169503454245597869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58816488452009211321594317 22056183169503454245597869)
            ·
              refine ⟨8271068688563795342099201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22056183169503454245597869 8271068688563795342099201)
              ·
                refine ⟨6203301516422846506574401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8271068688563795342099201 6203301516422846506574401)
                ·
                  refine ⟨4652476137317134879930801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6203301516422846506574401 4652476137317134879930801)
                  ·
                    refine ⟨3489357102987851159948101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4652476137317134879930801 3489357102987851159948101)
                    ·
                      refine ⟨654254456810222092490269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3489357102987851159948101 654254456810222092490269)
                      ·
                        rfl

theorem cell23_1274156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_1274156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274156 prefixEnd_1274156 := by exact prefixLift 1274156
  have htrace : WordTrace (prefixWord ++ tailWord_1274156) baseStart_1274156 baseEnd_1274156 := by
    simpa [prefixWord, tailWord_1274156, baseEnd_1274156] using wordTrace_append hprefix tailTrace_1274156
  have hstable : (prefixWord ++ tailWord_1274156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274156).length < 2 ^ (prefixWord ++ tailWord_1274156).sum := by decide
  have hdescent : baseEnd_1274156 < baseStart_1274156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274160 : List Nat := [2, 1, 1, 1, 2, 2, 2, 6, 2, 2, 2]
def baseStart_1274160 : Nat := 118140960795 + 1274160 * 2 ^ 59
def prefixEnd_1274160 : Nat := 4983230072969 + 3 ^ 40 * 1274160 * 2
def baseEnd_1274160 : Nat := 654256510732840076840251

theorem tailTrace_1274160 : CollatzResearch.WordTrace tailWord_1274160 prefixEnd_1274160 654256510732840076840251 := by
  unfold tailWord_1274160
  simp only [CollatzResearch.WordTrace]
  refine ⟨23236216531971702024177967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30981622042628936032237289 23236216531971702024177967)
  ·
    refine ⟨34854324797957553036266951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23236216531971702024177967 34854324797957553036266951)
    ·
      refine ⟨52281487196936329554400427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34854324797957553036266951 52281487196936329554400427)
      ·
        refine ⟨78422230795404494331600641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52281487196936329554400427 78422230795404494331600641)
        ·
          refine ⟨58816673096553370748700481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78422230795404494331600641 58816673096553370748700481)
          ·
            refine ⟨44112504822415028061525361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58816673096553370748700481 44112504822415028061525361)
            ·
              refine ⟨33084378616811271046144021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44112504822415028061525361 33084378616811271046144021)
              ·
                refine ⟨1550830247663028330288001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33084378616811271046144021 1550830247663028330288001)
                ·
                  refine ⟨1163122685747271247716001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1550830247663028330288001 1163122685747271247716001)
                  ·
                    refine ⟨872342014310453435787001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1163122685747271247716001 872342014310453435787001)
                    ·
                      refine ⟨654256510732840076840251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 872342014310453435787001 654256510732840076840251)
                      ·
                        rfl

theorem cell23_1274160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 2, 2, 2].length) (baseStart_1274160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274160 prefixEnd_1274160 := by exact prefixLift 1274160
  have htrace : WordTrace (prefixWord ++ tailWord_1274160) baseStart_1274160 baseEnd_1274160 := by
    simpa [prefixWord, tailWord_1274160, baseEnd_1274160] using wordTrace_append hprefix tailTrace_1274160
  have hstable : (prefixWord ++ tailWord_1274160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274160).length < 2 ^ (prefixWord ++ tailWord_1274160).sum := by decide
  have hdescent : baseEnd_1274160 < baseStart_1274160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274176 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 3]
def baseStart_1274176 : Nat := 118140960795 + 1274176 * 2 ^ 59
def prefixEnd_1274176 : Nat := 4983230072969 + 3 ^ 40 * 1274176 * 2
def baseEnd_1274176 : Nat := 654264726423312014240177

theorem tailTrace_1274176 : CollatzResearch.WordTrace tailWord_1274176 prefixEnd_1274176 654264726423312014240177 := by
  unfold tailWord_1274176
  simp only [CollatzResearch.WordTrace]
  refine ⟨23236508315942719390469191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30982011087923625853958921 23236508315942719390469191)
  ·
    refine ⟨34854762473914079085703787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23236508315942719390469191 34854762473914079085703787)
    ·
      refine ⟨52282143710871118628555681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34854762473914079085703787 52282143710871118628555681)
      ·
        refine ⟨39211607783153338971416761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52282143710871118628555681 39211607783153338971416761)
        ·
          refine ⟨29408705837365004228562571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39211607783153338971416761 29408705837365004228562571)
          ·
            refine ⟨44113058756047506342843857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29408705837365004228562571 44113058756047506342843857)
            ·
              refine ⟨33084794067035629757132893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44113058756047506342843857 33084794067035629757132893)
              ·
                refine ⟨12406797775138361158924835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33084794067035629757132893 12406797775138361158924835)
                ·
                  refine ⟨18610196662707541738387253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12406797775138361158924835 18610196662707541738387253)
                  ·
                    refine ⟨1744705937128832037973805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18610196662707541738387253 1744705937128832037973805)
                    ·
                      refine ⟨654264726423312014240177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1744705937128832037973805 654264726423312014240177)
                      ·
                        rfl

theorem cell23_1274176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_1274176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274176 prefixEnd_1274176 := by exact prefixLift 1274176
  have htrace : WordTrace (prefixWord ++ tailWord_1274176) baseStart_1274176 baseEnd_1274176 := by
    simpa [prefixWord, tailWord_1274176, baseEnd_1274176] using wordTrace_append hprefix tailTrace_1274176
  have hstable : (prefixWord ++ tailWord_1274176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274176).length < 2 ^ (prefixWord ++ tailWord_1274176).sum := by decide
  have hdescent : baseEnd_1274176 < baseStart_1274176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274213 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 2, 5]
def baseStart_1274213 : Nat := 118140960795 + 1274213 * 2 ^ 59
def prefixEnd_1274213 : Nat := 4983230072969 + 3 ^ 40 * 1274213 * 2
def baseEnd_1274213 : Nat := 218094575069176123159169

theorem tailTrace_1274213 : CollatzResearch.WordTrace tailWord_1274213 prefixEnd_1274213 218094575069176123159169 := by
  unfold tailWord_1274213
  simp only [CollatzResearch.WordTrace]
  refine ⟨46474366132751394100035293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30982910755167596066690195 46474366132751394100035293)
  ·
    refine ⟨17427887299781772787513235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46474366132751394100035293 17427887299781772787513235)
    ·
      refine ⟨26141830949672659181269853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17427887299781772787513235 26141830949672659181269853)
      ·
        refine ⟨9803186606127247192976195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26141830949672659181269853 9803186606127247192976195)
        ·
          refine ⟨14704779909190870789464293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9803186606127247192976195 14704779909190870789464293)
          ·
            refine ⟨2757146232973288273024555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14704779909190870789464293 2757146232973288273024555)
            ·
              refine ⟨4135719349459932409536833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2757146232973288273024555 4135719349459932409536833)
              ·
                refine ⟨3101789512094949307152625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4135719349459932409536833 3101789512094949307152625)
                ·
                  refine ⟨2326342134071211980364469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3101789512094949307152625 2326342134071211980364469)
                  ·
                    refine ⟨218094575069176123159169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2326342134071211980364469 218094575069176123159169)
                    ·
                      rfl

theorem cell23_1274213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_1274213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274213 prefixEnd_1274213 := by exact prefixLift 1274213
  have htrace : WordTrace (prefixWord ++ tailWord_1274213) baseStart_1274213 baseEnd_1274213 := by
    simpa [prefixWord, tailWord_1274213, baseEnd_1274213] using wordTrace_append hprefix tailTrace_1274213
  have hstable : (prefixWord ++ tailWord_1274213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274213).length < 2 ^ (prefixWord ++ tailWord_1274213).sum := by decide
  have hdescent : baseEnd_1274213 < baseStart_1274213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274233 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 1, 6, 2]
def baseStart_1274233 : Nat := 118140960795 + 1274233 * 2 ^ 59
def prefixEnd_1274233 : Nat := 4983230072969 + 3 ^ 40 * 1274233 * 2
def baseEnd_1274233 : Nat := 654293994820618291227415

theorem tailTrace_1274233 : CollatzResearch.WordTrace tailWord_1274233 prefixEnd_1274233 654293994820618291227415 := by
  unfold tailWord_1274233
  simp only [CollatzResearch.WordTrace]
  refine ⟨46475095592678937515763353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30983397061785958343842235 46475095592678937515763353)
  ·
    refine ⟨34856321694509203136822515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46475095592678937515763353 34856321694509203136822515)
    ·
      refine ⟨52284482541763804705233773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34856321694509203136822515 52284482541763804705233773)
      ·
        refine ⟨19606680953161426764462665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52284482541763804705233773 19606680953161426764462665)
        ·
          refine ⟨14705010714871070073346999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19606680953161426764462665 14705010714871070073346999)
          ·
            refine ⟨22057516072306605110020499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14705010714871070073346999 22057516072306605110020499)
            ·
              refine ⟨33086274108459907665030749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22057516072306605110020499 33086274108459907665030749)
              ·
                refine ⟨12407352790672465374386531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33086274108459907665030749 12407352790672465374386531)
                ·
                  refine ⟨18611029186008698061579797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12407352790672465374386531 18611029186008698061579797)
                  ·
                    refine ⟨872391993094157721636553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18611029186008698061579797 872391993094157721636553)
                    ·
                      refine ⟨654293994820618291227415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 872391993094157721636553 654293994820618291227415)
                      ·
                        rfl

theorem cell23_1274233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_1274233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274233 prefixEnd_1274233 := by exact prefixLift 1274233
  have htrace : WordTrace (prefixWord ++ tailWord_1274233) baseStart_1274233 baseEnd_1274233 := by
    simpa [prefixWord, tailWord_1274233, baseEnd_1274233] using wordTrace_append hprefix tailTrace_1274233
  have hstable : (prefixWord ++ tailWord_1274233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274233).length < 2 ^ (prefixWord ++ tailWord_1274233).sum := by decide
  have hdescent : baseEnd_1274233 < baseStart_1274233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274296 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_1274296 : Nat := 118140960795 + 1274296 * 2 ^ 59
def prefixEnd_1274296 : Nat := 4983230072969 + 3 ^ 40 * 1274296 * 2
def baseEnd_1274296 : Nat := 654326344101851544739625

theorem tailTrace_1274296 : CollatzResearch.WordTrace tailWord_1274296 prefixEnd_1274296 654326344101851544739625 := by
  unfold tailWord_1274296
  simp only [CollatzResearch.WordTrace]
  refine ⟨23238696695725349637653371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30984928927633799516871161 23238696695725349637653371)
  ·
    refine ⟨34858045043588024456480057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23238696695725349637653371 34858045043588024456480057)
    ·
      refine ⟨26143533782691018342360043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34858045043588024456480057 26143533782691018342360043)
      ·
        refine ⟨39215300674036527513540065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26143533782691018342360043 39215300674036527513540065)
        ·
          refine ⟨29411475505527395635155049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39215300674036527513540065 29411475505527395635155049)
          ·
            refine ⟨22058606629145546726366287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29411475505527395635155049 22058606629145546726366287)
            ·
              refine ⟨33087909943718320089549431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22058606629145546726366287 33087909943718320089549431)
              ·
                refine ⟨49631864915577480134324147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33087909943718320089549431 49631864915577480134324147)
                ·
                  refine ⟨74447797373366220201486221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49631864915577480134324147 74447797373366220201486221)
                  ·
                    refine ⟨27917924015012332575557333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74447797373366220201486221 27917924015012332575557333)
                    ·
                      refine ⟨654326344101851544739625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27917924015012332575557333 654326344101851544739625)
                      ·
                        rfl

theorem cell23_1274296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_1274296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274296 prefixEnd_1274296 := by exact prefixLift 1274296
  have htrace : WordTrace (prefixWord ++ tailWord_1274296) baseStart_1274296 baseEnd_1274296 := by
    simpa [prefixWord, tailWord_1274296, baseEnd_1274296] using wordTrace_append hprefix tailTrace_1274296
  have hstable : (prefixWord ++ tailWord_1274296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274296).length < 2 ^ (prefixWord ++ tailWord_1274296).sum := by decide
  have hdescent : baseEnd_1274296 < baseStart_1274296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274350 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_1274350 : Nat := 118140960795 + 1274350 * 2 ^ 59
def prefixEnd_1274350 : Nat := 4983230072969 + 3 ^ 40 * 1274350 * 2
def baseEnd_1274350 : Nat := 218118024019064777821459

theorem tailTrace_1274350 : CollatzResearch.WordTrace tailWord_1274350 prefixEnd_1274350 218118024019064777821459 := by
  unfold tailWord_1274350
  simp only [CollatzResearch.WordTrace]
  refine ⟨5809920366656883312221563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30986241955503377665181669 5809920366656883312221563)
  ·
    refine ⟨8714880549985324968332345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5809920366656883312221563 8714880549985324968332345)
    ·
      refine ⟨6536160412488993726249259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8714880549985324968332345 6536160412488993726249259)
      ·
        refine ⟨9804240618733490589373889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6536160412488993726249259 9804240618733490589373889)
        ·
          refine ⟨7353180464050117942030417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9804240618733490589373889 7353180464050117942030417)
          ·
            refine ⟨5514885348037588456522813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7353180464050117942030417 5514885348037588456522813)
            ·
              refine ⟨2068082005514095671196055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5514885348037588456522813 2068082005514095671196055)
              ·
                refine ⟨3102123008271143506794083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068082005514095671196055 3102123008271143506794083)
                ·
                  refine ⟨4653184512406715260191125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3102123008271143506794083 4653184512406715260191125)
                  ·
                    refine ⟨218118024019064777821459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4653184512406715260191125 218118024019064777821459)
                    ·
                      rfl

theorem cell23_1274350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_1274350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274350 prefixEnd_1274350 := by exact prefixLift 1274350
  have htrace : WordTrace (prefixWord ++ tailWord_1274350) baseStart_1274350 baseEnd_1274350 := by
    simpa [prefixWord, tailWord_1274350, baseEnd_1274350] using wordTrace_append hprefix tailTrace_1274350
  have hstable : (prefixWord ++ tailWord_1274350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274350).length < 2 ^ (prefixWord ++ tailWord_1274350).sum := by decide
  have hdescent : baseEnd_1274350 < baseStart_1274350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274353 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_1274353 : Nat := 118140960795 + 1274353 * 2 ^ 59
def prefixEnd_1274353 : Nat := 4983230072969 + 3 ^ 40 * 1274353 * 2
def baseEnd_1274353 : Nat := 654355612499157821726863

theorem tailTrace_1274353 : CollatzResearch.WordTrace tailWord_1274353 prefixEnd_1274353 654355612499157821726863 := by
  unfold tailWord_1274353
  simp only [CollatzResearch.WordTrace]
  refine ⟨46479472352244198010131713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30986314901496132006754475 46479472352244198010131713)
  ·
    refine ⟨34859604264183148507598785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46479472352244198010131713 34859604264183148507598785)
    ·
      refine ⟨26144703198137361380699089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34859604264183148507598785 26144703198137361380699089)
      ·
        refine ⟨19608527398603021035524317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26144703198137361380699089 19608527398603021035524317)
        ·
          refine ⟨7353197774476132888321619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19608527398603021035524317 7353197774476132888321619)
          ·
            refine ⟨11029796661714199332482429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7353197774476132888321619 11029796661714199332482429)
            ·
              refine ⟨4136173748142824749680911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11029796661714199332482429 4136173748142824749680911)
              ·
                refine ⟨6204260622214237124521367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4136173748142824749680911 6204260622214237124521367)
                ·
                  refine ⟨9306390933321355686782051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6204260622214237124521367 9306390933321355686782051)
                  ·
                    refine ⟨13959586399982033530173077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9306390933321355686782051 13959586399982033530173077)
                    ·
                      refine ⟨654355612499157821726863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13959586399982033530173077 654355612499157821726863)
                      ·
                        rfl

theorem cell23_1274353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_1274353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274353 prefixEnd_1274353 := by exact prefixLift 1274353
  have htrace : WordTrace (prefixWord ++ tailWord_1274353) baseStart_1274353 baseEnd_1274353 := by
    simpa [prefixWord, tailWord_1274353, baseEnd_1274353] using wordTrace_append hprefix tailTrace_1274353
  have hstable : (prefixWord ++ tailWord_1274353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274353).length < 2 ^ (prefixWord ++ tailWord_1274353).sum := by decide
  have hdescent : baseEnd_1274353 < baseStart_1274353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274447 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 4, 2, 2]
def baseStart_1274447 : Nat := 118140960795 + 1274447 * 2 ^ 59
def prefixEnd_1274447 : Nat := 4983230072969 + 3 ^ 40 * 1274447 * 2
def baseEnd_1274447 : Nat := 654403879680680453951431

theorem tailTrace_1274447 : CollatzResearch.WordTrace tailWord_1274447 prefixEnd_1274447 654403879680680453951431 := by
  unfold tailWord_1274447
  simp only [CollatzResearch.WordTrace]
  refine ⟨46482900813903652064053595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30988600542602434709369063 46482900813903652064053595)
  ·
    refine ⟨69724351220855478096080393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46482900813903652064053595 69724351220855478096080393)
    ·
      refine ⟨52293263415641608572060295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69724351220855478096080393 52293263415641608572060295)
      ·
        refine ⟨78439895123462412858090443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52293263415641608572060295 78439895123462412858090443)
        ·
          refine ⟨117659842685193619287135665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78439895123462412858090443 117659842685193619287135665)
          ·
            refine ⟨88244882013895214465351749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117659842685193619287135665 88244882013895214465351749)
            ·
              refine ⟨16545915377605352712253453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88244882013895214465351749 16545915377605352712253453)
              ·
                refine ⟨6204718266602007267095045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16545915377605352712253453 6204718266602007267095045)
                ·
                  refine ⟨1163384674987876362580321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6204718266602007267095045 1163384674987876362580321)
                  ·
                    refine ⟨872538506240907271935241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1163384674987876362580321 872538506240907271935241)
                    ·
                      refine ⟨654403879680680453951431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 872538506240907271935241 654403879680680453951431)
                      ·
                        rfl

theorem cell23_1274447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 2, 2].length) (baseStart_1274447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274447 prefixEnd_1274447 := by exact prefixLift 1274447
  have htrace : WordTrace (prefixWord ++ tailWord_1274447) baseStart_1274447 baseEnd_1274447 := by
    simpa [prefixWord, tailWord_1274447, baseEnd_1274447] using wordTrace_append hprefix tailTrace_1274447
  have hstable : (prefixWord ++ tailWord_1274447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274447).length < 2 ^ (prefixWord ++ tailWord_1274447).sum := by decide
  have hdescent : baseEnd_1274447 < baseStart_1274447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274450 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_1274450 : Nat := 118140960795 + 1274450 * 2 ^ 59
def prefixEnd_1274450 : Nat := 4983230072969 + 3 ^ 40 * 1274450 * 2
def baseEnd_1274450 : Nat := 654405420122643942213917

theorem tailTrace_1274450 : CollatzResearch.WordTrace tailWord_1274450 prefixEnd_1274450 654405420122643942213917 := by
  unfold tailWord_1274450
  simp only [CollatzResearch.WordTrace]
  refine ⟨11620752558223195894103201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30988673488595189050941869 11620752558223195894103201)
  ·
    refine ⟨8715564418667396920577401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11620752558223195894103201 8715564418667396920577401)
    ·
      refine ⟨6536673314000547690433051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8715564418667396920577401 6536673314000547690433051)
      ·
        refine ⟨9805009971000821535649577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6536673314000547690433051 9805009971000821535649577)
        ·
          refine ⟨7353757478250616151737183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9805009971000821535649577 7353757478250616151737183)
          ·
            refine ⟨11030636217375924227605775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7353757478250616151737183 11030636217375924227605775)
            ·
              refine ⟨16545954326063886341408663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11030636217375924227605775 16545954326063886341408663)
              ·
                refine ⟨24818931489095829512112995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16545954326063886341408663 24818931489095829512112995)
                ·
                  refine ⟨37228397233643744268169493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24818931489095829512112995 37228397233643744268169493)
                  ·
                    refine ⟨1745081120327050512570445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37228397233643744268169493 1745081120327050512570445)
                    ·
                      refine ⟨654405420122643942213917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1745081120327050512570445 654405420122643942213917)
                      ·
                        rfl

theorem cell23_1274450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_1274450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274450 prefixEnd_1274450 := by exact prefixLift 1274450
  have htrace : WordTrace (prefixWord ++ tailWord_1274450) baseStart_1274450 baseEnd_1274450 := by
    simpa [prefixWord, tailWord_1274450, baseEnd_1274450] using wordTrace_append hprefix tailTrace_1274450
  have hstable : (prefixWord ++ tailWord_1274450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274450).length < 2 ^ (prefixWord ++ tailWord_1274450).sum := by decide
  have hdescent : baseEnd_1274450 < baseStart_1274450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274464 : List Nat := [2, 1, 1, 3, 2, 1, 4, 3, 2, 2, 2]
def baseStart_1274464 : Nat := 118140960795 + 1274464 * 2 ^ 59
def prefixEnd_1274464 : Nat := 4983230072969 + 3 ^ 40 * 1274464 * 2
def baseEnd_1274464 : Nat := 654412608851806887438853

theorem tailTrace_1274464 : CollatzResearch.WordTrace tailWord_1274464 prefixEnd_1274464 654412608851806887438853 := by
  unfold tailWord_1274464
  simp only [CollatzResearch.WordTrace]
  refine ⟨23241760427421031983711223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30989013903228042644948297 23241760427421031983711223)
  ·
    refine ⟨34862640641131547975566835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23241760427421031983711223 34862640641131547975566835)
    ·
      refine ⟨52293960961697321963350253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34862640641131547975566835 52293960961697321963350253)
      ·
        refine ⟨19610235360636495736256345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52293960961697321963350253 19610235360636495736256345)
        ·
          refine ⟨14707676520477371802192259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19610235360636495736256345 14707676520477371802192259)
          ·
            refine ⟨22061514780716057703288389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14707676520477371802192259 22061514780716057703288389)
            ·
              refine ⟨4136534021384260819366573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22061514780716057703288389 4136534021384260819366573)
              ·
                refine ⟨1551200258019097807262465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4136534021384260819366573 1551200258019097807262465)
                ·
                  refine ⟨1163400193514323355446849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1551200258019097807262465 1163400193514323355446849)
                  ·
                    refine ⟨872550145135742516585137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1163400193514323355446849 872550145135742516585137)
                    ·
                      refine ⟨654412608851806887438853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 872550145135742516585137 654412608851806887438853)
                      ·
                        rfl

theorem cell23_1274464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_1274464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274464 prefixEnd_1274464 := by exact prefixLift 1274464
  have htrace : WordTrace (prefixWord ++ tailWord_1274464) baseStart_1274464 baseEnd_1274464 := by
    simpa [prefixWord, tailWord_1274464, baseEnd_1274464] using wordTrace_append hprefix tailTrace_1274464
  have hstable : (prefixWord ++ tailWord_1274464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274464).length < 2 ^ (prefixWord ++ tailWord_1274464).sum := by decide
  have hdescent : baseEnd_1274464 < baseStart_1274464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274485 : List Nat := [1, 3, 4, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_1274485 : Nat := 118140960795 + 1274485 * 2 ^ 59
def prefixEnd_1274485 : Nat := 4983230072969 + 3 ^ 40 * 1274485 * 2
def baseEnd_1274485 : Nat := 654423391945551305276257

theorem tailTrace_1274485 : CollatzResearch.WordTrace tailWord_1274485 prefixEnd_1274485 654423391945551305276257 := by
  unfold tailWord_1274485
  simp only [CollatzResearch.WordTrace]
  refine ⟨46484286787765984553936909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30989524525177323035957939 46484286787765984553936909)
  ·
    refine ⟨17431607545412244207726341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46484286787765984553936909 17431607545412244207726341)
    ·
      refine ⟨3268426414764795788948689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17431607545412244207726341 3268426414764795788948689)
      ·
        refine ⟨2451319811073596841711517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3268426414764795788948689 2451319811073596841711517)
        ·
          refine ⟨919244929152598815641819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2451319811073596841711517 919244929152598815641819)
          ·
            refine ⟨1378867393728898223462729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919244929152598815641819 1378867393728898223462729)
            ·
              refine ⟨1034150545296673667597047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1378867393728898223462729 1034150545296673667597047)
              ·
                refine ⟨1551225817945010501395571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034150545296673667597047 1551225817945010501395571)
                ·
                  refine ⟨2326838726917515752093357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1551225817945010501395571 2326838726917515752093357)
                  ·
                    refine ⟨872564522594068407035009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2326838726917515752093357 872564522594068407035009)
                    ·
                      refine ⟨654423391945551305276257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 872564522594068407035009 654423391945551305276257)
                      ·
                        rfl

theorem cell23_1274485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_1274485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274485 prefixEnd_1274485 := by exact prefixLift 1274485
  have htrace : WordTrace (prefixWord ++ tailWord_1274485) baseStart_1274485 baseEnd_1274485 := by
    simpa [prefixWord, tailWord_1274485, baseEnd_1274485] using wordTrace_append hprefix tailTrace_1274485
  have hstable : (prefixWord ++ tailWord_1274485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274485).length < 2 ^ (prefixWord ++ tailWord_1274485).sum := by decide
  have hdescent : baseEnd_1274485 < baseStart_1274485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274510 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1274510 : Nat := 118140960795 + 1274510 * 2 ^ 59
def prefixEnd_1274510 : Nat := 4983230072969 + 3 ^ 40 * 1274510 * 2
def baseEnd_1274510 : Nat := 654436228961913707463641

theorem tailTrace_1274510 : CollatzResearch.WordTrace tailWord_1274510 prefixEnd_1274510 654436228961913707463641 := by
  unfold tailWord_1274510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5810649826584426727949623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30990132408450275882397989 5810649826584426727949623)
  ·
    refine ⟨8715974739876640091924435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5810649826584426727949623 8715974739876640091924435)
    ·
      refine ⟨13073962109814960137886653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8715974739876640091924435 13073962109814960137886653)
      ·
        refine ⟨4902735791180610051707495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13073962109814960137886653 4902735791180610051707495)
        ·
          refine ⟨7354103686770915077561243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4902735791180610051707495 7354103686770915077561243)
          ·
            refine ⟨11031155530156372616341865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7354103686770915077561243 11031155530156372616341865)
            ·
              refine ⟨8273366647617279462256399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11031155530156372616341865 8273366647617279462256399)
              ·
                refine ⟨12410049971425919193384599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8273366647617279462256399 12410049971425919193384599)
                ·
                  refine ⟨18615074957138878790076899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12410049971425919193384599 18615074957138878790076899)
                  ·
                    refine ⟨27922612435708318185115349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18615074957138878790076899 27922612435708318185115349)
                    ·
                      refine ⟨654436228961913707463641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27922612435708318185115349 654436228961913707463641)
                      ·
                        rfl

theorem cell23_1274510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1274510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274510 prefixEnd_1274510 := by exact prefixLift 1274510
  have htrace : WordTrace (prefixWord ++ tailWord_1274510) baseStart_1274510 baseEnd_1274510 := by
    simpa [prefixWord, tailWord_1274510, baseEnd_1274510] using wordTrace_append hprefix tailTrace_1274510
  have hstable : (prefixWord ++ tailWord_1274510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274510).length < 2 ^ (prefixWord ++ tailWord_1274510).sum := by decide
  have hdescent : baseEnd_1274510 < baseStart_1274510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274520 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1274520 : Nat := 118140960795 + 1274520 * 2 ^ 59
def prefixEnd_1274520 : Nat := 4983230072969 + 3 ^ 40 * 1274520 * 2
def baseEnd_1274520 : Nat := 654441363768458668338595

theorem tailTrace_1274520 : CollatzResearch.WordTrace tailWord_1274520 prefixEnd_1274520 654441363768458668338595 := by
  unfold tailWord_1274520
  simp only [CollatzResearch.WordTrace]
  refine ⟨23242781671319592765730507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30990375561759457020974009 23242781671319592765730507)
  ·
    refine ⟨34864172506979389148595761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23242781671319592765730507 34864172506979389148595761)
    ·
      refine ⟨26148129380234541861446821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34864172506979389148595761 26148129380234541861446821)
      ·
        refine ⟨4902774258793976599021279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26148129380234541861446821 4902774258793976599021279)
        ·
          refine ⟨7354161388190964898531919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4902774258793976599021279 7354161388190964898531919)
          ·
            refine ⟨11031242082286447347797879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7354161388190964898531919 11031242082286447347797879)
            ·
              refine ⟨16546863123429671021696819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11031242082286447347797879 16546863123429671021696819)
              ·
                refine ⟨24820294685144506532545229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16546863123429671021696819 24820294685144506532545229)
                ·
                  refine ⟨9307610506929189949704461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24820294685144506532545229 9307610506929189949704461)
                  ·
                    refine ⟨3490353940098446231139173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9307610506929189949704461 3490353940098446231139173)
                    ·
                      refine ⟨654441363768458668338595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3490353940098446231139173 654441363768458668338595)
                      ·
                        rfl

theorem cell23_1274520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1274520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274520 prefixEnd_1274520 := by exact prefixLift 1274520
  have htrace : WordTrace (prefixWord ++ tailWord_1274520) baseStart_1274520 baseEnd_1274520 := by
    simpa [prefixWord, tailWord_1274520, baseEnd_1274520] using wordTrace_append hprefix tailTrace_1274520
  have hstable : (prefixWord ++ tailWord_1274520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274520).length < 2 ^ (prefixWord ++ tailWord_1274520).sum := by decide
  have hdescent : baseEnd_1274520 < baseStart_1274520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274538 : List Nat := [3, 1, 5, 2, 1, 2, 1, 3, 5]
def baseStart_1274538 : Nat := 118140960795 + 1274538 * 2 ^ 59
def prefixEnd_1274538 : Nat := 4983230072969 + 3 ^ 40 * 1274538 * 2
def baseEnd_1274538 : Nat := 72716734046693288657057

theorem tailTrace_1274538 : CollatzResearch.WordTrace tailWord_1274538 prefixEnd_1274538 72716734046693288657057 := by
  unfold tailWord_1274538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11621554964143493651404067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30990813237715983070410845 11621554964143493651404067)
  ·
    refine ⟨17432332446215240477106101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11621554964143493651404067 17432332446215240477106101)
    ·
      refine ⟨1634281166832678794728697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17432332446215240477106101 1634281166832678794728697)
      ·
        refine ⟨1225710875124509096046523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1634281166832678794728697 1225710875124509096046523)
        ·
          refine ⟨1838566312686763644069785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225710875124509096046523 1838566312686763644069785)
          ·
            refine ⟨1378924734515072733052339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1838566312686763644069785 1378924734515072733052339)
            ·
              refine ⟨2068387101772609099578509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378924734515072733052339 2068387101772609099578509)
              ·
                refine ⟨775645163164728412341941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2068387101772609099578509 775645163164728412341941)
                ·
                  refine ⟨72716734046693288657057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 775645163164728412341941 72716734046693288657057)
                  ·
                    rfl

theorem cell23_1274538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 5].length) (baseStart_1274538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274538 prefixEnd_1274538 := by exact prefixLift 1274538
  have htrace : WordTrace (prefixWord ++ tailWord_1274538) baseStart_1274538 baseEnd_1274538 := by
    simpa [prefixWord, tailWord_1274538, baseEnd_1274538] using wordTrace_append hprefix tailTrace_1274538
  have hstable : (prefixWord ++ tailWord_1274538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274538).length < 2 ^ (prefixWord ++ tailWord_1274538).sum := by decide
  have hdescent : baseEnd_1274538 < baseStart_1274538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274557 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_1274557 : Nat := 118140960795 + 1274557 * 2 ^ 59
def prefixEnd_1274557 : Nat := 4983230072969 + 3 ^ 40 * 1274557 * 2
def baseEnd_1274557 : Nat := 654460362552675023575925

theorem tailTrace_1274557 : CollatzResearch.WordTrace tailWord_1274557 prefixEnd_1274557 654460362552675023575925 := by
  unfold tailWord_1274557
  simp only [CollatzResearch.WordTrace]
  refine ⟨46486912843505140850557925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30991275229003427233705283 46486912843505140850557925)
  ·
    refine ⟨8716296158157213909479611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46486912843505140850557925 8716296158157213909479611)
    ·
      refine ⟨13074444237235820864219417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8716296158157213909479611 13074444237235820864219417)
      ·
        refine ⟨9805833177926865648164563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13074444237235820864219417 9805833177926865648164563)
        ·
          refine ⟨14708749766890298472246845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9805833177926865648164563 14708749766890298472246845)
          ·
            refine ⟨5515781162583861927092567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14708749766890298472246845 5515781162583861927092567)
            ·
              refine ⟨8273671743875792890638851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5515781162583861927092567 8273671743875792890638851)
              ·
                refine ⟨12410507615813689335958277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8273671743875792890638851 12410507615813689335958277)
                ·
                  refine ⟨2326970177965066750492177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12410507615813689335958277 2326970177965066750492177)
                  ·
                    refine ⟨1745227633473800062869133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2326970177965066750492177 1745227633473800062869133)
                    ·
                      refine ⟨654460362552675023575925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1745227633473800062869133 654460362552675023575925)
                      ·
                        rfl

theorem cell23_1274557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_1274557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274557 prefixEnd_1274557 := by exact prefixLift 1274557
  have htrace : WordTrace (prefixWord ++ tailWord_1274557) baseStart_1274557 baseEnd_1274557 := by
    simpa [prefixWord, tailWord_1274557, baseEnd_1274557] using wordTrace_append hprefix tailTrace_1274557
  have hstable : (prefixWord ++ tailWord_1274557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274557).length < 2 ^ (prefixWord ++ tailWord_1274557).sum := by decide
  have hdescent : baseEnd_1274557 < baseStart_1274557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274560 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 8]
def baseStart_1274560 : Nat := 118140960795 + 1274560 * 2 ^ 59
def prefixEnd_1274560 : Nat := 4983230072969 + 3 ^ 40 * 1274560 * 2
def baseEnd_1274560 : Nat := 72717989221626501315379

theorem tailTrace_1274560 : CollatzResearch.WordTrace tailWord_1274560 prefixEnd_1274560 72717989221626501315379 := by
  unfold tailWord_1274560
  simp only [CollatzResearch.WordTrace]
  refine ⟨23243511131247136181458567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30991348174996181575278089 23243511131247136181458567)
  ·
    refine ⟨34865266696870704272187851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23243511131247136181458567 34865266696870704272187851)
    ·
      refine ⟨52297900045306056408281777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34865266696870704272187851 52297900045306056408281777)
      ·
        refine ⟨39223425033979542306211333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52297900045306056408281777 39223425033979542306211333)
        ·
          refine ⟨7354392193871164182414625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39223425033979542306211333 7354392193871164182414625)
          ·
            refine ⟨5515794145403373136810969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7354392193871164182414625 5515794145403373136810969)
            ·
              refine ⟨4136845609052529852608227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5515794145403373136810969 4136845609052529852608227)
              ·
                refine ⟨6205268413578794778912341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4136845609052529852608227 6205268413578794778912341)
                ·
                  refine ⟨72717989221626501315379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6205268413578794778912341 72717989221626501315379)
                  ·
                    rfl

theorem cell23_1274560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 8].length) (baseStart_1274560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274560 prefixEnd_1274560 := by exact prefixLift 1274560
  have htrace : WordTrace (prefixWord ++ tailWord_1274560) baseStart_1274560 baseEnd_1274560 := by
    simpa [prefixWord, tailWord_1274560, baseEnd_1274560] using wordTrace_append hprefix tailTrace_1274560
  have hstable : (prefixWord ++ tailWord_1274560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274560).length < 2 ^ (prefixWord ++ tailWord_1274560).sum := by decide
  have hdescent : baseEnd_1274560 < baseStart_1274560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274564 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_1274564 : Nat := 118140960795 + 1274564 * 2 ^ 59
def prefixEnd_1274564 : Nat := 4983230072969 + 3 ^ 40 * 1274564 * 2
def baseEnd_1274564 : Nat := 218154652305752165396131

theorem tailTrace_1274564 : CollatzResearch.WordTrace tailWord_1274564 prefixEnd_1274564 218154652305752165396131 := by
  unfold tailWord_1274564
  simp only [CollatzResearch.WordTrace]
  refine ⟨23243584077239890523031373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30991445436319854030708497 23243584077239890523031373)
  ·
    refine ⟨8716344028964958946136765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23243584077239890523031373 8716344028964958946136765)
    ·
      refine ⟨3268629010861859604801287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8716344028964958946136765 3268629010861859604801287)
      ·
        refine ⟨4902943516292789407201931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3268629010861859604801287 4902943516292789407201931)
        ·
          refine ⟨7354415274439184110802897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4902943516292789407201931 7354415274439184110802897)
          ·
            refine ⟨5515811455829388083102173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7354415274439184110802897 5515811455829388083102173)
            ·
              refine ⟨2068429295936020531163315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5515811455829388083102173 2068429295936020531163315)
              ·
                refine ⟨3102643943904030796744973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068429295936020531163315 3102643943904030796744973)
                ·
                  refine ⟨1163491478964011548779365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3102643943904030796744973 1163491478964011548779365)
                  ·
                    refine ⟨218154652305752165396131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1163491478964011548779365 218154652305752165396131)
                    ·
                      rfl

theorem cell23_1274564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_1274564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274564 prefixEnd_1274564 := by exact prefixLift 1274564
  have htrace : WordTrace (prefixWord ++ tailWord_1274564) baseStart_1274564 baseEnd_1274564 := by
    simpa [prefixWord, tailWord_1274564, baseEnd_1274564] using wordTrace_append hprefix tailTrace_1274564
  have hstable : (prefixWord ++ tailWord_1274564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274564).length < 2 ^ (prefixWord ++ tailWord_1274564).sum := by decide
  have hdescent : baseEnd_1274564 < baseStart_1274564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274621 : List Nat := [1, 4, 1, 1, 1, 1, 5, 4, 1, 1, 3]
def baseStart_1274621 : Nat := 118140960795 + 1274621 * 2 ^ 59
def prefixEnd_1274621 : Nat := 4983230072969 + 3 ^ 40 * 1274621 * 2
def baseEnd_1274621 : Nat := 654493225314562773175631

theorem tailTrace_1274621 : CollatzResearch.WordTrace tailWord_1274621 prefixEnd_1274621 654493225314562773175631 := by
  unfold tailWord_1274621
  simp only [CollatzResearch.WordTrace]
  refine ⟨46489247115273279780887717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30992831410182186520591811 46489247115273279780887717)
  ·
    refine ⟨8716733834113739958916447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46489247115273279780887717 8716733834113739958916447)
    ·
      refine ⟨13075100751170609938374671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8716733834113739958916447 13075100751170609938374671)
      ·
        refine ⟨19612651126755914907562007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13075100751170609938374671 19612651126755914907562007)
        ·
          refine ⟨29418976690133872361343011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19612651126755914907562007 29418976690133872361343011)
          ·
            refine ⟨44128465035200808542014517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29418976690133872361343011 44128465035200808542014517)
            ·
              refine ⟨4137043597050075800813861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44128465035200808542014517 4137043597050075800813861)
              ·
                refine ⟨775695674446889212652599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4137043597050075800813861 775695674446889212652599)
                ·
                  refine ⟨1163543511670333818978899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 775695674446889212652599 1163543511670333818978899)
                  ·
                    refine ⟨1745315267505500728468349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1163543511670333818978899 1745315267505500728468349)
                    ·
                      refine ⟨654493225314562773175631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1745315267505500728468349 654493225314562773175631)
                      ·
                        rfl

theorem cell23_1274621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_1274621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274621 prefixEnd_1274621 := by exact prefixLift 1274621
  have htrace : WordTrace (prefixWord ++ tailWord_1274621) baseStart_1274621 baseEnd_1274621 := by
    simpa [prefixWord, tailWord_1274621, baseEnd_1274621] using wordTrace_append hprefix tailTrace_1274621
  have hstable : (prefixWord ++ tailWord_1274621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274621).length < 2 ^ (prefixWord ++ tailWord_1274621).sum := by decide
  have hdescent : baseEnd_1274621 < baseStart_1274621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274627 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 2, 6, 2]
def baseStart_1274627 : Nat := 118140960795 + 1274627 * 2 ^ 59
def prefixEnd_1274627 : Nat := 4983230072969 + 3 ^ 40 * 1274627 * 2
def baseEnd_1274627 : Nat := 654496306198489749700603

theorem tailTrace_1274627 : CollatzResearch.WordTrace tailWord_1274627 prefixEnd_1274627 654496306198489749700603 := by
  unfold tailWord_1274627
  simp only [CollatzResearch.WordTrace]
  refine ⟨46489465953251542805606135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30992977302167695203737423 46489465953251542805606135)
  ·
    refine ⟨69734198929877314208409203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46489465953251542805606135 69734198929877314208409203)
    ·
      refine ⟨104601298394815971312613805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69734198929877314208409203 104601298394815971312613805)
      ·
        refine ⟨39225486898055989242230177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104601298394815971312613805 39225486898055989242230177)
        ·
          refine ⟨29419115173541991931672633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39225486898055989242230177 29419115173541991931672633)
          ·
            refine ⟨22064336380156493948754475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29419115173541991931672633 22064336380156493948754475)
            ·
              refine ⟨33096504570234740923131713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22064336380156493948754475 33096504570234740923131713)
              ·
                refine ⟨24822378427676055692348785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33096504570234740923131713 24822378427676055692348785)
                ·
                  refine ⟨18616783820757041769261589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24822378427676055692348785 18616783820757041769261589)
                  ·
                    refine ⟨872661741597986332934137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18616783820757041769261589 872661741597986332934137)
                    ·
                      refine ⟨654496306198489749700603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 872661741597986332934137 654496306198489749700603)
                      ·
                        rfl

theorem cell23_1274627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 6, 2].length) (baseStart_1274627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274627 prefixEnd_1274627 := by exact prefixLift 1274627
  have htrace : WordTrace (prefixWord ++ tailWord_1274627) baseStart_1274627 baseEnd_1274627 := by
    simpa [prefixWord, tailWord_1274627, baseEnd_1274627] using wordTrace_append hprefix tailTrace_1274627
  have hstable : (prefixWord ++ tailWord_1274627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274627).length < 2 ^ (prefixWord ++ tailWord_1274627).sum := by decide
  have hdescent : baseEnd_1274627 < baseStart_1274627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274657 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_1274657 : Nat := 118140960795 + 1274657 * 2 ^ 59
def prefixEnd_1274657 : Nat := 4983230072969 + 3 ^ 40 * 1274657 * 2
def baseEnd_1274657 : Nat := 654511710618124632325465

theorem tailTrace_1274657 : CollatzResearch.WordTrace tailWord_1274657 prefixEnd_1274657 654511710618124632325465 := by
  unfold tailWord_1274657
  simp only [CollatzResearch.WordTrace]
  refine ⟨46490560143142857929198225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30993706762095238619465483 46490560143142857929198225)
  ·
    refine ⟨34867920107357143446898669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46490560143142857929198225 34867920107357143446898669)
    ·
      refine ⟨13075470040258928792587001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34867920107357143446898669 13075470040258928792587001)
      ·
        refine ⟨9806602530194196594440251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13075470040258928792587001 9806602530194196594440251)
        ·
          refine ⟨14709903795291294891660377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9806602530194196594440251 14709903795291294891660377)
          ·
            refine ⟨11032427846468471168745283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14709903795291294891660377 11032427846468471168745283)
            ·
              refine ⟨16548641769702706753117925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11032427846468471168745283 16548641769702706753117925)
              ·
                refine ⟨3102870331819257516209611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16548641769702706753117925 3102870331819257516209611)
                ·
                  refine ⟨4654305497728886274314417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3102870331819257516209611 4654305497728886274314417)
                  ·
                    refine ⟨3490729123296664705735813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4654305497728886274314417 3490729123296664705735813)
                    ·
                      refine ⟨654511710618124632325465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3490729123296664705735813 654511710618124632325465)
                      ·
                        rfl

theorem cell23_1274657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_1274657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274657 prefixEnd_1274657 := by exact prefixLift 1274657
  have htrace : WordTrace (prefixWord ++ tailWord_1274657) baseStart_1274657 baseEnd_1274657 := by
    simpa [prefixWord, tailWord_1274657, baseEnd_1274657] using wordTrace_append hprefix tailTrace_1274657
  have hstable : (prefixWord ++ tailWord_1274657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274657).length < 2 ^ (prefixWord ++ tailWord_1274657).sum := by decide
  have hdescent : baseEnd_1274657 < baseStart_1274657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274704 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 3, 3, 2]
def baseStart_1274704 : Nat := 118140960795 + 1274704 * 2 ^ 59
def prefixEnd_1274704 : Nat := 4983230072969 + 3 ^ 40 * 1274704 * 2
def baseEnd_1274704 : Nat := 654535844208885948437749

theorem tailTrace_1274704 : CollatzResearch.WordTrace tailWord_1274704 prefixEnd_1274704 654535844208885948437749 := by
  unfold tailWord_1274704
  simp only [CollatzResearch.WordTrace]
  refine ⟨23246137186986292478079583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30994849582648389970772777 23246137186986292478079583)
  ·
    refine ⟨34869205780479438717119375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23246137186986292478079583 34869205780479438717119375)
    ·
      refine ⟨52303808670719158075679063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34869205780479438717119375 52303808670719158075679063)
      ·
        refine ⟨78455713006078737113518595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52303808670719158075679063 78455713006078737113518595)
        ·
          refine ⟨117683569509118105670277893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78455713006078737113518595 117683569509118105670277893)
          ·
            refine ⟨22065669282959644813177105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117683569509118105670277893 22065669282959644813177105)
            ·
              refine ⟨16549251962219733609882829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22065669282959644813177105 16549251962219733609882829)
              ·
                refine ⟨6205969485832400103706061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16549251962219733609882829 6205969485832400103706061)
                ·
                  refine ⟨2327238557187150038889773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6205969485832400103706061 2327238557187150038889773)
                  ·
                    refine ⟨872714458945181264583665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2327238557187150038889773 872714458945181264583665)
                    ·
                      refine ⟨654535844208885948437749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 872714458945181264583665 654535844208885948437749)
                      ·
                        rfl

theorem cell23_1274704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 3, 3, 2].length) (baseStart_1274704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274704 prefixEnd_1274704 := by exact prefixLift 1274704
  have htrace : WordTrace (prefixWord ++ tailWord_1274704) baseStart_1274704 baseEnd_1274704 := by
    simpa [prefixWord, tailWord_1274704, baseEnd_1274704] using wordTrace_append hprefix tailTrace_1274704
  have hstable : (prefixWord ++ tailWord_1274704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274704).length < 2 ^ (prefixWord ++ tailWord_1274704).sum := by decide
  have hdescent : baseEnd_1274704 < baseStart_1274704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274747 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 4]
def baseStart_1274747 : Nat := 118140960795 + 1274747 * 2 ^ 59
def prefixEnd_1274747 : Nat := 4983230072969 + 3 ^ 40 * 1274747 * 2
def baseEnd_1274747 : Nat := 654557923877029280200051

theorem tailTrace_1274747 : CollatzResearch.WordTrace tailWord_1274747 prefixEnd_1274747 654557923877029280200051 := by
  unfold tailWord_1274747
  simp only [CollatzResearch.WordTrace]
  refine ⟨46493842712816803299974495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30995895141877868866649663 46493842712816803299974495)
  ·
    refine ⟨69740764069225204949961743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46493842712816803299974495 69740764069225204949961743)
    ·
      refine ⟨104611146103837807424942615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69740764069225204949961743 104611146103837807424942615)
      ·
        refine ⟨156916719155756711137413923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104611146103837807424942615 156916719155756711137413923)
        ·
          refine ⟨235375078733635066706120885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156916719155756711137413923 235375078733635066706120885)
          ·
            refine ⟨22066413631278287503698833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 235375078733635066706120885 22066413631278287503698833)
            ·
              refine ⟨16549810223458715627774125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22066413631278287503698833 16549810223458715627774125)
              ·
                refine ⟨6206178833797018360415297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16549810223458715627774125 6206178833797018360415297)
                ·
                  refine ⟨4654634125347763770311473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6206178833797018360415297 4654634125347763770311473)
                  ·
                    refine ⟨3490975594010822827733605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4654634125347763770311473 3490975594010822827733605)
                    ·
                      refine ⟨654557923877029280200051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3490975594010822827733605 654557923877029280200051)
                      ·
                        rfl

theorem cell23_1274747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 4].length) (baseStart_1274747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274747 prefixEnd_1274747 := by exact prefixLift 1274747
  have htrace : WordTrace (prefixWord ++ tailWord_1274747) baseStart_1274747 baseEnd_1274747 := by
    simpa [prefixWord, tailWord_1274747, baseEnd_1274747] using wordTrace_append hprefix tailTrace_1274747
  have hstable : (prefixWord ++ tailWord_1274747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274747).length < 2 ^ (prefixWord ++ tailWord_1274747).sum := by decide
  have hdescent : baseEnd_1274747 < baseStart_1274747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274785 : List Nat := [1, 2, 3, 4, 1, 2, 2, 2, 2, 2, 2]
def baseStart_1274785 : Nat := 118140960795 + 1274785 * 2 ^ 59
def prefixEnd_1274785 : Nat := 4983230072969 + 3 ^ 40 * 1274785 * 2
def baseEnd_1274785 : Nat := 654577436141900131524877

theorem tailTrace_1274785 : CollatzResearch.WordTrace tailWord_1274785 prefixEnd_1274785 654577436141900131524877 := by
  unfold tailWord_1274785
  simp only [CollatzResearch.WordTrace]
  refine ⟨46495228686679135789857809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30996819124452757193238539 46495228686679135789857809)
  ·
    refine ⟨34871421515009351842393357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46495228686679135789857809 34871421515009351842393357)
    ·
      refine ⟨13076783068128506940897509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34871421515009351842393357 13076783068128506940897509)
      ·
        refine ⟨2451896825274095051418283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13076783068128506940897509 2451896825274095051418283)
        ·
          refine ⟨3677845237911142577127425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451896825274095051418283 3677845237911142577127425)
          ·
            refine ⟨2758383928433356932845569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3677845237911142577127425 2758383928433356932845569)
            ·
              refine ⟨2068787946325017699634177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2758383928433356932845569 2068787946325017699634177)
              ·
                refine ⟨1551590959743763274725633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2068787946325017699634177 1551590959743763274725633)
                ·
                  refine ⟨1163693219807822456044225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1551590959743763274725633 1163693219807822456044225)
                  ·
                    refine ⟨872769914855866842033169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1163693219807822456044225 872769914855866842033169)
                    ·
                      refine ⟨654577436141900131524877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 872769914855866842033169 654577436141900131524877)
                      ·
                        rfl

theorem cell23_1274785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_1274785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274785 prefixEnd_1274785 := by exact prefixLift 1274785
  have htrace : WordTrace (prefixWord ++ tailWord_1274785) baseStart_1274785 baseEnd_1274785 := by
    simpa [prefixWord, tailWord_1274785, baseEnd_1274785] using wordTrace_append hprefix tailTrace_1274785
  have hstable : (prefixWord ++ tailWord_1274785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274785).length < 2 ^ (prefixWord ++ tailWord_1274785).sum := by decide
  have hdescent : baseEnd_1274785 < baseStart_1274785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274801 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 2, 3, 3]
def baseStart_1274801 : Nat := 118140960795 + 1274801 * 2 ^ 59
def prefixEnd_1274801 : Nat := 4983230072969 + 3 ^ 40 * 1274801 * 2
def baseEnd_1274801 : Nat := 654585651832372068924803

theorem tailTrace_1274801 : CollatzResearch.WordTrace tailWord_1274801 prefixEnd_1274801 654585651832372068924803 := by
  unfold tailWord_1274801
  simp only [CollatzResearch.WordTrace]
  refine ⟨46495812254621170522440257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30997208169747447014960171 46495812254621170522440257)
  ·
    refine ⟨34871859190965877891830193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46495812254621170522440257 34871859190965877891830193)
    ·
      refine ⟨26153894393224408418872645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34871859190965877891830193 26153894393224408418872645)
      ·
        refine ⟨4903855198729576578538621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26153894393224408418872645 4903855198729576578538621)
        ·
          refine ⟨1838945699523591216951983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4903855198729576578538621 1838945699523591216951983)
          ·
            refine ⟨2758418549285386825427975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838945699523591216951983 2758418549285386825427975)
            ·
              refine ⟨4137627823928080238141963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758418549285386825427975 4137627823928080238141963)
              ·
                refine ⟨6206441735892120357212945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4137627823928080238141963 6206441735892120357212945)
                ·
                  refine ⟨4654831301919090267909709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6206441735892120357212945 4654831301919090267909709)
                  ·
                    refine ⟨1745561738219658850466141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4654831301919090267909709 1745561738219658850466141)
                    ·
                      refine ⟨654585651832372068924803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1745561738219658850466141 654585651832372068924803)
                      ·
                        rfl

theorem cell23_1274801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_1274801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274801 prefixEnd_1274801 := by exact prefixLift 1274801
  have htrace : WordTrace (prefixWord ++ tailWord_1274801) baseStart_1274801 baseEnd_1274801 := by
    simpa [prefixWord, tailWord_1274801, baseEnd_1274801] using wordTrace_append hprefix tailTrace_1274801
  have hstable : (prefixWord ++ tailWord_1274801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274801).length < 2 ^ (prefixWord ++ tailWord_1274801).sum := by decide
  have hdescent : baseEnd_1274801 < baseStart_1274801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274841 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 2, 4, 2]
def baseStart_1274841 : Nat := 118140960795 + 1274841 * 2 ^ 59
def prefixEnd_1274841 : Nat := 4983230072969 + 3 ^ 40 * 1274841 * 2
def baseEnd_1274841 : Nat := 654606191058551912424619

theorem tailTrace_1274841 : CollatzResearch.WordTrace tailWord_1274841 prefixEnd_1274841 654606191058551912424619 := by
  unfold tailWord_1274841
  simp only [CollatzResearch.WordTrace]
  refine ⟨46497271174476257353896377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30998180782984171569264251 46497271174476257353896377)
  ·
    refine ⟨34872953380857193015422283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46497271174476257353896377 34872953380857193015422283)
    ·
      refine ⟨52309430071285789523133425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34872953380857193015422283 52309430071285789523133425)
      ·
        refine ⟨39232072553464342142350069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52309430071285789523133425 39232072553464342142350069)
        ·
          refine ⟨3678006801887282075845319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39232072553464342142350069 3678006801887282075845319)
          ·
            refine ⟨5517010202830923113767979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3678006801887282075845319 5517010202830923113767979)
            ·
              refine ⟨8275515304246384670651969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5517010202830923113767979 8275515304246384670651969)
              ·
                refine ⟨6206636478184788502988977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8275515304246384670651969 6206636478184788502988977)
                ·
                  refine ⟨4654977358638591377241733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6206636478184788502988977 4654977358638591377241733)
                  ·
                    refine ⟨872808254744735883232825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4654977358638591377241733 872808254744735883232825)
                    ·
                      refine ⟨654606191058551912424619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 872808254744735883232825 654606191058551912424619)
                      ·
                        rfl

theorem cell23_1274841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 4, 2].length) (baseStart_1274841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274841 prefixEnd_1274841 := by exact prefixLift 1274841
  have htrace : WordTrace (prefixWord ++ tailWord_1274841) baseStart_1274841 baseEnd_1274841 := by
    simpa [prefixWord, tailWord_1274841, baseEnd_1274841] using wordTrace_append hprefix tailTrace_1274841
  have hstable : (prefixWord ++ tailWord_1274841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274841).length < 2 ^ (prefixWord ++ tailWord_1274841).sum := by decide
  have hdescent : baseEnd_1274841 < baseStart_1274841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274851 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 3, 4]
def baseStart_1274851 : Nat := 118140960795 + 1274851 * 2 ^ 59
def prefixEnd_1274851 : Nat := 4983230072969 + 3 ^ 40 * 1274851 * 2
def baseEnd_1274851 : Nat := 218203775288365624433191

theorem tailTrace_1274851 : CollatzResearch.WordTrace tailWord_1274851 prefixEnd_1274851 218203775288365624433191 := by
  unfold tailWord_1274851
  simp only [CollatzResearch.WordTrace]
  refine ⟨46497635904440029061760407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30998423936293352707840271 46497635904440029061760407)
  ·
    refine ⟨69746453856660043592640611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46497635904440029061760407 69746453856660043592640611)
    ·
      refine ⟨104619680784990065388960917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69746453856660043592640611 104619680784990065388960917)
      ·
        refine ⟨4904047536796409315107543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104619680784990065388960917 4904047536796409315107543)
        ·
          refine ⟨7356071305194613972661315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4904047536796409315107543 7356071305194613972661315)
          ·
            refine ⟨11034106957791920958991973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7356071305194613972661315 11034106957791920958991973)
            ·
              refine ⟨2068895054585985179810995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11034106957791920958991973 2068895054585985179810995)
              ·
                refine ⟨3103342581878977769716493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068895054585985179810995 3103342581878977769716493)
                ·
                  refine ⟨1163753468204616663643685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3103342581878977769716493 1163753468204616663643685)
                  ·
                    refine ⟨218203775288365624433191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1163753468204616663643685 218203775288365624433191)
                    ·
                      rfl

theorem cell23_1274851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 4].length) (baseStart_1274851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274851 prefixEnd_1274851 := by exact prefixLift 1274851
  have htrace : WordTrace (prefixWord ++ tailWord_1274851) baseStart_1274851 baseEnd_1274851 := by
    simpa [prefixWord, tailWord_1274851, baseEnd_1274851] using wordTrace_append hprefix tailTrace_1274851
  have hstable : (prefixWord ++ tailWord_1274851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274851).length < 2 ^ (prefixWord ++ tailWord_1274851).sum := by decide
  have hdescent : baseEnd_1274851 < baseStart_1274851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274924 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 1, 6]
def baseStart_1274924 : Nat := 118140960795 + 1274924 * 2 ^ 59
def prefixEnd_1274924 : Nat := 4983230072969 + 3 ^ 40 * 1274924 * 2
def baseEnd_1274924 : Nat := 218216269984291695895579

theorem tailTrace_1274924 : CollatzResearch.WordTrace tailWord_1274924 prefixEnd_1274924 218216269984291695895579 := by
  unfold tailWord_1274924
  simp only [CollatzResearch.WordTrace]
  refine ⟨23250149216587781264583913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31000198955450375019445217 23250149216587781264583913)
  ·
    refine ⟨17437611912440835948437935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23250149216587781264583913 17437611912440835948437935)
    ·
      refine ⟨26156417868661253922656903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17437611912440835948437935 26156417868661253922656903)
      ·
        refine ⟨39234626802991880883985355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26156417868661253922656903 39234626802991880883985355)
        ·
          refine ⟨58851940204487821325978033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39234626802991880883985355 58851940204487821325978033)
          ·
            refine ⟨44138955153365865994483525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58851940204487821325978033 44138955153365865994483525)
            ·
              refine ⟨8276054091256099873965661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44138955153365865994483525 8276054091256099873965661)
              ·
                refine ⟨3103520284221037452737123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8276054091256099873965661 3103520284221037452737123)
                ·
                  refine ⟨4655280426331556179105685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3103520284221037452737123 4655280426331556179105685)
                  ·
                    refine ⟨218216269984291695895579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4655280426331556179105685 218216269984291695895579)
                    ·
                      rfl

theorem cell23_1274924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_1274924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274924 prefixEnd_1274924 := by exact prefixLift 1274924
  have htrace : WordTrace (prefixWord ++ tailWord_1274924) baseStart_1274924 baseEnd_1274924 := by
    simpa [prefixWord, tailWord_1274924, baseEnd_1274924] using wordTrace_append hprefix tailTrace_1274924
  have hstable : (prefixWord ++ tailWord_1274924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274924).length < 2 ^ (prefixWord ++ tailWord_1274924).sum := by decide
  have hdescent : baseEnd_1274924 < baseStart_1274924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274941 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_1274941 : Nat := 118140960795 + 1274941 * 2 ^ 59
def prefixEnd_1274941 : Nat := 4983230072969 + 3 ^ 40 * 1274941 * 2
def baseEnd_1274941 : Nat := 218219179708000507058053

theorem tailTrace_1274941 : CollatzResearch.WordTrace tailWord_1274941 prefixEnd_1274941 218219179708000507058053 := by
  unfold tailWord_1274941
  simp only [CollatzResearch.WordTrace]
  refine ⟨46500918474113974432536677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31000612316075982955024451 46500918474113974432536677)
  ·
    refine ⟨8718922213896370206100627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46500918474113974432536677 8718922213896370206100627)
    ·
      refine ⟨13078383320844555309150941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8718922213896370206100627 13078383320844555309150941)
      ·
        refine ⟨4904393745316708240931603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13078383320844555309150941 4904393745316708240931603)
        ·
          refine ⟨7356590617975062361397405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4904393745316708240931603 7356590617975062361397405)
          ·
            refine ⟨2758721481740648385524027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7356590617975062361397405 2758721481740648385524027)
            ·
              refine ⟨4138082222610972578286041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758721481740648385524027 4138082222610972578286041)
              ·
                refine ⟨3103561666958229433714531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4138082222610972578286041 3103561666958229433714531)
                ·
                  refine ⟨4655342500437344150571797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3103561666958229433714531 4655342500437344150571797)
                  ·
                    refine ⟨218219179708000507058053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4655342500437344150571797 218219179708000507058053)
                    ·
                      rfl

theorem cell23_1274941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_1274941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274941 prefixEnd_1274941 := by exact prefixLift 1274941
  have htrace : WordTrace (prefixWord ++ tailWord_1274941) baseStart_1274941 baseEnd_1274941 := by
    simpa [prefixWord, tailWord_1274941, baseEnd_1274941] using wordTrace_append hprefix tailTrace_1274941
  have hstable : (prefixWord ++ tailWord_1274941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274941).length < 2 ^ (prefixWord ++ tailWord_1274941).sum := by decide
  have hdescent : baseEnd_1274941 < baseStart_1274941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274945 : List Nat := [1, 2, 5, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1274945 : Nat := 118140960795 + 1274945 * 2 ^ 59
def prefixEnd_1274945 : Nat := 4983230072969 + 3 ^ 40 * 1274945 * 2
def baseEnd_1274945 : Nat := 218219864348873168508047

theorem tailTrace_1274945 : CollatzResearch.WordTrace tailWord_1274945 prefixEnd_1274945 218219864348873168508047 := by
  unfold tailWord_1274945
  simp only [CollatzResearch.WordTrace]
  refine ⟨46501064366099483115682289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31000709577399655410454859 46501064366099483115682289)
  ·
    refine ⟨34875798274574612336761717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46501064366099483115682289 34875798274574612336761717)
    ·
      refine ⟨3269606088241369906571411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34875798274574612336761717 3269606088241369906571411)
      ·
        refine ⟨4904409132362054859857117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3269606088241369906571411 4904409132362054859857117)
        ·
          refine ⟨1839153424635770572446419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4904409132362054859857117 1839153424635770572446419)
          ·
            refine ⟨2758730136953655858669629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1839153424635770572446419 2758730136953655858669629)
            ·
              refine ⟨1034523801357620947001111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2758730136953655858669629 1034523801357620947001111)
              ·
                refine ⟨1551785702036431420501667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034523801357620947001111 1551785702036431420501667)
                ·
                  refine ⟨2327678553054647130752501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1551785702036431420501667 2327678553054647130752501)
                  ·
                    refine ⟨218219864348873168508047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2327678553054647130752501 218219864348873168508047)
                    ·
                      rfl

theorem cell23_1274945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1274945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274945 prefixEnd_1274945 := by exact prefixLift 1274945
  have htrace : WordTrace (prefixWord ++ tailWord_1274945) baseStart_1274945 baseEnd_1274945 := by
    simpa [prefixWord, tailWord_1274945, baseEnd_1274945] using wordTrace_append hprefix tailTrace_1274945
  have hstable : (prefixWord ++ tailWord_1274945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274945).length < 2 ^ (prefixWord ++ tailWord_1274945).sum := by decide
  have hdescent : baseEnd_1274945 < baseStart_1274945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274951 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_1274951 : Nat := 118140960795 + 1274951 * 2 ^ 59
def prefixEnd_1274951 : Nat := 4983230072969 + 3 ^ 40 * 1274951 * 2
def baseEnd_1274951 : Nat := 654662673930546482049113

theorem tailTrace_1274951 : CollatzResearch.WordTrace tailWord_1274951 prefixEnd_1274951 654662673930546482049113 := by
  unfold tailWord_1274951
  simp only [CollatzResearch.WordTrace]
  refine ⟨46501283204077746140400707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31000855469385164093600471 46501283204077746140400707)
  ·
    refine ⟨69751924806116619210601061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46501283204077746140400707 69751924806116619210601061)
    ·
      refine ⟨13078485901146866101987699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69751924806116619210601061 13078485901146866101987699)
      ·
        refine ⟨19617728851720299152981549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13078485901146866101987699 19617728851720299152981549)
        ·
          refine ⟨7356648319395112182368081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19617728851720299152981549 7356648319395112182368081)
          ·
            refine ⟨5517486239546334136776061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7356648319395112182368081 5517486239546334136776061)
            ·
              refine ⟨2069057339829875301291023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5517486239546334136776061 2069057339829875301291023)
              ·
                refine ⟨3103586009744812951936535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069057339829875301291023 3103586009744812951936535)
                ·
                  refine ⟨4655379014617219427904803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3103586009744812951936535 4655379014617219427904803)
                  ·
                    refine ⟨6983068521925829141857205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4655379014617219427904803 6983068521925829141857205)
                    ·
                      refine ⟨654662673930546482049113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6983068521925829141857205 654662673930546482049113)
                      ·
                        rfl

theorem cell23_1274951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_1274951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274951 prefixEnd_1274951 := by exact prefixLift 1274951
  have htrace : WordTrace (prefixWord ++ tailWord_1274951) baseStart_1274951 baseEnd_1274951 := by
    simpa [prefixWord, tailWord_1274951, baseEnd_1274951] using wordTrace_append hprefix tailTrace_1274951
  have hstable : (prefixWord ++ tailWord_1274951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274951).length < 2 ^ (prefixWord ++ tailWord_1274951).sum := by decide
  have hdescent : baseEnd_1274951 < baseStart_1274951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274958 : List Nat := [4, 1, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_1274958 : Nat := 118140960795 + 1274958 * 2 ^ 59
def prefixEnd_1274958 : Nat := 4983230072969 + 3 ^ 40 * 1274958 * 2
def baseEnd_1274958 : Nat := 218222089431709318220527

theorem tailTrace_1274958 : CollatzResearch.WordTrace tailWord_1274958 prefixEnd_1274958 218222089431709318220527 := by
  unfold tailWord_1274958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5812692314381548291988191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31001025676701590890603685 5812692314381548291988191)
  ·
    refine ⟨8719038471572322437982287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5812692314381548291988191 8719038471572322437982287)
    ·
      refine ⟨13078557707358483656973431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8719038471572322437982287 13078557707358483656973431)
      ·
        refine ⟨19617836561037725485460147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13078557707358483656973431 19617836561037725485460147)
        ·
          refine ⟨29426754841556588228190221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19617836561037725485460147 29426754841556588228190221)
          ·
            refine ⟨11035033065583720585571333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29426754841556588228190221 11035033065583720585571333)
            ·
              refine ⟨2069068699796947609794625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11035033065583720585571333 2069068699796947609794625)
              ·
                refine ⟨1551801524847710707345969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2069068699796947609794625 1551801524847710707345969)
                ·
                  refine ⟨1163851143635783030509477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1551801524847710707345969 1163851143635783030509477)
                  ·
                    refine ⟨218222089431709318220527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1163851143635783030509477 218222089431709318220527)
                    ·
                      rfl

theorem cell23_1274958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_1274958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274958 prefixEnd_1274958 := by exact prefixLift 1274958
  have htrace : WordTrace (prefixWord ++ tailWord_1274958) baseStart_1274958 baseEnd_1274958 := by
    simpa [prefixWord, tailWord_1274958, baseEnd_1274958] using wordTrace_append hprefix tailTrace_1274958
  have hstable : (prefixWord ++ tailWord_1274958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274958).length < 2 ^ (prefixWord ++ tailWord_1274958).sum := by decide
  have hdescent : baseEnd_1274958 < baseStart_1274958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274978 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1274978 : Nat := 118140960795 + 1274978 * 2 ^ 59
def prefixEnd_1274978 : Nat := 4983230072969 + 3 ^ 40 * 1274978 * 2
def baseEnd_1274978 : Nat := 654676537908217876411489

theorem tailTrace_1274978 : CollatzResearch.WordTrace tailWord_1274978 prefixEnd_1274978 654676537908217876411489 := by
  unfold tailWord_1274978
  simp only [CollatzResearch.WordTrace]
  refine ⟨11625566993744982437908397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31001511983319953167755725 11625566993744982437908397)
  ·
    refine ⟨4359587622654368414215649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11625566993744982437908397 4359587622654368414215649)
    ·
      refine ⟨3269690716990776310661737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4359587622654368414215649 3269690716990776310661737)
      ·
        refine ⟨2452268037743082232996303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3269690716990776310661737 2452268037743082232996303)
        ·
          refine ⟨3678402056614623349494455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2452268037743082232996303 3678402056614623349494455)
          ·
            refine ⟨5517603084921935024241683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3678402056614623349494455 5517603084921935024241683)
            ·
              refine ⟨8276404627382902536362525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5517603084921935024241683 8276404627382902536362525)
              ·
                refine ⟨3103651735268588451135947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8276404627382902536362525 3103651735268588451135947)
                ·
                  refine ⟨4655477602902882676703921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3103651735268588451135947 4655477602902882676703921)
                  ·
                    refine ⟨3491608202177162007527941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4655477602902882676703921 3491608202177162007527941)
                    ·
                      refine ⟨654676537908217876411489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3491608202177162007527941 654676537908217876411489)
                      ·
                        rfl

theorem cell23_1274978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1274978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274978 prefixEnd_1274978 := by exact prefixLift 1274978
  have htrace : WordTrace (prefixWord ++ tailWord_1274978) baseStart_1274978 baseEnd_1274978 := by
    simpa [prefixWord, tailWord_1274978, baseEnd_1274978] using wordTrace_append hprefix tailTrace_1274978
  have hstable : (prefixWord ++ tailWord_1274978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274978).length < 2 ^ (prefixWord ++ tailWord_1274978).sum := by decide
  have hdescent : baseEnd_1274978 < baseStart_1274978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274998 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1274998 : Nat := 118140960795 + 1274998 * 2 ^ 59
def prefixEnd_1274998 : Nat := 4983230072969 + 3 ^ 40 * 1274998 * 2
def baseEnd_1274998 : Nat := 654686807521307798161397

theorem tailTrace_1274998 : CollatzResearch.WordTrace tailWord_1274998 prefixEnd_1274998 654686807521307798161397 := by
  unfold tailWord_1274998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2906437339681717072960103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31001998289938315444907765 2906437339681717072960103)
  ·
    refine ⟨4359656009522575609440155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2906437339681717072960103 4359656009522575609440155)
    ·
      refine ⟨6539484014283863414160233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4359656009522575609440155 6539484014283863414160233)
      ·
        refine ⟨4904613010712897560620175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6539484014283863414160233 4904613010712897560620175)
        ·
          refine ⟨7356919516069346340930263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4904613010712897560620175 7356919516069346340930263)
          ·
            refine ⟨11035379274104019511395395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7356919516069346340930263 11035379274104019511395395)
            ·
              refine ⟨16553068911156029267093093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11035379274104019511395395 16553068911156029267093093)
              ·
                refine ⟨3103700420841755487579955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16553068911156029267093093 3103700420841755487579955)
                ·
                  refine ⟨4655550631262633231369933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3103700420841755487579955 4655550631262633231369933)
                  ·
                    refine ⟨1745831486723487461763725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4655550631262633231369933 1745831486723487461763725)
                    ·
                      refine ⟨654686807521307798161397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1745831486723487461763725 654686807521307798161397)
                      ·
                        rfl

theorem cell23_1274998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1274998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1274998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1274998 prefixEnd_1274998 := by exact prefixLift 1274998
  have htrace : WordTrace (prefixWord ++ tailWord_1274998) baseStart_1274998 baseEnd_1274998 := by
    simpa [prefixWord, tailWord_1274998, baseEnd_1274998] using wordTrace_append hprefix tailTrace_1274998
  have hstable : (prefixWord ++ tailWord_1274998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274998).length < 2 ^ (prefixWord ++ tailWord_1274998).sum := by decide
  have hdescent : baseEnd_1274998 < baseStart_1274998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275024 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 5]
def baseStart_1275024 : Nat := 118140960795 + 1275024 * 2 ^ 59
def prefixEnd_1275024 : Nat := 4983230072969 + 3 ^ 40 * 1275024 * 2
def baseEnd_1275024 : Nat := 654700158018324696436277

theorem tailTrace_1275024 : CollatzResearch.WordTrace tailWord_1275024 prefixEnd_1275024 654700158018324696436277 := by
  unfold tailWord_1275024
  simp only [CollatzResearch.WordTrace]
  refine ⟨23251972866406639803904063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31002630488542186405205417 23251972866406639803904063)
  ·
    refine ⟨34877959299609959705856095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23251972866406639803904063 34877959299609959705856095)
    ·
      refine ⟨52316938949414939558784143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34877959299609959705856095 52316938949414939558784143)
      ·
        refine ⟨78475408424122409338176215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52316938949414939558784143 78475408424122409338176215)
        ·
          refine ⟨117713112636183614007264323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78475408424122409338176215 117713112636183614007264323)
          ·
            refine ⟨176569668954275421010896485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117713112636183614007264323 176569668954275421010896485)
            ·
              refine ⟨33106812928926641439543091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176569668954275421010896485 33106812928926641439543091)
              ·
                refine ⟨49660219393389962159314637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33106812928926641439543091 49660219393389962159314637)
                ·
                  refine ⟨18622582272521235809742989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49660219393389962159314637 18622582272521235809742989)
                  ·
                    refine ⟨6983468352195463428653621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18622582272521235809742989 6983468352195463428653621)
                    ·
                      refine ⟨654700158018324696436277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6983468352195463428653621 654700158018324696436277)
                      ·
                        rfl

theorem cell23_1275024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_1275024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275024 prefixEnd_1275024 := by exact prefixLift 1275024
  have htrace : WordTrace (prefixWord ++ tailWord_1275024) baseStart_1275024 baseEnd_1275024 := by
    simpa [prefixWord, tailWord_1275024, baseEnd_1275024] using wordTrace_append hprefix tailTrace_1275024
  have hstable : (prefixWord ++ tailWord_1275024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275024).length < 2 ^ (prefixWord ++ tailWord_1275024).sum := by decide
  have hdescent : baseEnd_1275024 < baseStart_1275024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275031 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 2, 6]
def baseStart_1275031 : Nat := 118140960795 + 1275031 * 2 ^ 59
def prefixEnd_1275031 : Nat := 4983230072969 + 3 ^ 40 * 1275031 * 2
def baseEnd_1275031 : Nat := 218234584127635389682915

theorem tailTrace_1275031 : CollatzResearch.WordTrace tailWord_1275031 prefixEnd_1275031 218234584127635389682915 := by
  unfold tailWord_1275031
  simp only [CollatzResearch.WordTrace]
  refine ⟨46504201043787919803312947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31002800695858613202208631 46504201043787919803312947)
  ·
    refine ⟨69756301565681879704969421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46504201043787919803312947 69756301565681879704969421)
    ·
      refine ⟨26158613087130704889363533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69756301565681879704969421 26158613087130704889363533)
      ·
        refine ⟨9809479907674014333511325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26158613087130704889363533 9809479907674014333511325)
        ·
          refine ⟨3678554965377755375066747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9809479907674014333511325 3678554965377755375066747)
          ·
            refine ⟨5517832448066633062600121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3678554965377755375066747 5517832448066633062600121)
            ·
              refine ⟨4138374336049974796950091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5517832448066633062600121 4138374336049974796950091)
              ·
                refine ⟨6207561504074962195425137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4138374336049974796950091 6207561504074962195425137)
                ·
                  refine ⟨4655671128056221646568853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6207561504074962195425137 4655671128056221646568853)
                  ·
                    refine ⟨218234584127635389682915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4655671128056221646568853 218234584127635389682915)
                    ·
                      rfl

theorem cell23_1275031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_1275031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275031 prefixEnd_1275031 := by exact prefixLift 1275031
  have htrace : WordTrace (prefixWord ++ tailWord_1275031) baseStart_1275031 baseEnd_1275031 := by
    simpa [prefixWord, tailWord_1275031, baseEnd_1275031] using wordTrace_append hprefix tailTrace_1275031
  have hstable : (prefixWord ++ tailWord_1275031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275031).length < 2 ^ (prefixWord ++ tailWord_1275031).sum := by decide
  have hdescent : baseEnd_1275031 < baseStart_1275031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275032 : List Nat := [2, 1, 2, 4, 2, 2, 3, 1, 2, 1, 3]
def baseStart_1275032 : Nat := 118140960795 + 1275032 * 2 ^ 59
def prefixEnd_1275032 : Nat := 4983230072969 + 3 ^ 40 * 1275032 * 2
def baseEnd_1275032 : Nat := 654704265863560665136241

theorem tailTrace_1275032 : CollatzResearch.WordTrace tailWord_1275032 prefixEnd_1275032 654704265863560665136241 := by
  unfold tailWord_1275032
  simp only [CollatzResearch.WordTrace]
  refine ⟨23252118758392148487049675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31002825011189531316066233 23252118758392148487049675)
  ·
    refine ⟨34878178137588222730574513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23252118758392148487049675 34878178137588222730574513)
    ·
      refine ⟨26158633603191167047930885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34878178137588222730574513 26158633603191167047930885)
      ·
        refine ⟨4904743800598343821487041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26158633603191167047930885 4904743800598343821487041)
        ·
          refine ⟨3678557850448757866115281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4904743800598343821487041 3678557850448757866115281)
          ·
            refine ⟨2758918387836568399586461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3678557850448757866115281 2758918387836568399586461)
            ·
              refine ⟨1034594395438713149844923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2758918387836568399586461 1034594395438713149844923)
              ·
                refine ⟨1551891593158069724767385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034594395438713149844923 1551891593158069724767385)
                ·
                  refine ⟨1163918694868552293575539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1551891593158069724767385 1163918694868552293575539)
                  ·
                    refine ⟨1745878042302828440363309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1163918694868552293575539 1745878042302828440363309)
                    ·
                      refine ⟨654704265863560665136241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1745878042302828440363309 654704265863560665136241)
                      ·
                        rfl

theorem cell23_1275032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_1275032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275032 prefixEnd_1275032 := by exact prefixLift 1275032
  have htrace : WordTrace (prefixWord ++ tailWord_1275032) baseStart_1275032 baseEnd_1275032 := by
    simpa [prefixWord, tailWord_1275032, baseEnd_1275032] using wordTrace_append hprefix tailTrace_1275032
  have hstable : (prefixWord ++ tailWord_1275032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275032).length < 2 ^ (prefixWord ++ tailWord_1275032).sum := by decide
  have hdescent : baseEnd_1275032 < baseStart_1275032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275041 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1275041 : Nat := 118140960795 + 1275041 * 2 ^ 59
def prefixEnd_1275041 : Nat := 4983230072969 + 3 ^ 40 * 1275041 * 2
def baseEnd_1275041 : Nat := 654708887189451129923699

theorem tailTrace_1275041 : CollatzResearch.WordTrace tailWord_1275041 prefixEnd_1275041 654708887189451129923699 := by
  unfold tailWord_1275041
  simp only [CollatzResearch.WordTrace]
  refine ⟨46504565773751691511176977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31003043849167794340784651 46504565773751691511176977)
  ·
    refine ⟨34878424330313768633382733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46504565773751691511176977 34878424330313768633382733)
    ·
      refine ⟨13079409123867663237518525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34878424330313768633382733 13079409123867663237518525)
      ·
        refine ⟨4904778421450373714069447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13079409123867663237518525 4904778421450373714069447)
        ·
          refine ⟨7357167632175560571104171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4904778421450373714069447 7357167632175560571104171)
          ·
            refine ⟨11035751448263340856656257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7357167632175560571104171 11035751448263340856656257)
            ·
              refine ⟨8276813586197505642492193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11035751448263340856656257 8276813586197505642492193)
              ·
                refine ⟨6207610189648129231869145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8276813586197505642492193 6207610189648129231869145)
                ·
                  refine ⟨4655707642236096923901859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6207610189648129231869145 4655707642236096923901859)
                  ·
                    refine ⟨6983561463354145385852789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4655707642236096923901859 6983561463354145385852789)
                    ·
                      refine ⟨654708887189451129923699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6983561463354145385852789 654708887189451129923699)
                      ·
                        rfl

theorem cell23_1275041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1275041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275041 prefixEnd_1275041 := by exact prefixLift 1275041
  have htrace : WordTrace (prefixWord ++ tailWord_1275041) baseStart_1275041 baseEnd_1275041 := by
    simpa [prefixWord, tailWord_1275041, baseEnd_1275041] using wordTrace_append hprefix tailTrace_1275041
  have hstable : (prefixWord ++ tailWord_1275041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275041).length < 2 ^ (prefixWord ++ tailWord_1275041).sum := by decide
  have hdescent : baseEnd_1275041 < baseStart_1275041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275071 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 3]
def baseStart_1275071 : Nat := 118140960795 + 1275071 * 2 ^ 59
def prefixEnd_1275071 : Nat := 4983230072969 + 3 ^ 40 * 1275071 * 2
def baseEnd_1275071 : Nat := 654724291609086012548561

theorem tailTrace_1275071 : CollatzResearch.WordTrace tailWord_1275071 prefixEnd_1275071 654724291609086012548561 := by
  unfold tailWord_1275071
  simp only [CollatzResearch.WordTrace]
  refine ⟨46505659963643006634769067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31003773309095337756512711 46505659963643006634769067)
  ·
    refine ⟨69758489945464509952153601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46505659963643006634769067 69758489945464509952153601)
    ·
      refine ⟨52318867459098382464115201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69758489945464509952153601 52318867459098382464115201)
      ·
        refine ⟨39239150594323786848086401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52318867459098382464115201 39239150594323786848086401)
        ·
          refine ⟨29429362945742840136064801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39239150594323786848086401 29429362945742840136064801)
          ·
            refine ⟨22072022209307130102048601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29429362945742840136064801 22072022209307130102048601)
            ·
              refine ⟨16554016656980347576536451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22072022209307130102048601 16554016656980347576536451)
              ·
                refine ⟨24831024985470521364804677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16554016656980347576536451 24831024985470521364804677)
                ·
                  refine ⟨4655817184775722755900877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24831024985470521364804677 4655817184775722755900877)
                  ·
                    refine ⟨1745931444290896033462829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4655817184775722755900877 1745931444290896033462829)
                    ·
                      refine ⟨654724291609086012548561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1745931444290896033462829 654724291609086012548561)
                      ·
                        rfl

theorem cell23_1275071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_1275071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275071 prefixEnd_1275071 := by exact prefixLift 1275071
  have htrace : WordTrace (prefixWord ++ tailWord_1275071) baseStart_1275071 baseEnd_1275071 := by
    simpa [prefixWord, tailWord_1275071, baseEnd_1275071] using wordTrace_append hprefix tailTrace_1275071
  have hstable : (prefixWord ++ tailWord_1275071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275071).length < 2 ^ (prefixWord ++ tailWord_1275071).sum := by decide
  have hdescent : baseEnd_1275071 < baseStart_1275071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275165 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1275165 : Nat := 118140960795 + 1275165 * 2 ^ 59
def prefixEnd_1275165 : Nat := 4983230072969 + 3 ^ 40 * 1275165 * 2
def baseEnd_1275165 : Nat := 654772558790608644773129

theorem tailTrace_1275165 : CollatzResearch.WordTrace tailWord_1275165 prefixEnd_1275165 654772558790608644773129 := by
  unfold tailWord_1275165
  simp only [CollatzResearch.WordTrace]
  refine ⟨46509088425302460688690949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31006058950201640459127299 46509088425302460688690949)
  ·
    refine ⟨8720454079744211379129553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46509088425302460688690949 8720454079744211379129553)
    ·
      refine ⟨6540340559808158534347165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8720454079744211379129553 6540340559808158534347165)
      ·
        refine ⟨2452627709928059450380187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6540340559808158534347165 2452627709928059450380187)
        ·
          refine ⟨3678941564892089175570281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2452627709928059450380187 3678941564892089175570281)
          ·
            refine ⟨2759206173669066881677711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3678941564892089175570281 2759206173669066881677711)
            ·
              refine ⟨4138809260503600322516567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2759206173669066881677711 4138809260503600322516567)
              ·
                refine ⟨6208213890755400483774851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4138809260503600322516567 6208213890755400483774851)
                ·
                  refine ⟨9312320836133100725662277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6208213890755400483774851 9312320836133100725662277)
                  ·
                    refine ⟨1746060156774956386061677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9312320836133100725662277 1746060156774956386061677)
                    ·
                      refine ⟨654772558790608644773129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1746060156774956386061677 654772558790608644773129)
                      ·
                        rfl

theorem cell23_1275165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1275165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275165 prefixEnd_1275165 := by exact prefixLift 1275165
  have htrace : WordTrace (prefixWord ++ tailWord_1275165) baseStart_1275165 baseEnd_1275165 := by
    simpa [prefixWord, tailWord_1275165, baseEnd_1275165] using wordTrace_append hprefix tailTrace_1275165
  have hstable : (prefixWord ++ tailWord_1275165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275165).length < 2 ^ (prefixWord ++ tailWord_1275165).sum := by decide
  have hdescent : baseEnd_1275165 < baseStart_1275165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275172 : List Nat := [2, 3, 1, 3, 1, 1, 4, 3, 1, 4]
def baseStart_1275172 : Nat := 118140960795 + 1275172 * 2 ^ 59
def prefixEnd_1275172 : Nat := 4983230072969 + 3 ^ 40 * 1275172 * 2
def baseEnd_1275172 : Nat := 218258717718396705795199

theorem tailTrace_1275172 : CollatzResearch.WordTrace tailWord_1275172 prefixEnd_1275172 218258717718396705795199 := by
  unfold tailWord_1275172
  simp only [CollatzResearch.WordTrace]
  refine ⟨23254671868138550442097885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31006229157518067256130513 23254671868138550442097885)
  ·
    refine ⟨8720501950551956415786707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23254671868138550442097885 8720501950551956415786707)
    ·
      refine ⟨13080752925827934623680061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8720501950551956415786707 13080752925827934623680061)
      ·
        refine ⟨4905282347185475483880023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13080752925827934623680061 4905282347185475483880023)
        ·
          refine ⟨7357923520778213225820035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4905282347185475483880023 7357923520778213225820035)
          ·
            refine ⟨11036885281167319838730053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7357923520778213225820035 11036885281167319838730053)
            ·
              refine ⟨2069415990218872469761885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11036885281167319838730053 2069415990218872469761885)
              ·
                refine ⟨776030996332077176160707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2069415990218872469761885 776030996332077176160707)
                ·
                  refine ⟨1164046494498115764241061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776030996332077176160707 1164046494498115764241061)
                  ·
                    refine ⟨218258717718396705795199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1164046494498115764241061 218258717718396705795199)
                    ·
                      rfl

theorem cell23_1275172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_1275172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275172 prefixEnd_1275172 := by exact prefixLift 1275172
  have htrace : WordTrace (prefixWord ++ tailWord_1275172) baseStart_1275172 baseEnd_1275172 := by
    simpa [prefixWord, tailWord_1275172, baseEnd_1275172] using wordTrace_append hprefix tailTrace_1275172
  have hstable : (prefixWord ++ tailWord_1275172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275172).length < 2 ^ (prefixWord ++ tailWord_1275172).sum := by decide
  have hdescent : baseEnd_1275172 < baseStart_1275172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275185 : List Nat := [1, 2, 2, 3, 3, 3, 1, 2, 6]
def baseStart_1275185 : Nat := 118140960795 + 1275185 * 2 ^ 59
def prefixEnd_1275185 : Nat := 4983230072969 + 3 ^ 40 * 1275185 * 2
def baseEnd_1275185 : Nat := 72753647600410951835893

theorem tailTrace_1275185 : CollatzResearch.WordTrace tailWord_1275185 prefixEnd_1275185 72753647600410951835893 := by
  unfold tailWord_1275185
  simp only [CollatzResearch.WordTrace]
  refine ⟨46509817885230004104419009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31006545256820002736279339 46509817885230004104419009)
  ·
    refine ⟨34882363413922503078314257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46509817885230004104419009 34882363413922503078314257)
    ·
      refine ⟨26161772560441877308735693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34882363413922503078314257 26161772560441877308735693)
      ·
        refine ⟨9810664710165703990775885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26161772560441877308735693 9810664710165703990775885)
        ·
          refine ⟨3678999266312138996540957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9810664710165703990775885 3678999266312138996540957)
          ·
            refine ⟨1379624724867052123702859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3678999266312138996540957 1379624724867052123702859)
            ·
              refine ⟨2069437087300578185554289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1379624724867052123702859 2069437087300578185554289)
              ·
                refine ⟨1552077815475433639165717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2069437087300578185554289 1552077815475433639165717)
                ·
                  refine ⟨72753647600410951835893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1552077815475433639165717 72753647600410951835893)
                  ·
                    rfl

theorem cell23_1275185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 6].length) (baseStart_1275185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275185 prefixEnd_1275185 := by exact prefixLift 1275185
  have htrace : WordTrace (prefixWord ++ tailWord_1275185) baseStart_1275185 baseEnd_1275185 := by
    simpa [prefixWord, tailWord_1275185, baseEnd_1275185] using wordTrace_append hprefix tailTrace_1275185
  have hstable : (prefixWord ++ tailWord_1275185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275185).length < 2 ^ (prefixWord ++ tailWord_1275185).sum := by decide
  have hdescent : baseEnd_1275185 < baseStart_1275185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275188 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1275188 : Nat := 118140960795 + 1275188 * 2 ^ 59
def prefixEnd_1275188 : Nat := 4983230072969 + 3 ^ 40 * 1275188 * 2
def baseEnd_1275188 : Nat := 654784368845662054785523

theorem tailTrace_1275188 : CollatzResearch.WordTrace tailWord_1275188 prefixEnd_1275188 654784368845662054785523 := by
  unfold tailWord_1275188
  simp only [CollatzResearch.WordTrace]
  refine ⟨23254963652109567808389109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31006618202812757077852145 23254963652109567808389109)
  ·
    refine ⟨2180152842385271982036479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23254963652109567808389109 2180152842385271982036479)
    ·
      refine ⟨3270229263577907973054719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2180152842385271982036479 3270229263577907973054719)
      ·
        refine ⟨4905343895366861959582079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270229263577907973054719 4905343895366861959582079)
        ·
          refine ⟨7358015843050292939373119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4905343895366861959582079 7358015843050292939373119)
          ·
            refine ⟨11037023764575439409059679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7358015843050292939373119 11037023764575439409059679)
            ·
              refine ⟨16555535646863159113589519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11037023764575439409059679 16555535646863159113589519)
              ·
                refine ⟨24833303470294738670384279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16555535646863159113589519 24833303470294738670384279)
                ·
                  refine ⟨37249955205442108005576419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24833303470294738670384279 37249955205442108005576419)
                  ·
                    refine ⟨55874932808163162008364629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37249955205442108005576419 55874932808163162008364629)
                    ·
                      refine ⟨654784368845662054785523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 55874932808163162008364629 654784368845662054785523)
                      ·
                        rfl

theorem cell23_1275188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1275188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275188 prefixEnd_1275188 := by exact prefixLift 1275188
  have htrace : WordTrace (prefixWord ++ tailWord_1275188) baseStart_1275188 baseEnd_1275188 := by
    simpa [prefixWord, tailWord_1275188, baseEnd_1275188] using wordTrace_append hprefix tailTrace_1275188
  have hstable : (prefixWord ++ tailWord_1275188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275188).length < 2 ^ (prefixWord ++ tailWord_1275188).sum := by decide
  have hdescent : baseEnd_1275188 < baseStart_1275188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275235 : List Nat := [1, 1, 1, 5, 2, 2, 2, 3, 1, 1, 4]
def baseStart_1275235 : Nat := 118140960795 + 1275235 * 2 ^ 59
def prefixEnd_1275235 : Nat := 4983230072969 + 3 ^ 40 * 1275235 * 2
def baseEnd_1275235 : Nat := 654808502436423370897807

theorem tailTrace_1275235 : CollatzResearch.WordTrace tailWord_1275235 prefixEnd_1275235 654808502436423370897807 := by
  unfold tailWord_1275235
  simp only [CollatzResearch.WordTrace]
  refine ⟨46511641535048862643739159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31007761023365908429159439 46511641535048862643739159)
  ·
    refine ⟨69767462302573293965608739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46511641535048862643739159 69767462302573293965608739)
    ·
      refine ⟨104651193453859940948413109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69767462302573293965608739 104651193453859940948413109)
      ·
        refine ⟨9811049386299369463913729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104651193453859940948413109 9811049386299369463913729)
        ·
          refine ⟨7358287039724527097935297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9811049386299369463913729 7358287039724527097935297)
          ·
            refine ⟨5518715279793395323451473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7358287039724527097935297 5518715279793395323451473)
            ·
              refine ⟨4139036459845046492588605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5518715279793395323451473 4139036459845046492588605)
              ·
                refine ⟨1552138672441892434720727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4139036459845046492588605 1552138672441892434720727)
                ·
                  refine ⟨2328208008662838652081091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552138672441892434720727 2328208008662838652081091)
                  ·
                    refine ⟨3492312012994257978121637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2328208008662838652081091 3492312012994257978121637)
                    ·
                      refine ⟨654808502436423370897807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3492312012994257978121637 654808502436423370897807)
                      ·
                        rfl

theorem cell23_1275235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_1275235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275235 prefixEnd_1275235 := by exact prefixLift 1275235
  have htrace : WordTrace (prefixWord ++ tailWord_1275235) baseStart_1275235 baseEnd_1275235 := by
    simpa [prefixWord, tailWord_1275235, baseEnd_1275235] using wordTrace_append hprefix tailTrace_1275235
  have hstable : (prefixWord ++ tailWord_1275235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275235).length < 2 ^ (prefixWord ++ tailWord_1275235).sum := by decide
  have hdescent : baseEnd_1275235 < baseStart_1275235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275245 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_1275245 : Nat := 118140960795 + 1275245 * 2 ^ 59
def prefixEnd_1275245 : Nat := 4983230072969 + 3 ^ 40 * 1275245 * 2
def baseEnd_1275245 : Nat := 218271212414322777257587

theorem tailTrace_1275245 : CollatzResearch.WordTrace tailWord_1275245 prefixEnd_1275245 218271212414322777257587 := by
  unfold tailWord_1275245
  simp only [CollatzResearch.WordTrace]
  refine ⟨46512006265012634351603189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31008004176675089567735459 46512006265012634351603189)
  ·
    refine ⟨4360500587344934470462799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46512006265012634351603189 4360500587344934470462799)
    ·
      refine ⟨6540750881017401705694199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4360500587344934470462799 6540750881017401705694199)
      ·
        refine ⟨9811126321526102558541299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6540750881017401705694199 9811126321526102558541299)
        ·
          refine ⟨14716689482289153837811949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9811126321526102558541299 14716689482289153837811949)
          ·
            refine ⟨5518758555858432689179481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14716689482289153837811949 5518758555858432689179481)
            ·
              refine ⟨4139068916893824516884611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5518758555858432689179481 4139068916893824516884611)
              ·
                refine ⟨6208603375340736775326917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4139068916893824516884611 6208603375340736775326917)
                ·
                  refine ⟨1164113132876388145373797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6208603375340736775326917 1164113132876388145373797)
                  ·
                    refine ⟨218271212414322777257587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1164113132876388145373797 218271212414322777257587)
                    ·
                      rfl

theorem cell23_1275245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_1275245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275245 prefixEnd_1275245 := by exact prefixLift 1275245
  have htrace : WordTrace (prefixWord ++ tailWord_1275245) baseStart_1275245 baseEnd_1275245 := by
    simpa [prefixWord, tailWord_1275245, baseEnd_1275245] using wordTrace_append hprefix tailTrace_1275245
  have hstable : (prefixWord ++ tailWord_1275245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275245).length < 2 ^ (prefixWord ++ tailWord_1275245).sum := by decide
  have hdescent : baseEnd_1275245 < baseStart_1275245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275246 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1275246 : Nat := 118140960795 + 1275246 * 2 ^ 59
def prefixEnd_1275246 : Nat := 4983230072969 + 3 ^ 40 * 1275246 * 2
def baseEnd_1275246 : Nat := 654814150723622827860257

theorem tailTrace_1275246 : CollatzResearch.WordTrace tailWord_1275246 prefixEnd_1275246 654814150723622827860257 := by
  unfold tailWord_1275246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5814005342251126440298699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31008028492006007681593061 5814005342251126440298699)
  ·
    refine ⟨8721008013376689660448049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5814005342251126440298699 8721008013376689660448049)
    ·
      refine ⟨6540756010032517245336037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8721008013376689660448049 6540756010032517245336037)
      ·
        refine ⟨1226391751881096983500507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6540756010032517245336037 1226391751881096983500507)
        ·
          refine ⟨1839587627821645475250761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1226391751881096983500507 1839587627821645475250761)
          ·
            refine ⟨1379690720866234106438071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1839587627821645475250761 1379690720866234106438071)
            ·
              refine ⟨2069536081299351159657107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1379690720866234106438071 2069536081299351159657107)
              ·
                refine ⟨3104304121949026739485661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069536081299351159657107 3104304121949026739485661)
                ·
                  refine ⟨1164114045730885027307123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3104304121949026739485661 1164114045730885027307123)
                  ·
                    refine ⟨1746171068596327540960685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1164114045730885027307123 1746171068596327540960685)
                    ·
                      refine ⟨654814150723622827860257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1746171068596327540960685 654814150723622827860257)
                      ·
                        rfl

theorem cell23_1275246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1275246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275246 prefixEnd_1275246 := by exact prefixLift 1275246
  have htrace : WordTrace (prefixWord ++ tailWord_1275246) baseStart_1275246 baseEnd_1275246 := by
    simpa [prefixWord, tailWord_1275246, baseEnd_1275246] using wordTrace_append hprefix tailTrace_1275246
  have hstable : (prefixWord ++ tailWord_1275246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275246).length < 2 ^ (prefixWord ++ tailWord_1275246).sum := by decide
  have hdescent : baseEnd_1275246 < baseStart_1275246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275251 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 7]
def baseStart_1275251 : Nat := 118140960795 + 1275251 * 2 ^ 59
def prefixEnd_1275251 : Nat := 4983230072969 + 3 ^ 40 * 1275251 * 2
def baseEnd_1275251 : Nat := 654816718126895308297733

theorem tailTrace_1275251 : CollatzResearch.WordTrace tailWord_1275251 prefixEnd_1275251 654816718126895308297733 := by
  unfold tailWord_1275251
  simp only [CollatzResearch.WordTrace]
  refine ⟨46512225102990897376321607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31008150068660598250881071 46512225102990897376321607)
  ·
    refine ⟨69768337654486346064482411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46512225102990897376321607 69768337654486346064482411)
    ·
      refine ⟨104652506481729519096723617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69768337654486346064482411 104652506481729519096723617)
      ·
        refine ⟨78489379861297139322542713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104652506481729519096723617 78489379861297139322542713)
        ·
          refine ⟨58867034895972854491907035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78489379861297139322542713 58867034895972854491907035)
          ·
            refine ⟨88300552343959281737860553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58867034895972854491907035 88300552343959281737860553)
            ·
              refine ⟨66225414257969461303395415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88300552343959281737860553 66225414257969461303395415)
              ·
                refine ⟨99338121386954191955093123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66225414257969461303395415 99338121386954191955093123)
                ·
                  refine ⟨149007182080431287932639685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99338121386954191955093123 149007182080431287932639685)
                  ·
                    refine ⟨27938846640080866487369941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149007182080431287932639685 27938846640080866487369941)
                    ·
                      refine ⟨654816718126895308297733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27938846640080866487369941 654816718126895308297733)
                      ·
                        rfl

theorem cell23_1275251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_1275251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275251 prefixEnd_1275251 := by exact prefixLift 1275251
  have htrace : WordTrace (prefixWord ++ tailWord_1275251) baseStart_1275251 baseEnd_1275251 := by
    simpa [prefixWord, tailWord_1275251, baseEnd_1275251] using wordTrace_append hprefix tailTrace_1275251
  have hstable : (prefixWord ++ tailWord_1275251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275251).length < 2 ^ (prefixWord ++ tailWord_1275251).sum := by decide
  have hdescent : baseEnd_1275251 < baseStart_1275251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275272 : List Nat := [2, 1, 3, 3, 1, 2, 3, 2, 1, 2, 3]
def baseStart_1275272 : Nat := 118140960795 + 1275272 * 2 ^ 59
def prefixEnd_1275272 : Nat := 4983230072969 + 3 ^ 40 * 1275272 * 2
def baseEnd_1275272 : Nat := 654827501220639726135137

theorem tailTrace_1275272 : CollatzResearch.WordTrace tailWord_1275272 prefixEnd_1275272 654827501220639726135137 := by
  unfold tailWord_1275272
  simp only [CollatzResearch.WordTrace]
  refine ⟨23256495517957408981418035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31008660690609878641890713 23256495517957408981418035)
  ·
    refine ⟨34884743276936113472127053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23256495517957408981418035 34884743276936113472127053)
    ·
      refine ⟨13081778728851042552047645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34884743276936113472127053 13081778728851042552047645)
      ·
        refine ⟨4905667023319140957017867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13081778728851042552047645 4905667023319140957017867)
        ·
          refine ⟨7358500534978711435526801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4905667023319140957017867 7358500534978711435526801)
          ·
            refine ⟨5518875401234033576645101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7358500534978711435526801 5518875401234033576645101)
            ·
              refine ⟨2069578275462762591241913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5518875401234033576645101 2069578275462762591241913)
              ·
                refine ⟨1552183706597071943431435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2069578275462762591241913 1552183706597071943431435)
                ·
                  refine ⟨2328275559895607915147153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552183706597071943431435 2328275559895607915147153)
                  ·
                    refine ⟨1746206669921705936360365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2328275559895607915147153 1746206669921705936360365)
                    ·
                      refine ⟨654827501220639726135137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1746206669921705936360365 654827501220639726135137)
                      ·
                        rfl

theorem cell23_1275272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_1275272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275272 prefixEnd_1275272 := by exact prefixLift 1275272
  have htrace : WordTrace (prefixWord ++ tailWord_1275272) baseStart_1275272 baseEnd_1275272 := by
    simpa [prefixWord, tailWord_1275272, baseEnd_1275272] using wordTrace_append hprefix tailTrace_1275272
  have hstable : (prefixWord ++ tailWord_1275272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275272).length < 2 ^ (prefixWord ++ tailWord_1275272).sum := by decide
  have hdescent : baseEnd_1275272 < baseStart_1275272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275285 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 6, 1, 3]
def baseStart_1275285 : Nat := 118140960795 + 1275285 * 2 ^ 59
def prefixEnd_1275285 : Nat := 4983230072969 + 3 ^ 40 * 1275285 * 2
def baseEnd_1275285 : Nat := 654834176469148175272577

theorem tailTrace_1275285 : CollatzResearch.WordTrace tailWord_1275285 prefixEnd_1275285 654834176469148175272577 := by
  unfold tailWord_1275285
  simp only [CollatzResearch.WordTrace]
  refine ⟨46513465184867721183059309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31008976789911814122039539 46513465184867721183059309)
  ·
    refine ⟨17442549444325395443647241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46513465184867721183059309 17442549444325395443647241)
    ·
      refine ⟨13081912083244046582735431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17442549444325395443647241 13081912083244046582735431)
      ·
        refine ⟨19622868124866069874103147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13081912083244046582735431 19622868124866069874103147)
        ·
          refine ⟨29434302187299104811154721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19622868124866069874103147 29434302187299104811154721)
          ·
            refine ⟨22075726640474328608366041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29434302187299104811154721 22075726640474328608366041)
            ·
              refine ⟨16556794980355746456274531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22075726640474328608366041 16556794980355746456274531)
              ·
                refine ⟨24835192470533619684411797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16556794980355746456274531 24835192470533619684411797)
                ·
                  refine ⟨1164149647056263422706803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24835192470533619684411797 1164149647056263422706803)
                  ·
                    refine ⟨1746224470584395134060205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1164149647056263422706803 1746224470584395134060205)
                    ·
                      refine ⟨654834176469148175272577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1746224470584395134060205 654834176469148175272577)
                      ·
                        rfl

theorem cell23_1275285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_1275285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275285 prefixEnd_1275285 := by exact prefixLift 1275285
  have htrace : WordTrace (prefixWord ++ tailWord_1275285) baseStart_1275285 baseEnd_1275285 := by
    simpa [prefixWord, tailWord_1275285, baseEnd_1275285] using wordTrace_append hprefix tailTrace_1275285
  have hstable : (prefixWord ++ tailWord_1275285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275285).length < 2 ^ (prefixWord ++ tailWord_1275285).sum := by decide
  have hdescent : baseEnd_1275285 < baseStart_1275285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275308 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_1275308 : Nat := 118140960795 + 1275308 * 2 ^ 59
def prefixEnd_1275308 : Nat := 4983230072969 + 3 ^ 40 * 1275308 * 2
def baseEnd_1275308 : Nat := 654845986524201585284971

theorem tailTrace_1275308 : CollatzResearch.WordTrace tailWord_1275308 prefixEnd_1275308 654845986524201585284971 := by
  unfold tailWord_1275308
  simp only [CollatzResearch.WordTrace]
  refine ⟨23257152031892198055573289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31009536042522930740764385 23257152031892198055573289)
  ·
    refine ⟨17442864023919148541679967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23257152031892198055573289 17442864023919148541679967)
    ·
      refine ⟨26164296035878722812519951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17442864023919148541679967 26164296035878722812519951)
      ·
        refine ⟨39246444053818084218779927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26164296035878722812519951 39246444053818084218779927)
        ·
          refine ⟨58869666080727126328169891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39246444053818084218779927 58869666080727126328169891)
          ·
            refine ⟨88304499121090689492254837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58869666080727126328169891 88304499121090689492254837)
            ·
              refine ⟨8278546792602252139898891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88304499121090689492254837 8278546792602252139898891)
              ·
                refine ⟨12417820188903378209848337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8278546792602252139898891 12417820188903378209848337)
                ·
                  refine ⟨9313365141677533657386253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12417820188903378209848337 9313365141677533657386253)
                  ·
                    refine ⟨3492511928129075121519845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9313365141677533657386253 3492511928129075121519845)
                    ·
                      refine ⟨654845986524201585284971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3492511928129075121519845 654845986524201585284971)
                      ·
                        rfl

theorem cell23_1275308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_1275308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275308 prefixEnd_1275308 := by exact prefixLift 1275308
  have htrace : WordTrace (prefixWord ++ tailWord_1275308) baseStart_1275308 baseEnd_1275308 := by
    simpa [prefixWord, tailWord_1275308, baseEnd_1275308] using wordTrace_append hprefix tailTrace_1275308
  have hstable : (prefixWord ++ tailWord_1275308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275308).length < 2 ^ (prefixWord ++ tailWord_1275308).sum := by decide
  have hdescent : baseEnd_1275308 < baseStart_1275308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275328 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 5]
def baseStart_1275328 : Nat := 118140960795 + 1275328 * 2 ^ 59
def prefixEnd_1275328 : Nat := 4983230072969 + 3 ^ 40 * 1275328 * 2
def baseEnd_1275328 : Nat := 654856256137291507034879

theorem tailTrace_1275328 : CollatzResearch.WordTrace tailWord_1275328 prefixEnd_1275328 654856256137291507034879 := by
  unfold tailWord_1275328
  simp only [CollatzResearch.WordTrace]
  refine ⟨23257516761855969763437319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31010022349141293017916425 23257516761855969763437319)
  ·
    refine ⟨34886275142783954645155979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23257516761855969763437319 34886275142783954645155979)
    ·
      refine ⟨52329412714175931967733969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34886275142783954645155979 52329412714175931967733969)
      ·
        refine ⟨39247059535631948975800477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52329412714175931967733969 39247059535631948975800477)
        ·
          refine ⟨14717647325861980865925179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39247059535631948975800477 14717647325861980865925179)
          ·
            refine ⟨22076470988792971298887769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14717647325861980865925179 22076470988792971298887769)
            ·
              refine ⟨16557353241594728474165827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22076470988792971298887769 16557353241594728474165827)
              ·
                refine ⟨24836029862392092711248741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16557353241594728474165827 24836029862392092711248741)
                ·
                  refine ⟨4656755599198517383359139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24836029862392092711248741 4656755599198517383359139)
                  ·
                    refine ⟨6985133398797776075038709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4656755599198517383359139 6985133398797776075038709)
                    ·
                      refine ⟨654856256137291507034879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6985133398797776075038709 654856256137291507034879)
                      ·
                        rfl

theorem cell23_1275328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_1275328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275328 prefixEnd_1275328 := by exact prefixLift 1275328
  have htrace : WordTrace (prefixWord ++ tailWord_1275328) baseStart_1275328 baseEnd_1275328 := by
    simpa [prefixWord, tailWord_1275328, baseEnd_1275328] using wordTrace_append hprefix tailTrace_1275328
  have hstable : (prefixWord ++ tailWord_1275328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275328).length < 2 ^ (prefixWord ++ tailWord_1275328).sum := by decide
  have hdescent : baseEnd_1275328 < baseStart_1275328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275342 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2]
def baseStart_1275342 : Nat := 118140960795 + 1275342 * 2 ^ 59
def prefixEnd_1275342 : Nat := 4983230072969 + 3 ^ 40 * 1275342 * 2
def baseEnd_1275342 : Nat := 654863444866454452259815

theorem tailTrace_1275342 : CollatzResearch.WordTrace tailWord_1275342 prefixEnd_1275342 654863444866454452259815 := by
  unfold tailWord_1275342
  simp only [CollatzResearch.WordTrace]
  refine ⟨5814443018207652489735535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31010362763774146611922853 5814443018207652489735535)
  ·
    refine ⟨8721664527311478734603303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5814443018207652489735535 8721664527311478734603303)
    ·
      refine ⟨13082496790967218101904955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8721664527311478734603303 13082496790967218101904955)
      ·
        refine ⟨19623745186450827152857433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13082496790967218101904955 19623745186450827152857433)
        ·
          refine ⟨14717808889838120364643075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19623745186450827152857433 14717808889838120364643075)
          ·
            refine ⟨22076713334757180546964613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14717808889838120364643075 22076713334757180546964613)
            ·
              refine ⟨4139383750266971352555865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22076713334757180546964613 4139383750266971352555865)
              ·
                refine ⟨3104537812700228514416899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4139383750266971352555865 3104537812700228514416899)
                ·
                  refine ⟨4656806719050342771625349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3104537812700228514416899 4656806719050342771625349)
                  ·
                    refine ⟨873151259821939269679753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4656806719050342771625349 873151259821939269679753)
                    ·
                      refine ⟨654863444866454452259815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 873151259821939269679753 654863444866454452259815)
                      ·
                        rfl

theorem cell23_1275342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_1275342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275342 prefixEnd_1275342 := by exact prefixLift 1275342
  have htrace : WordTrace (prefixWord ++ tailWord_1275342) baseStart_1275342 baseEnd_1275342 := by
    simpa [prefixWord, tailWord_1275342, baseEnd_1275342] using wordTrace_append hprefix tailTrace_1275342
  have hstable : (prefixWord ++ tailWord_1275342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275342).length < 2 ^ (prefixWord ++ tailWord_1275342).sum := by decide
  have hdescent : baseEnd_1275342 < baseStart_1275342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275365 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 7]
def baseStart_1275365 : Nat := 118140960795 + 1275365 * 2 ^ 59
def prefixEnd_1275365 : Nat := 4983230072969 + 3 ^ 40 * 1275365 * 2
def baseEnd_1275365 : Nat := 72763917213500873585801

theorem tailTrace_1275365 : CollatzResearch.WordTrace tailWord_1275365 prefixEnd_1275365 72763917213500873585801 := by
  unfold tailWord_1275365
  simp only [CollatzResearch.WordTrace]
  refine ⟨46516383024577894845971549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31010922016385263230647699 46516383024577894845971549)
  ·
    refine ⟨17443643634216710567239331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46516383024577894845971549 17443643634216710567239331)
    ·
      refine ⟨26165465451325065850858997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17443643634216710567239331 26165465451325065850858997)
      ·
        refine ⟨2453012386061724923518031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26165465451325065850858997 2453012386061724923518031)
        ·
          refine ⟨3679518579092587385277047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2453012386061724923518031 3679518579092587385277047)
          ·
            refine ⟨5519277868638881077915571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3679518579092587385277047 5519277868638881077915571)
            ·
              refine ⟨8278916802958321616873357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5519277868638881077915571 8278916802958321616873357)
              ·
                refine ⟨3104593801109370606327509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8278916802958321616873357 3104593801109370606327509)
                ·
                  refine ⟨72763917213500873585801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3104593801109370606327509 72763917213500873585801)
                  ·
                    rfl

theorem cell23_1275365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_1275365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275365 prefixEnd_1275365 := by exact prefixLift 1275365
  have htrace : WordTrace (prefixWord ++ tailWord_1275365) baseStart_1275365 baseEnd_1275365 := by
    simpa [prefixWord, tailWord_1275365, baseEnd_1275365] using wordTrace_append hprefix tailTrace_1275365
  have hstable : (prefixWord ++ tailWord_1275365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275365).length < 2 ^ (prefixWord ++ tailWord_1275365).sum := by decide
  have hdescent : baseEnd_1275365 < baseStart_1275365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275375 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 3]
def baseStart_1275375 : Nat := 118140960795 + 1275375 * 2 ^ 59
def prefixEnd_1275375 : Nat := 4983230072969 + 3 ^ 40 * 1275375 * 2
def baseEnd_1275375 : Nat := 654880389728052823147163

theorem tailTrace_1275375 : CollatzResearch.WordTrace tailWord_1275375 prefixEnd_1275375 654880389728052823147163 := by
  unfold tailWord_1275375
  simp only [CollatzResearch.WordTrace]
  refine ⟨46516747754541666553835579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31011165169694444369223719 46516747754541666553835579)
  ·
    refine ⟨69775121631812499830753369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46516747754541666553835579 69775121631812499830753369)
    ·
      refine ⟨52331341223859374873065027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69775121631812499830753369 52331341223859374873065027)
      ·
        refine ⟨78497011835789062309597541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52331341223859374873065027 78497011835789062309597541)
        ·
          refine ⟨14718189719210449183049539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78497011835789062309597541 14718189719210449183049539)
          ·
            refine ⟨22077284578815673774574309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14718189719210449183049539 22077284578815673774574309)
            ·
              refine ⟨4139490858527938832732683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22077284578815673774574309 4139490858527938832732683)
              ·
                refine ⟨6209236287791908249099025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4139490858527938832732683 6209236287791908249099025)
                ·
                  refine ⟨4656927215843931186824269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6209236287791908249099025 4656927215843931186824269)
                  ·
                    refine ⟨1746347705941474195059101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4656927215843931186824269 1746347705941474195059101)
                    ·
                      refine ⟨654880389728052823147163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1746347705941474195059101 654880389728052823147163)
                      ·
                        rfl

theorem cell23_1275375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 3].length) (baseStart_1275375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275375 prefixEnd_1275375 := by exact prefixLift 1275375
  have htrace : WordTrace (prefixWord ++ tailWord_1275375) baseStart_1275375 baseEnd_1275375 := by
    simpa [prefixWord, tailWord_1275375, baseEnd_1275375] using wordTrace_append hprefix tailTrace_1275375
  have hstable : (prefixWord ++ tailWord_1275375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275375).length < 2 ^ (prefixWord ++ tailWord_1275375).sum := by decide
  have hdescent : baseEnd_1275375 < baseStart_1275375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275376 : List Nat := [2, 1, 1, 1, 3, 5, 3, 1, 2, 2, 2]
def baseStart_1275376 : Nat := 118140960795 + 1275376 * 2 ^ 59
def prefixEnd_1275376 : Nat := 4983230072969 + 3 ^ 40 * 1275376 * 2
def baseEnd_1275376 : Nat := 654880903208707319234659

theorem tailTrace_1275376 : CollatzResearch.WordTrace tailWord_1275376 prefixEnd_1275376 654880903208707319234659 := by
  unfold tailWord_1275376
  simp only [CollatzResearch.WordTrace]
  refine ⟨23258392113769021862310991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31011189485025362483081321 23258392113769021862310991)
  ·
    refine ⟨34887588170653532793466487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23258392113769021862310991 34887588170653532793466487)
    ·
      refine ⟨52331382255980299190199731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34887588170653532793466487 52331382255980299190199731)
      ·
        refine ⟨78497073383970448785299597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52331382255980299190199731 78497073383970448785299597)
        ·
          refine ⟨29436402518988918294487349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78497073383970448785299597 29436402518988918294487349)
          ·
            refine ⟨2759662736155211090108189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29436402518988918294487349 2759662736155211090108189)
            ·
              refine ⟨1034873526058204158790571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2759662736155211090108189 1034873526058204158790571)
              ·
                refine ⟨1552310289087306238185857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034873526058204158790571 1552310289087306238185857)
                ·
                  refine ⟨1164232716815479678639393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1552310289087306238185857 1164232716815479678639393)
                  ·
                    refine ⟨873174537611609758979545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1164232716815479678639393 873174537611609758979545)
                    ·
                      refine ⟨654880903208707319234659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 873174537611609758979545 654880903208707319234659)
                      ·
                        rfl

theorem cell23_1275376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 2, 2, 2].length) (baseStart_1275376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275376 prefixEnd_1275376 := by exact prefixLift 1275376
  have htrace : WordTrace (prefixWord ++ tailWord_1275376) baseStart_1275376 baseEnd_1275376 := by
    simpa [prefixWord, tailWord_1275376, baseEnd_1275376] using wordTrace_append hprefix tailTrace_1275376
  have hstable : (prefixWord ++ tailWord_1275376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275376).length < 2 ^ (prefixWord ++ tailWord_1275376).sum := by decide
  have hdescent : baseEnd_1275376 < baseStart_1275376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275399 : List Nat := [1, 1, 4, 3, 2, 3, 1, 3, 5]
def baseStart_1275399 : Nat := 118140960795 + 1275399 * 2 ^ 59
def prefixEnd_1275399 : Nat := 4983230072969 + 3 ^ 40 * 1275399 * 2
def baseEnd_1275399 : Nat := 72765857029306747694117

theorem tailTrace_1275399 : CollatzResearch.WordTrace tailWord_1275399 prefixEnd_1275399 72765857029306747694117 := by
  unfold tailWord_1275399
  simp only [CollatzResearch.WordTrace]
  refine ⟨46517623106454718652709251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31011748737636479101806167 46517623106454718652709251)
  ·
    refine ⟨69776434659682077979063877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46517623106454718652709251 69776434659682077979063877)
    ·
      refine ⟨13083081498690389621074477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69776434659682077979063877 13083081498690389621074477)
      ·
        refine ⟨4906155562008896107902929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13083081498690389621074477 4906155562008896107902929)
        ·
          refine ⟨3679616671506672080927197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4906155562008896107902929 3679616671506672080927197)
          ·
            refine ⟨1379856251815002030347699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3679616671506672080927197 1379856251815002030347699)
            ·
              refine ⟨2069784377722503045521549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1379856251815002030347699 2069784377722503045521549)
              ·
                refine ⟨776169141645938642070581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2069784377722503045521549 776169141645938642070581)
                ·
                  refine ⟨72765857029306747694117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 776169141645938642070581 72765857029306747694117)
                  ·
                    rfl

theorem cell23_1275399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 5].length) (baseStart_1275399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275399 prefixEnd_1275399 := by exact prefixLift 1275399
  have htrace : WordTrace (prefixWord ++ tailWord_1275399) baseStart_1275399 baseEnd_1275399 := by
    simpa [prefixWord, tailWord_1275399, baseEnd_1275399] using wordTrace_append hprefix tailTrace_1275399
  have hstable : (prefixWord ++ tailWord_1275399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275399).length < 2 ^ (prefixWord ++ tailWord_1275399).sum := by decide
  have hdescent : baseEnd_1275399 < baseStart_1275399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275482 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3]
def baseStart_1275482 : Nat := 118140960795 + 1275482 * 2 ^ 59
def prefixEnd_1275482 : Nat := 4983230072969 + 3 ^ 40 * 1275482 * 2
def baseEnd_1275482 : Nat := 654935332158083904509171

theorem tailTrace_1275482 : CollatzResearch.WordTrace tailWord_1275482 prefixEnd_1275482 654935332158083904509171 := by
  unfold tailWord_1275482
  simp only [CollatzResearch.WordTrace]
  refine ⟨11630162591288505956995175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31013766910102682551987133 11630162591288505956995175)
  ·
    refine ⟨17445243886932758935492763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11630162591288505956995175 17445243886932758935492763)
    ·
      refine ⟨26167865830399138403239145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17445243886932758935492763 26167865830399138403239145)
      ·
        refine ⟨19625899372799353802429359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26167865830399138403239145 19625899372799353802429359)
        ·
          refine ⟨29438849059199030703644039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19625899372799353802429359 29438849059199030703644039)
          ·
            refine ⟨44158273588798546055466059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29438849059199030703644039 44158273588798546055466059)
            ·
              refine ⟨66237410383197819083199089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44158273588798546055466059 66237410383197819083199089)
              ·
                refine ⟨49678057787398364312399317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66237410383197819083199089 49678057787398364312399317)
                ·
                  refine ⟨1164329479392149163571859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 49678057787398364312399317 1164329479392149163571859)
                  ·
                    refine ⟨1746494219088223745357789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1164329479392149163571859 1746494219088223745357789)
                    ·
                      refine ⟨654935332158083904509171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1746494219088223745357789 654935332158083904509171)
                      ·
                        rfl

theorem cell23_1275482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_1275482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275482 prefixEnd_1275482 := by exact prefixLift 1275482
  have htrace : WordTrace (prefixWord ++ tailWord_1275482) baseStart_1275482 baseEnd_1275482 := by
    simpa [prefixWord, tailWord_1275482, baseEnd_1275482] using wordTrace_append hprefix tailTrace_1275482
  have hstable : (prefixWord ++ tailWord_1275482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275482).length < 2 ^ (prefixWord ++ tailWord_1275482).sum := by decide
  have hdescent : baseEnd_1275482 < baseStart_1275482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275515 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 1, 6]
def baseStart_1275515 : Nat := 118140960795 + 1275515 * 2 ^ 59
def prefixEnd_1275515 : Nat := 4983230072969 + 3 ^ 40 * 1275515 * 2
def baseEnd_1275515 : Nat := 218317425673227425132173

theorem tailTrace_1275515 : CollatzResearch.WordTrace tailWord_1275515 prefixEnd_1275515 218317425673227425132173 := by
  unfold tailWord_1275515
  simp only [CollatzResearch.WordTrace]
  refine ⟨46521853974034470463931999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31014569316022980309287999 46521853974034470463931999)
  ·
    refine ⟨69782780961051705695897999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46521853974034470463931999 69782780961051705695897999)
    ·
      refine ⟨104674171441577558543846999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69782780961051705695897999 104674171441577558543846999)
      ·
        refine ⟨157011257162366337815770499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104674171441577558543846999 157011257162366337815770499)
        ·
          refine ⟨235516885743549506723655749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157011257162366337815770499 235516885743549506723655749)
          ·
            refine ⟨44159416076915532510685453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235516885743549506723655749 44159416076915532510685453)
            ·
              refine ⟨16559781028843324691507045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44159416076915532510685453 16559781028843324691507045)
              ·
                refine ⟨3104958942908123379657571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16559781028843324691507045 3104958942908123379657571)
                ·
                  refine ⟨4657438414362185069486357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3104958942908123379657571 4657438414362185069486357)
                  ·
                    refine ⟨218317425673227425132173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4657438414362185069486357 218317425673227425132173)
                    ·
                      rfl

theorem cell23_1275515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 6].length) (baseStart_1275515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275515 prefixEnd_1275515 := by exact prefixLift 1275515
  have htrace : WordTrace (prefixWord ++ tailWord_1275515) baseStart_1275515 baseEnd_1275515 := by
    simpa [prefixWord, tailWord_1275515, baseEnd_1275515] using wordTrace_append hprefix tailTrace_1275515
  have hstable : (prefixWord ++ tailWord_1275515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275515).length < 2 ^ (prefixWord ++ tailWord_1275515).sum := by decide
  have hdescent : baseEnd_1275515 < baseStart_1275515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275532 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 4, 4]
def baseStart_1275532 : Nat := 118140960795 + 1275532 * 2 ^ 59
def prefixEnd_1275532 : Nat := 4983230072969 + 3 ^ 40 * 1275532 * 2
def baseEnd_1275532 : Nat := 218320335396936236294647

theorem tailTrace_1275532 : CollatzResearch.WordTrace tailWord_1275532 prefixEnd_1275532 218320335396936236294647 := by
  unfold tailWord_1275532
  simp only [CollatzResearch.WordTrace]
  refine ⟨23261237007486441183650425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31014982676648588244867233 23261237007486441183650425)
  ·
    refine ⟨17445927755614830887737819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23261237007486441183650425 17445927755614830887737819)
    ·
      refine ⟨26168891633422246331606729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17445927755614830887737819 26168891633422246331606729)
      ·
        refine ⟨19626668725066684748705047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26168891633422246331606729 19626668725066684748705047)
        ·
          refine ⟨29440003087600027123057571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19626668725066684748705047 29440003087600027123057571)
          ·
            refine ⟨44160004631400040684586357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29440003087600027123057571 44160004631400040684586357)
            ·
              refine ⟨4140000434193753814179971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44160004631400040684586357 4140000434193753814179971)
              ·
                refine ⟨6210000651290630721269957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4140000434193753814179971 6210000651290630721269957)
                ·
                  refine ⟨1164375122116993260238117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6210000651290630721269957 1164375122116993260238117)
                  ·
                    refine ⟨218320335396936236294647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1164375122116993260238117 218320335396936236294647)
                    ·
                      rfl

theorem cell23_1275532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_1275532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275532 prefixEnd_1275532 := by exact prefixLift 1275532
  have htrace : WordTrace (prefixWord ++ tailWord_1275532) baseStart_1275532 baseEnd_1275532 := by
    simpa [prefixWord, tailWord_1275532, baseEnd_1275532] using wordTrace_append hprefix tailTrace_1275532
  have hstable : (prefixWord ++ tailWord_1275532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275532).length < 2 ^ (prefixWord ++ tailWord_1275532).sum := by decide
  have hdescent : baseEnd_1275532 < baseStart_1275532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275552 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 6]
def baseStart_1275552 : Nat := 118140960795 + 1275552 * 2 ^ 59
def prefixEnd_1275552 : Nat := 4983230072969 + 3 ^ 40 * 1275552 * 2
def baseEnd_1275552 : Nat := 654971275803898630633849

theorem tailTrace_1275552 : CollatzResearch.WordTrace tailWord_1275552 prefixEnd_1275552 654971275803898630633849 := by
  unfold tailWord_1275552
  simp only [CollatzResearch.WordTrace]
  refine ⟨23261601737450212891514455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31015468983266950522019273 23261601737450212891514455)
  ·
    refine ⟨34892402606175319337271683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23261601737450212891514455 34892402606175319337271683)
    ·
      refine ⟨52338603909262979005907525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34892402606175319337271683 52338603909262979005907525)
      ·
        refine ⟨9813488232986808563607661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52338603909262979005907525 9813488232986808563607661)
        ·
          refine ⟨3680058087370053211352873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9813488232986808563607661 3680058087370053211352873)
          ·
            refine ⟨2760043565527539908514655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3680058087370053211352873 2760043565527539908514655)
            ·
              refine ⟨4140065348291309862771983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2760043565527539908514655 4140065348291309862771983)
              ·
                refine ⟨6210098022436964794157975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4140065348291309862771983 6210098022436964794157975)
                ·
                  refine ⟨9315147033655447191236963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6210098022436964794157975 9315147033655447191236963)
                  ·
                    refine ⟨13972720550483170786855445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9315147033655447191236963 13972720550483170786855445)
                    ·
                      refine ⟨654971275803898630633849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13972720550483170786855445 654971275803898630633849)
                      ·
                        rfl

theorem cell23_1275552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_1275552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275552 prefixEnd_1275552 := by exact prefixLift 1275552
  have htrace : WordTrace (prefixWord ++ tailWord_1275552) baseStart_1275552 baseEnd_1275552 := by
    simpa [prefixWord, tailWord_1275552, baseEnd_1275552] using wordTrace_append hprefix tailTrace_1275552
  have hstable : (prefixWord ++ tailWord_1275552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275552).length < 2 ^ (prefixWord ++ tailWord_1275552).sum := by decide
  have hdescent : baseEnd_1275552 < baseStart_1275552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275556 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 3, 2, 2]
def baseStart_1275556 : Nat := 118140960795 + 1275556 * 2 ^ 59
def prefixEnd_1275556 : Nat := 4983230072969 + 3 ^ 40 * 1275556 * 2
def baseEnd_1275556 : Nat := 654973329726516614983831

theorem tailTrace_1275556 : CollatzResearch.WordTrace tailWord_1275556 prefixEnd_1275556 654973329726516614983831 := by
  unfold tailWord_1275556
  simp only [CollatzResearch.WordTrace]
  refine ⟨23261674683442967233087261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31015566244590622977449681 23261674683442967233087261)
  ·
    refine ⟨8723128006291112712407723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23261674683442967233087261 8723128006291112712407723)
    ·
      refine ⟨13084692009436669068611585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8723128006291112712407723 13084692009436669068611585)
      ·
        refine ⟨9813519007077501801458689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13084692009436669068611585 9813519007077501801458689)
        ·
          refine ⟨7360139255308126351094017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9813519007077501801458689 7360139255308126351094017)
          ·
            refine ⟨5520104441481094763320513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7360139255308126351094017 5520104441481094763320513)
            ·
              refine ⟨4140078331110821072490385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5520104441481094763320513 4140078331110821072490385)
              ·
                refine ⟨3105058748333115804367789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4140078331110821072490385 3105058748333115804367789)
                ·
                  refine ⟨1164397030624918426637921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3105058748333115804367789 1164397030624918426637921)
                  ·
                    refine ⟨873297772968688819978441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1164397030624918426637921 873297772968688819978441)
                    ·
                      refine ⟨654973329726516614983831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 873297772968688819978441 654973329726516614983831)
                      ·
                        rfl

theorem cell23_1275556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_1275556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275556 prefixEnd_1275556 := by exact prefixLift 1275556
  have htrace : WordTrace (prefixWord ++ tailWord_1275556) baseStart_1275556 baseEnd_1275556 := by
    simpa [prefixWord, tailWord_1275556, baseEnd_1275556] using wordTrace_append hprefix tailTrace_1275556
  have hstable : (prefixWord ++ tailWord_1275556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275556).length < 2 ^ (prefixWord ++ tailWord_1275556).sum := by decide
  have hdescent : baseEnd_1275556 < baseStart_1275556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275616 : List Nat := [2, 1, 1, 3, 1, 2, 5, 2, 1, 3, 2]
def baseStart_1275616 : Nat := 118140960795 + 1275616 * 2 ^ 59
def prefixEnd_1275616 : Nat := 4983230072969 + 3 ^ 40 * 1275616 * 2
def baseEnd_1275616 : Nat := 655004138565786380233555

theorem tailTrace_1275616 : CollatzResearch.WordTrace tailWord_1275616 prefixEnd_1275616 655004138565786380233555 := by
  unfold tailWord_1275616
  simp only [CollatzResearch.WordTrace]
  refine ⟨23262768873334282356679351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31017025164445709808905801 23262768873334282356679351)
  ·
    refine ⟨34894153310001423535019027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23262768873334282356679351 34894153310001423535019027)
    ·
      refine ⟨52341229965002135302528541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34894153310001423535019027 52341229965002135302528541)
      ·
        refine ⟨19627961236875800738448203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52341229965002135302528541 19627961236875800738448203)
        ·
          refine ⟨29441941855313701107672305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19627961236875800738448203 29441941855313701107672305)
          ·
            refine ⟨22081456391485275830754229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29441941855313701107672305 22081456391485275830754229)
            ·
              refine ⟨2070136536701744609133209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22081456391485275830754229 2070136536701744609133209)
              ·
                refine ⟨1552602402526308456849907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2070136536701744609133209 1552602402526308456849907)
                ·
                  refine ⟨2328903603789462685274861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552602402526308456849907 2328903603789462685274861)
                  ·
                    refine ⟨873338851421048506978073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2328903603789462685274861 873338851421048506978073)
                    ·
                      refine ⟨655004138565786380233555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 873338851421048506978073 655004138565786380233555)
                      ·
                        rfl

theorem cell23_1275616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_1275616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275616 prefixEnd_1275616 := by exact prefixLift 1275616
  have htrace : WordTrace (prefixWord ++ tailWord_1275616) baseStart_1275616 baseEnd_1275616 := by
    simpa [prefixWord, tailWord_1275616, baseEnd_1275616] using wordTrace_append hprefix tailTrace_1275616
  have hstable : (prefixWord ++ tailWord_1275616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275616).length < 2 ^ (prefixWord ++ tailWord_1275616).sum := by decide
  have hdescent : baseEnd_1275616 < baseStart_1275616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275633 : List Nat := [1, 2, 2, 2, 2, 4, 3, 1, 1, 3, 2]
def baseStart_1275633 : Nat := 118140960795 + 1275633 * 2 ^ 59
def prefixEnd_1275633 : Nat := 4983230072969 + 3 ^ 40 * 1275633 * 2
def baseEnd_1275633 : Nat := 655012867736912813720977

theorem tailTrace_1275633 : CollatzResearch.WordTrace tailWord_1275633 prefixEnd_1275633 655012867736912813720977 := by
  unfold tailWord_1275633
  simp only [CollatzResearch.WordTrace]
  refine ⟨46526157787606976616727553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31017438525071317744485035 46526157787606976616727553)
  ·
    refine ⟨34894618340705232462545665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46526157787606976616727553 34894618340705232462545665)
    ·
      refine ⟨26170963755528924346909249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34894618340705232462545665 26170963755528924346909249)
      ·
        refine ⟨19628222816646693260181937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26170963755528924346909249 19628222816646693260181937)
        ·
          refine ⟨14721167112485019945136453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19628222816646693260181937 14721167112485019945136453)
          ·
            refine ⟨2760218833590941239713085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14721167112485019945136453 2760218833590941239713085)
            ·
              refine ⟨1035082062596602964892407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2760218833590941239713085 1035082062596602964892407)
              ·
                refine ⟨1552623093894904447338611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1035082062596602964892407 1552623093894904447338611)
                ·
                  refine ⟨2328934640842356671007917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552623093894904447338611 2328934640842356671007917)
                  ·
                    refine ⟨873350490315883751627969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2328934640842356671007917 873350490315883751627969)
                    ·
                      refine ⟨655012867736912813720977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 873350490315883751627969 655012867736912813720977)
                      ·
                        rfl

theorem cell23_1275633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_1275633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275633 prefixEnd_1275633 := by exact prefixLift 1275633
  have htrace : WordTrace (prefixWord ++ tailWord_1275633) baseStart_1275633 baseEnd_1275633 := by
    simpa [prefixWord, tailWord_1275633, baseEnd_1275633] using wordTrace_append hprefix tailTrace_1275633
  have hstable : (prefixWord ++ tailWord_1275633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275633).length < 2 ^ (prefixWord ++ tailWord_1275633).sum := by decide
  have hdescent : baseEnd_1275633 < baseStart_1275633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275642 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_1275642 : Nat := 118140960795 + 1275642 * 2 ^ 59
def prefixEnd_1275642 : Nat := 4983230072969 + 3 ^ 40 * 1275642 * 2
def baseEnd_1275642 : Nat := 655017489062803278508435

theorem tailTrace_1275642 : CollatzResearch.WordTrace tailWord_1275642 prefixEnd_1275642 655017489062803278508435 := by
  unfold tailWord_1275642
  simp only [CollatzResearch.WordTrace]
  refine ⟨11631621511143592788451295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31017657363049580769203453 11631621511143592788451295)
  ·
    refine ⟨17447432266715389182676943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11631621511143592788451295 17447432266715389182676943)
    ·
      refine ⟨26171148400073083774015415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17447432266715389182676943 26171148400073083774015415)
      ·
        refine ⟨39256722600109625661023123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26171148400073083774015415 39256722600109625661023123)
        ·
          refine ⟨58885083900164438491534685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39256722600109625661023123 58885083900164438491534685)
          ·
            refine ⟨22081906462561664434325507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58885083900164438491534685 22081906462561664434325507)
            ·
              refine ⟨33122859693842496651488261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22081906462561664434325507 33122859693842496651488261)
              ·
                refine ⟨6210536192595468122154049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33122859693842496651488261 6210536192595468122154049)
                ·
                  refine ⟨4657902144446601091615537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6210536192595468122154049 4657902144446601091615537)
                  ·
                    refine ⟨3493426608334950818711653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4657902144446601091615537 3493426608334950818711653)
                    ·
                      refine ⟨655017489062803278508435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3493426608334950818711653 655017489062803278508435)
                      ·
                        rfl

theorem cell23_1275642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_1275642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275642 prefixEnd_1275642 := by exact prefixLift 1275642
  have htrace : WordTrace (prefixWord ++ tailWord_1275642) baseStart_1275642 baseEnd_1275642 := by
    simpa [prefixWord, tailWord_1275642, baseEnd_1275642] using wordTrace_append hprefix tailTrace_1275642
  have hstable : (prefixWord ++ tailWord_1275642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275642).length < 2 ^ (prefixWord ++ tailWord_1275642).sum := by decide
  have hdescent : baseEnd_1275642 < baseStart_1275642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275756 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 3]
def baseStart_1275756 : Nat := 118140960795 + 1275756 * 2 ^ 59
def prefixEnd_1275756 : Nat := 4983230072969 + 3 ^ 40 * 1275756 * 2
def baseEnd_1275756 : Nat := 655076025857415832482911

theorem tailTrace_1275756 : CollatzResearch.WordTrace tailWord_1275756 prefixEnd_1275756 655076025857415832482911 := by
  unfold tailWord_1275756
  simp only [CollatzResearch.WordTrace]
  refine ⟨23265321983080684311727561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31020429310774245748970081 23265321983080684311727561)
  ·
    refine ⟨17448991487310513233795671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23265321983080684311727561 17448991487310513233795671)
    ·
      refine ⟨26173487230965769850693507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17448991487310513233795671 26173487230965769850693507)
      ·
        refine ⟨39260230846448654776040261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26173487230965769850693507 39260230846448654776040261)
        ·
          refine ⟨7361293283709122770507549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39260230846448654776040261 7361293283709122770507549)
          ·
            refine ⟨2760484981390921038940331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7361293283709122770507549 2760484981390921038940331)
            ·
              refine ⟨4140727472086381558410497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2760484981390921038940331 4140727472086381558410497)
              ·
                refine ⟨3105545604064786168807873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4140727472086381558410497 3105545604064786168807873)
                ·
                  refine ⟨2329159203048589626605905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3105545604064786168807873 2329159203048589626605905)
                  ·
                    refine ⟨1746869402286442219954429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2329159203048589626605905 1746869402286442219954429)
                    ·
                      refine ⟨655076025857415832482911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1746869402286442219954429 655076025857415832482911)
                      ·
                        rfl

theorem cell23_1275756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_1275756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275756 prefixEnd_1275756 := by exact prefixLift 1275756
  have htrace : WordTrace (prefixWord ++ tailWord_1275756) baseStart_1275756 baseEnd_1275756 := by
    simpa [prefixWord, tailWord_1275756, baseEnd_1275756] using wordTrace_append hprefix tailTrace_1275756
  have hstable : (prefixWord ++ tailWord_1275756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275756).length < 2 ^ (prefixWord ++ tailWord_1275756).sum := by decide
  have hdescent : baseEnd_1275756 < baseStart_1275756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275772 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 1, 11]
def baseStart_1275772 : Nat := 118140960795 + 1275772 * 2 ^ 59
def prefixEnd_1275772 : Nat := 4983230072969 + 3 ^ 40 * 1275772 * 2
def baseEnd_1275772 : Nat := 218361413849295923294279

theorem tailTrace_1275772 : CollatzResearch.WordTrace tailWord_1275772 prefixEnd_1275772 218361413849295923294279 := by
  unfold tailWord_1275772
  simp only [CollatzResearch.WordTrace]
  refine ⟨23265613767051701678018785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31020818356068935570691713 23265613767051701678018785)
  ·
    refine ⟨17449210325288776258514089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23265613767051701678018785 17449210325288776258514089)
    ·
      refine ⟨13086907743966582193885567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17449210325288776258514089 13086907743966582193885567)
      ·
        refine ⟨19630361615949873290828351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13086907743966582193885567 19630361615949873290828351)
        ·
          refine ⟨29445542423924809936242527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19630361615949873290828351 29445542423924809936242527)
          ·
            refine ⟨44168313635887214904363791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29445542423924809936242527 44168313635887214904363791)
            ·
              refine ⟨66252470453830822356545687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44168313635887214904363791 66252470453830822356545687)
              ·
                refine ⟨99378705680746233534818531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66252470453830822356545687 99378705680746233534818531)
                ·
                  refine ⟨149068058521119350302227797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99378705680746233534818531 149068058521119350302227797)
                  ·
                    refine ⟨218361413849295923294279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 149068058521119350302227797 218361413849295923294279)
                    ·
                      rfl

theorem cell23_1275772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_1275772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275772 prefixEnd_1275772 := by exact prefixLift 1275772
  have htrace : WordTrace (prefixWord ++ tailWord_1275772) baseStart_1275772 baseEnd_1275772 := by
    simpa [prefixWord, tailWord_1275772, baseEnd_1275772] using wordTrace_append hprefix tailTrace_1275772
  have hstable : (prefixWord ++ tailWord_1275772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275772).length < 2 ^ (prefixWord ++ tailWord_1275772).sum := by decide
  have hdescent : baseEnd_1275772 < baseStart_1275772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275790 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1275790 : Nat := 118140960795 + 1275790 * 2 ^ 59
def prefixEnd_1275790 : Nat := 4983230072969 + 3 ^ 40 * 1275790 * 2
def baseEnd_1275790 : Nat := 655093484199668699457755

theorem tailTrace_1275790 : CollatzResearch.WordTrace tailWord_1275790 prefixEnd_1275790 655093484199668699457755 := by
  unfold tailWord_1275790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5816485506004774053774103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31021256032025461620128549 5816485506004774053774103)
  ·
    refine ⟨8724728259007161080661155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5816485506004774053774103 8724728259007161080661155)
    ·
      refine ⟨13087092388510741620991733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8724728259007161080661155 13087092388510741620991733)
      ·
        refine ⟨1226914911422882026967975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13087092388510741620991733 1226914911422882026967975)
        ·
          refine ⟨1840372367134323040451963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1226914911422882026967975 1840372367134323040451963)
          ·
            refine ⟨2760558550701484560677945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840372367134323040451963 2760558550701484560677945)
            ·
              refine ⟨2070418913026113420508459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2760558550701484560677945 2070418913026113420508459)
              ·
                refine ⟨3105628369539170130762689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2070418913026113420508459 3105628369539170130762689)
                ·
                  refine ⟨2329221277154377598072017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3105628369539170130762689 2329221277154377598072017)
                  ·
                    refine ⟨1746915957865783198554013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2329221277154377598072017 1746915957865783198554013)
                    ·
                      refine ⟨655093484199668699457755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1746915957865783198554013 655093484199668699457755)
                      ·
                        rfl

theorem cell23_1275790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1275790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275790 prefixEnd_1275790 := by exact prefixLift 1275790
  have htrace : WordTrace (prefixWord ++ tailWord_1275790) baseStart_1275790 baseEnd_1275790 := by
    simpa [prefixWord, tailWord_1275790, baseEnd_1275790] using wordTrace_append hprefix tailTrace_1275790
  have hstable : (prefixWord ++ tailWord_1275790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275790).length < 2 ^ (prefixWord ++ tailWord_1275790).sum := by decide
  have hdescent : baseEnd_1275790 < baseStart_1275790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275899 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 4]
def baseStart_1275899 : Nat := 118140960795 + 1275899 * 2 ^ 59
def prefixEnd_1275899 : Nat := 4983230072969 + 3 ^ 40 * 1275899 * 2
def baseEnd_1275899 : Nat := 655149453591008772994753

theorem tailTrace_1275899 : CollatzResearch.WordTrace tailWord_1275899 prefixEnd_1275899 655149453591008772994753 := by
  unfold tailWord_1275899
  simp only [CollatzResearch.WordTrace]
  refine ⟨46535859604643304045910751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31023906403095536030607167 46535859604643304045910751)
  ·
    refine ⟨69803789406964956068866127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46535859604643304045910751 69803789406964956068866127)
    ·
      refine ⟨104705684110447434103299191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69803789406964956068866127 104705684110447434103299191)
      ·
        refine ⟨157058526165671151154948787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104705684110447434103299191 157058526165671151154948787)
        ·
          refine ⟨235587789248506726732423181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157058526165671151154948787 235587789248506726732423181)
          ·
            refine ⟨88345420968190022524658693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235587789248506726732423181 88345420968190022524658693)
            ·
              refine ⟨16564766431535629223373505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88345420968190022524658693 16564766431535629223373505)
              ·
                refine ⟨12423574823651721917530129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16564766431535629223373505 12423574823651721917530129)
                ·
                  refine ⟨9317681117738791438147597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12423574823651721917530129 9317681117738791438147597)
                  ·
                    refine ⟨3494130419152046789305349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9317681117738791438147597 3494130419152046789305349)
                    ·
                      refine ⟨655149453591008772994753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3494130419152046789305349 655149453591008772994753)
                      ·
                        rfl

theorem cell23_1275899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 4].length) (baseStart_1275899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275899 prefixEnd_1275899 := by exact prefixLift 1275899
  have htrace : WordTrace (prefixWord ++ tailWord_1275899) baseStart_1275899 baseEnd_1275899 := by
    simpa [prefixWord, tailWord_1275899, baseEnd_1275899] using wordTrace_append hprefix tailTrace_1275899
  have hstable : (prefixWord ++ tailWord_1275899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275899).length < 2 ^ (prefixWord ++ tailWord_1275899).sum := by decide
  have hdescent : baseEnd_1275899 < baseStart_1275899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275917 : List Nat := [1, 7, 1, 2, 2, 1, 9]
def baseStart_1275917 : Nat := 118140960795 + 1275917 * 2 ^ 59
def prefixEnd_1275917 : Nat := 4983230072969 + 3 ^ 40 * 1275917 * 2
def baseEnd_1275917 : Nat := 8088378965960366698391

theorem tailTrace_1275917 : CollatzResearch.WordTrace tailWord_1275917 prefixEnd_1275917 8088378965960366698391 := by
  unfold tailWord_1275917
  simp only [CollatzResearch.WordTrace]
  refine ⟨46536516118578093120066005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31024344079052062080044003 46536516118578093120066005)
  ·
    refine ⟨1090699596529174057501547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 46536516118578093120066005 1090699596529174057501547)
    ·
      refine ⟨1636049394793761086252321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1090699596529174057501547 1636049394793761086252321)
      ·
        refine ⟨1227037046095320814689241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1636049394793761086252321 1227037046095320814689241)
        ·
          refine ⟨920277784571490611016931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1227037046095320814689241 920277784571490611016931)
          ·
            refine ⟨1380416676857235916525397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920277784571490611016931 1380416676857235916525397)
            ·
              refine ⟨8088378965960366698391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1380416676857235916525397 8088378965960366698391)
              ·
                rfl

theorem cell23_1275917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 9].length) (baseStart_1275917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275917 prefixEnd_1275917 := by exact prefixLift 1275917
  have htrace : WordTrace (prefixWord ++ tailWord_1275917) baseStart_1275917 baseEnd_1275917 := by
    simpa [prefixWord, tailWord_1275917, baseEnd_1275917] using wordTrace_append hprefix tailTrace_1275917
  have hstable : (prefixWord ++ tailWord_1275917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275917).length < 2 ^ (prefixWord ++ tailWord_1275917).sum := by decide
  have hdescent : baseEnd_1275917 < baseStart_1275917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275979 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 7]
def baseStart_1275979 : Nat := 118140960795 + 1275979 * 2 ^ 59
def prefixEnd_1275979 : Nat := 4983230072969 + 3 ^ 40 * 1275979 * 2
def baseEnd_1275979 : Nat := 655190532043368459994385

theorem tailTrace_1275979 : CollatzResearch.WordTrace tailWord_1275979 prefixEnd_1275979 655190532043368459994385 := by
  unfold tailWord_1275979
  simp only [CollatzResearch.WordTrace]
  refine ⟨46538777444353477708822991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31025851629568985139215327 46538777444353477708822991)
  ·
    refine ⟨69808166166530216563234487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46538777444353477708822991 69808166166530216563234487)
    ·
      refine ⟨104712249249795324844851731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69808166166530216563234487 104712249249795324844851731)
      ·
        refine ⟨157068373874692987267277597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104712249249795324844851731 157068373874692987267277597)
        ·
          refine ⟨58900640203009870225229099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157068373874692987267277597 58900640203009870225229099)
          ·
            refine ⟨88350960304514805337843649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58900640203009870225229099 88350960304514805337843649)
            ·
              refine ⟨66263220228386104003382737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88350960304514805337843649 66263220228386104003382737)
              ·
                refine ⟨49697415171289578002537053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66263220228386104003382737 49697415171289578002537053)
                ·
                  refine ⟨18636530689233591750951395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49697415171289578002537053 18636530689233591750951395)
                  ·
                    refine ⟨27954796033850387626427093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18636530689233591750951395 27954796033850387626427093)
                    ·
                      refine ⟨655190532043368459994385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27954796033850387626427093 655190532043368459994385)
                      ·
                        rfl

theorem cell23_1275979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 7].length) (baseStart_1275979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1275979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1275979 prefixEnd_1275979 := by exact prefixLift 1275979
  have htrace : WordTrace (prefixWord ++ tailWord_1275979) baseStart_1275979 baseEnd_1275979 := by
    simpa [prefixWord, tailWord_1275979, baseEnd_1275979] using wordTrace_append hprefix tailTrace_1275979
  have hstable : (prefixWord ++ tailWord_1275979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275979).length < 2 ^ (prefixWord ++ tailWord_1275979).sum := by decide
  have hdescent : baseEnd_1275979 < baseStart_1275979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276023 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 4]
def baseStart_1276023 : Nat := 118140960795 + 1276023 * 2 ^ 59
def prefixEnd_1276023 : Nat := 4983230072969 + 3 ^ 40 * 1276023 * 2
def baseEnd_1276023 : Nat := 655213125192166287844183

theorem tailTrace_1276023 : CollatzResearch.WordTrace tailWord_1276023 prefixEnd_1276023 655213125192166287844183 := by
  unfold tailWord_1276023
  simp only [CollatzResearch.WordTrace]
  refine ⟨46540382256194073223424723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31026921504129382148949815 46540382256194073223424723)
  ·
    refine ⟨69810573384291109835137085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46540382256194073223424723 69810573384291109835137085)
    ·
      refine ⟨26178965019109166188176407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69810573384291109835137085 26178965019109166188176407)
      ·
        refine ⟨39268447528663749282264611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26178965019109166188176407 39268447528663749282264611)
        ·
          refine ⟨58902671292995623923396917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39268447528663749282264611 58902671292995623923396917)
          ·
            refine ⟨5522125433718339742818461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58902671292995623923396917 5522125433718339742818461)
            ·
              refine ⟨2070797037644377403556923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5522125433718339742818461 2070797037644377403556923)
              ·
                refine ⟨3106195556466566105335385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2070797037644377403556923 3106195556466566105335385)
                ·
                  refine ⟨2329646667349924579001539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3106195556466566105335385 2329646667349924579001539)
                  ·
                    refine ⟨3494470001024886868502309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2329646667349924579001539 3494470001024886868502309)
                    ·
                      refine ⟨655213125192166287844183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3494470001024886868502309 655213125192166287844183)
                      ·
                        rfl

theorem cell23_1276023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_1276023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276023 prefixEnd_1276023 := by exact prefixLift 1276023
  have htrace : WordTrace (prefixWord ++ tailWord_1276023) baseStart_1276023 baseEnd_1276023 := by
    simpa [prefixWord, tailWord_1276023, baseEnd_1276023] using wordTrace_append hprefix tailTrace_1276023
  have hstable : (prefixWord ++ tailWord_1276023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276023).length < 2 ^ (prefixWord ++ tailWord_1276023).sum := by decide
  have hdescent : baseEnd_1276023 < baseStart_1276023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276036 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_1276036 : Nat := 118140960795 + 1276036 * 2 ^ 59
def prefixEnd_1276036 : Nat := 4983230072969 + 3 ^ 40 * 1276036 * 2
def baseEnd_1276036 : Nat := 655219800440674736981623

theorem tailTrace_1276036 : CollatzResearch.WordTrace tailWord_1276036 prefixEnd_1276036 655219800440674736981623 := by
  unfold tailWord_1276036
  simp only [CollatzResearch.WordTrace]
  refine ⟨23270428202573488221823981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31027237603431317629098641 23270428202573488221823981)
  ·
    refine ⟨8726410575965058083183993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23270428202573488221823981 8726410575965058083183993)
    ·
      refine ⟨6544807931973793562387995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8726410575965058083183993 6544807931973793562387995)
      ·
        refine ⟨9817211897960690343581993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6544807931973793562387995 9817211897960690343581993)
        ·
          refine ⟨7362908923470517757686495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9817211897960690343581993 7362908923470517757686495)
          ·
            refine ⟨11044363385205776636529743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7362908923470517757686495 11044363385205776636529743)
            ·
              refine ⟨16566545077808664954794615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11044363385205776636529743 16566545077808664954794615)
              ·
                refine ⟨24849817616712997432191923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16566545077808664954794615 24849817616712997432191923)
                ·
                  refine ⟨37274726425069496148287885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24849817616712997432191923 37274726425069496148287885)
                  ·
                    refine ⟨13978022409401061055607957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37274726425069496148287885 13978022409401061055607957)
                    ·
                      refine ⟨655219800440674736981623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13978022409401061055607957 655219800440674736981623)
                      ·
                        rfl

theorem cell23_1276036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_1276036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276036 prefixEnd_1276036 := by exact prefixLift 1276036
  have htrace : WordTrace (prefixWord ++ tailWord_1276036) baseStart_1276036 baseEnd_1276036 := by
    simpa [prefixWord, tailWord_1276036, baseEnd_1276036] using wordTrace_append hprefix tailTrace_1276036
  have hstable : (prefixWord ++ tailWord_1276036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276036).length < 2 ^ (prefixWord ++ tailWord_1276036).sum := by decide
  have hdescent : baseEnd_1276036 < baseStart_1276036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276040 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 2, 4, 2]
def baseStart_1276040 : Nat := 118140960795 + 1276040 * 2 ^ 59
def prefixEnd_1276040 : Nat := 4983230072969 + 3 ^ 40 * 1276040 * 2
def baseEnd_1276040 : Nat := 655221854363292721331605

theorem tailTrace_1276040 : CollatzResearch.WordTrace tailWord_1276040 prefixEnd_1276040 655221854363292721331605 := by
  unfold tailWord_1276040
  simp only [CollatzResearch.WordTrace]
  refine ⟨23270501148566242563396787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31027334864754990084529049 23270501148566242563396787)
  ·
    refine ⟨34905751722849363845095181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23270501148566242563396787 34905751722849363845095181)
    ·
      refine ⟨13089656896068511441910693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34905751722849363845095181 13089656896068511441910693)
      ·
        refine ⟨2454310668012845895358255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13089656896068511441910693 2454310668012845895358255)
        ·
          refine ⟨3681466002019268843037383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454310668012845895358255 3681466002019268843037383)
          ·
            refine ⟨5522199003028903264556075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3681466002019268843037383 5522199003028903264556075)
            ·
              refine ⟨8283298504543354896834113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5522199003028903264556075 8283298504543354896834113)
              ·
                refine ⟨6212473878407516172625585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8283298504543354896834113 6212473878407516172625585)
                ·
                  refine ⟨4659355408805637129469189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6212473878407516172625585 4659355408805637129469189)
                  ·
                    refine ⟨873629139151056961775473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4659355408805637129469189 873629139151056961775473)
                    ·
                      refine ⟨655221854363292721331605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 873629139151056961775473 655221854363292721331605)
                      ·
                        rfl

theorem cell23_1276040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_1276040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276040 prefixEnd_1276040 := by exact prefixLift 1276040
  have htrace : WordTrace (prefixWord ++ tailWord_1276040) baseStart_1276040 baseEnd_1276040 := by
    simpa [prefixWord, tailWord_1276040, baseEnd_1276040] using wordTrace_append hprefix tailTrace_1276040
  have hstable : (prefixWord ++ tailWord_1276040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276040).length < 2 ^ (prefixWord ++ tailWord_1276040).sum := by decide
  have hdescent : baseEnd_1276040 < baseStart_1276040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276050 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_1276050 : Nat := 118140960795 + 1276050 * 2 ^ 59
def prefixEnd_1276050 : Nat := 4983230072969 + 3 ^ 40 * 1276050 * 2
def baseEnd_1276050 : Nat := 218408996389945894068853

theorem tailTrace_1276050 : CollatzResearch.WordTrace tailWord_1276050 prefixEnd_1276050 218408996389945894068853 := by
  unfold tailWord_1276050
  simp only [CollatzResearch.WordTrace]
  refine ⟨11635341756774064208664401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31027578018064171223105069 11635341756774064208664401)
  ·
    refine ⟨8726506317580548156498301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11635341756774064208664401 8726506317580548156498301)
    ·
      refine ⟨3272439869092705558686863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8726506317580548156498301 3272439869092705558686863)
      ·
        refine ⟨4908659803639058338030295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3272439869092705558686863 4908659803639058338030295)
        ·
          refine ⟨7362989705458587507045443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4908659803639058338030295 7362989705458587507045443)
          ·
            refine ⟨11044484558187881260568165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7362989705458587507045443 11044484558187881260568165)
            ·
              refine ⟨2070840854660227736356531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11044484558187881260568165 2070840854660227736356531)
              ·
                refine ⟨3106261281990341604534797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2070840854660227736356531 3106261281990341604534797)
                ·
                  refine ⟨1164847980746378101700549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3106261281990341604534797 1164847980746378101700549)
                  ·
                    refine ⟨218408996389945894068853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1164847980746378101700549 218408996389945894068853)
                    ·
                      rfl

theorem cell23_1276050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_1276050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276050 prefixEnd_1276050 := by exact prefixLift 1276050
  have htrace : WordTrace (prefixWord ++ tailWord_1276050) baseStart_1276050 baseEnd_1276050 := by
    simpa [prefixWord, tailWord_1276050, baseEnd_1276050] using wordTrace_append hprefix tailTrace_1276050
  have hstable : (prefixWord ++ tailWord_1276050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276050).length < 2 ^ (prefixWord ++ tailWord_1276050).sum := by decide
  have hdescent : baseEnd_1276050 < baseStart_1276050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276076 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 7, 5]
def baseStart_1276076 : Nat := 118140960795 + 1276076 * 2 ^ 59
def prefixEnd_1276076 : Nat := 4983230072969 + 3 ^ 40 * 1276076 * 2
def baseEnd_1276076 : Nat := 218413446555618193493813

theorem tailTrace_1276076 : CollatzResearch.WordTrace tailWord_1276076 prefixEnd_1276076 218413446555618193493813 := by
  unfold tailWord_1276076
  simp only [CollatzResearch.WordTrace]
  refine ⟨23271157662501031637552041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31028210216668042183402721 23271157662501031637552041)
  ·
    refine ⟨17453368246875773728164031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23271157662501031637552041 17453368246875773728164031)
    ·
      refine ⟨26180052370313660592246047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17453368246875773728164031 26180052370313660592246047)
      ·
        refine ⟨39270078555470490888369071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26180052370313660592246047 39270078555470490888369071)
        ·
          refine ⟨58905117833205736332553607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39270078555470490888369071 58905117833205736332553607)
          ·
            refine ⟨88357676749808604498830411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58905117833205736332553607 88357676749808604498830411)
            ·
              refine ⟨132536515124712906748245617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88357676749808604498830411 132536515124712906748245617)
              ·
                refine ⟨99402386343534680061184213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132536515124712906748245617 99402386343534680061184213)
                ·
                  refine ⟨2329743429926594063934005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 99402386343534680061184213 2329743429926594063934005)
                  ·
                    refine ⟨218413446555618193493813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2329743429926594063934005 218413446555618193493813)
                    ·
                      rfl

theorem cell23_1276076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_1276076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276076 prefixEnd_1276076 := by exact prefixLift 1276076
  have htrace : WordTrace (prefixWord ++ tailWord_1276076) baseStart_1276076 baseEnd_1276076 := by
    simpa [prefixWord, tailWord_1276076, baseEnd_1276076] using wordTrace_append hprefix tailTrace_1276076
  have hstable : (prefixWord ++ tailWord_1276076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276076).length < 2 ^ (prefixWord ++ tailWord_1276076).sum := by decide
  have hdescent : baseEnd_1276076 < baseStart_1276076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276143 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 4]
def baseStart_1276143 : Nat := 118140960795 + 1276143 * 2 ^ 59
def prefixEnd_1276143 : Nat := 4983230072969 + 3 ^ 40 * 1276143 * 2
def baseEnd_1276143 : Nat := 655274742870705818343631

theorem tailTrace_1276143 : CollatzResearch.WordTrace tailWord_1276143 prefixEnd_1276143 655274742870705818343631 := by
  unfold tailWord_1276143
  simp only [CollatzResearch.WordTrace]
  refine ⟨46544759015759333717793083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31029839343839555811862055 46544759015759333717793083)
  ·
    refine ⟨69817138523639000576689625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46544759015759333717793083 69817138523639000576689625)
    ·
      refine ⟨52362853892729250432517219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69817138523639000576689625 52362853892729250432517219)
      ·
        refine ⟨78544280839093875648775829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52362853892729250432517219 78544280839093875648775829)
        ·
          refine ⟨3681763164332525421036367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78544280839093875648775829 3681763164332525421036367)
          ·
            refine ⟨5522644746498788131554551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3681763164332525421036367 5522644746498788131554551)
            ·
              refine ⟨8283967119748182197331827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5522644746498788131554551 8283967119748182197331827)
              ·
                refine ⟨12425950679622273295997741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8283967119748182197331827 12425950679622273295997741)
                ·
                  refine ⟨4659731504858352485999153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12425950679622273295997741 4659731504858352485999153)
                  ·
                    refine ⟨3494798628643764364499365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4659731504858352485999153 3494798628643764364499365)
                    ·
                      refine ⟨655274742870705818343631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3494798628643764364499365 655274742870705818343631)
                      ·
                        rfl

theorem cell23_1276143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_1276143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276143 prefixEnd_1276143 := by exact prefixLift 1276143
  have htrace : WordTrace (prefixWord ++ tailWord_1276143) baseStart_1276143 baseEnd_1276143 := by
    simpa [prefixWord, tailWord_1276143, baseEnd_1276143] using wordTrace_append hprefix tailTrace_1276143
  have hstable : (prefixWord ++ tailWord_1276143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276143).length < 2 ^ (prefixWord ++ tailWord_1276143).sum := by decide
  have hdescent : baseEnd_1276143 < baseStart_1276143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276150 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_1276150 : Nat := 118140960795 + 1276150 * 2 ^ 59
def prefixEnd_1276150 : Nat := 4983230072969 + 3 ^ 40 * 1276150 * 2
def baseEnd_1276150 : Nat := 655278337235287290956099

theorem tailTrace_1276150 : CollatzResearch.WordTrace tailWord_1276150 prefixEnd_1276150 655278337235287290956099 := by
  unfold tailWord_1276150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2909063395420873369581119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31030009551155982608865269 2909063395420873369581119)
  ·
    refine ⟨4363595093131310054371679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2909063395420873369581119 4363595093131310054371679)
    ·
      refine ⟨6545392639696965081557519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4363595093131310054371679 6545392639696965081557519)
      ·
        refine ⟨9818088959545447622336279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6545392639696965081557519 9818088959545447622336279)
        ·
          refine ⟨14727133439318171433504419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9818088959545447622336279 14727133439318171433504419)
          ·
            refine ⟨22090700158977257150256629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14727133439318171433504419 22090700158977257150256629)
            ·
              refine ⟨2071003139904117857836559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22090700158977257150256629 2071003139904117857836559)
              ·
                refine ⟨3106504709856176786754839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2071003139904117857836559 3106504709856176786754839)
                ·
                  refine ⟨4659757064784265180132259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3106504709856176786754839 4659757064784265180132259)
                  ·
                    refine ⟨6989635597176397770198389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4659757064784265180132259 6989635597176397770198389)
                    ·
                      refine ⟨655278337235287290956099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6989635597176397770198389 655278337235287290956099)
                      ·
                        rfl

theorem cell23_1276150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_1276150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276150 prefixEnd_1276150 := by exact prefixLift 1276150
  have htrace : WordTrace (prefixWord ++ tailWord_1276150) baseStart_1276150 baseEnd_1276150 := by
    simpa [prefixWord, tailWord_1276150, baseEnd_1276150] using wordTrace_append hprefix tailTrace_1276150
  have hstable : (prefixWord ++ tailWord_1276150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276150).length < 2 ^ (prefixWord ++ tailWord_1276150).sum := by decide
  have hdescent : baseEnd_1276150 < baseStart_1276150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276163 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 3]
def baseStart_1276163 : Nat := 118140960795 + 1276163 * 2 ^ 59
def prefixEnd_1276163 : Nat := 4983230072969 + 3 ^ 40 * 1276163 * 2
def baseEnd_1276163 : Nat := 655285012483795740093539

theorem tailTrace_1276163 : CollatzResearch.WordTrace tailWord_1276163 prefixEnd_1276163 655285012483795740093539 := by
  unfold tailWord_1276163
  simp only [CollatzResearch.WordTrace]
  refine ⟨46545488475686877133521143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31030325650457918089014095 46545488475686877133521143)
  ·
    refine ⟨69818232713530315700281715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46545488475686877133521143 69818232713530315700281715)
    ·
      refine ⟨104727349070295473550422573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69818232713530315700281715 104727349070295473550422573)
      ·
        refine ⟨39272755901360802581408465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104727349070295473550422573 39272755901360802581408465)
        ·
          refine ⟨29454566926020601936056349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39272755901360802581408465 29454566926020601936056349)
          ·
            refine ⟨11045462597257725726021131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29454566926020601936056349 11045462597257725726021131)
            ·
              refine ⟨16568193895886588589031697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11045462597257725726021131 16568193895886588589031697)
              ·
                refine ⟨12426145421914941441773773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16568193895886588589031697 12426145421914941441773773)
                ·
                  refine ⟨4659804533218103040665165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12426145421914941441773773 4659804533218103040665165)
                  ·
                    refine ⟨1747426699956788640249437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4659804533218103040665165 1747426699956788640249437)
                    ·
                      refine ⟨655285012483795740093539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1747426699956788640249437 655285012483795740093539)
                      ·
                        rfl

theorem cell23_1276163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_1276163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276163 prefixEnd_1276163 := by exact prefixLift 1276163
  have htrace : WordTrace (prefixWord ++ tailWord_1276163) baseStart_1276163 baseEnd_1276163 := by
    simpa [prefixWord, tailWord_1276163, baseEnd_1276163] using wordTrace_append hprefix tailTrace_1276163
  have hstable : (prefixWord ++ tailWord_1276163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276163).length < 2 ^ (prefixWord ++ tailWord_1276163).sum := by decide
  have hdescent : baseEnd_1276163 < baseStart_1276163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276213 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 4, 6]
def baseStart_1276213 : Nat := 118140960795 + 1276213 * 2 ^ 59
def prefixEnd_1276213 : Nat := 4983230072969 + 3 ^ 40 * 1276213 * 2
def baseEnd_1276213 : Nat := 218436895505506848156103

theorem tailTrace_1276213 : CollatzResearch.WordTrace tailWord_1276213 prefixEnd_1276213 218436895505506848156103 := by
  unfold tailWord_1276213
  simp only [CollatzResearch.WordTrace]
  refine ⟨46547312125505735672841293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31031541417003823781894195 46547312125505735672841293)
  ·
    refine ⟨17455242047064650877315485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46547312125505735672841293 17455242047064650877315485)
    ·
      refine ⟨6545715767649244078993307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17455242047064650877315485 6545715767649244078993307)
      ·
        refine ⟨9818573651473866118489961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6545715767649244078993307 9818573651473866118489961)
        ·
          refine ⟨7363930238605399588867471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9818573651473866118489961 7363930238605399588867471)
          ·
            refine ⟨11045895357908099383301207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7363930238605399588867471 11045895357908099383301207)
            ·
              refine ⟨16568843036862149074951811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11045895357908099383301207 16568843036862149074951811)
              ·
                refine ⟨24853264555293223612427717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16568843036862149074951811 24853264555293223612427717)
                ·
                  refine ⟨4659987104117479427330197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24853264555293223612427717 4659987104117479427330197)
                  ·
                    refine ⟨218436895505506848156103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4659987104117479427330197 218436895505506848156103)
                    ·
                      rfl

theorem cell23_1276213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_1276213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276213 prefixEnd_1276213 := by exact prefixLift 1276213
  have htrace : WordTrace (prefixWord ++ tailWord_1276213) baseStart_1276213 baseEnd_1276213 := by
    simpa [prefixWord, tailWord_1276213, baseEnd_1276213] using wordTrace_append hprefix tailTrace_1276213
  have hstable : (prefixWord ++ tailWord_1276213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276213).length < 2 ^ (prefixWord ++ tailWord_1276213).sum := by decide
  have hdescent : baseEnd_1276213 < baseStart_1276213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276277 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 7]
def baseStart_1276277 : Nat := 118140960795 + 1276277 * 2 ^ 59
def prefixEnd_1276277 : Nat := 4983230072969 + 3 ^ 40 * 1276277 * 2
def baseEnd_1276277 : Nat := 72815949919823143785335

theorem tailTrace_1276277 : CollatzResearch.WordTrace tailWord_1276277 prefixEnd_1276277 72815949919823143785335 := by
  unfold tailWord_1276277
  simp only [CollatzResearch.WordTrace]
  refine ⟨46549646397273874603171085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31033097598182583068780723 46549646397273874603171085)
  ·
    refine ⟨17456117398977702976189157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46549646397273874603171085 17456117398977702976189157)
    ·
      refine ⟨3273022012308319308035467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17456117398977702976189157 3273022012308319308035467)
      ·
        refine ⟨4909533018462478962053201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3273022012308319308035467 4909533018462478962053201)
        ·
          refine ⟨3682149763846859221539901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4909533018462478962053201 3682149763846859221539901)
          ·
            refine ⟨1380806161442572208077463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3682149763846859221539901 1380806161442572208077463)
            ·
              refine ⟨2071209242163858312116195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380806161442572208077463 2071209242163858312116195)
              ·
                refine ⟨3106813863245787468174293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2071209242163858312116195 3106813863245787468174293)
                ·
                  refine ⟨72815949919823143785335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3106813863245787468174293 72815949919823143785335)
                  ·
                    rfl

theorem cell23_1276277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 7].length) (baseStart_1276277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276277 prefixEnd_1276277 := by exact prefixLift 1276277
  have htrace : WordTrace (prefixWord ++ tailWord_1276277) baseStart_1276277 baseEnd_1276277 := by
    simpa [prefixWord, tailWord_1276277, baseEnd_1276277] using wordTrace_append hprefix tailTrace_1276277
  have hstable : (prefixWord ++ tailWord_1276277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276277).length < 2 ^ (prefixWord ++ tailWord_1276277).sum := by decide
  have hdescent : baseEnd_1276277 < baseStart_1276277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276283 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 7]
def baseStart_1276283 : Nat := 118140960795 + 1276283 * 2 ^ 59
def prefixEnd_1276283 : Nat := 4983230072969 + 3 ^ 40 * 1276283 * 2
def baseEnd_1276283 : Nat := 655346630162335270592987

theorem tailTrace_1276283 : CollatzResearch.WordTrace tailWord_1276283 prefixEnd_1276283 655346630162335270592987 := by
  unfold tailWord_1276283
  simp only [CollatzResearch.WordTrace]
  refine ⟨46549865235252137627889503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31033243490168091751926335 46549865235252137627889503)
  ·
    refine ⟨69824797852878206441834255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46549865235252137627889503 69824797852878206441834255)
    ·
      refine ⟨104737196779317309662751383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69824797852878206441834255 104737196779317309662751383)
      ·
        refine ⟨157105795168975964494127075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104737196779317309662751383 157105795168975964494127075)
        ·
          refine ⟨235658692753463946741190613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157105795168975964494127075 235658692753463946741190613)
          ·
            refine ⟨5523250611409311251746655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 235658692753463946741190613 5523250611409311251746655)
            ·
              refine ⟨8284875917113966877619983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5523250611409311251746655 8284875917113966877619983)
              ·
                refine ⟨12427313875670950316429975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8284875917113966877619983 12427313875670950316429975)
                ·
                  refine ⟨18640970813506425474644963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12427313875670950316429975 18640970813506425474644963)
                  ·
                    refine ⟨27961456220259638211967445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18640970813506425474644963 27961456220259638211967445)
                    ·
                      refine ⟨655346630162335270592987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27961456220259638211967445 655346630162335270592987)
                      ·
                        rfl

theorem cell23_1276283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 7].length) (baseStart_1276283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276283 prefixEnd_1276283 := by exact prefixLift 1276283
  have htrace : WordTrace (prefixWord ++ tailWord_1276283) baseStart_1276283 baseEnd_1276283 := by
    simpa [prefixWord, tailWord_1276283, baseEnd_1276283] using wordTrace_append hprefix tailTrace_1276283
  have hstable : (prefixWord ++ tailWord_1276283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276283).length < 2 ^ (prefixWord ++ tailWord_1276283).sum := by decide
  have hdescent : baseEnd_1276283 < baseStart_1276283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276327 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1276327 : Nat := 118140960795 + 1276327 * 2 ^ 59
def prefixEnd_1276327 : Nat := 4983230072969 + 3 ^ 40 * 1276327 * 2
def baseEnd_1276327 : Nat := 655369223311133098442785

theorem tailTrace_1276327 : CollatzResearch.WordTrace tailWord_1276327 prefixEnd_1276327 655369223311133098442785 := by
  unfold tailWord_1276327
  simp only [CollatzResearch.WordTrace]
  refine ⟨46551470047092733142491235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31034313364728488761660823 46551470047092733142491235)
  ·
    refine ⟨69827205070639099713736853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46551470047092733142491235 69827205070639099713736853)
    ·
      refine ⟨3273150237686207799081415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69827205070639099713736853 3273150237686207799081415)
      ·
        refine ⟨4909725356529311698622123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3273150237686207799081415 4909725356529311698622123)
        ·
          refine ⟨7364588034793967547933185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4909725356529311698622123 7364588034793967547933185)
          ·
            refine ⟨5523441026095475660949889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7364588034793967547933185 5523441026095475660949889)
            ·
              refine ⟨4142580769571606745712417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5523441026095475660949889 4142580769571606745712417)
              ·
                refine ⟨3106935577178705059284313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4142580769571606745712417 3106935577178705059284313)
                ·
                  refine ⟨2330201682884028794463235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3106935577178705059284313 2330201682884028794463235)
                  ·
                    refine ⟨3495302524326043191694853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2330201682884028794463235 3495302524326043191694853)
                    ·
                      refine ⟨655369223311133098442785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3495302524326043191694853 655369223311133098442785)
                      ·
                        rfl

theorem cell23_1276327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1276327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276327 prefixEnd_1276327 := by exact prefixLift 1276327
  have htrace : WordTrace (prefixWord ++ tailWord_1276327) baseStart_1276327 baseEnd_1276327 := by
    simpa [prefixWord, tailWord_1276327, baseEnd_1276327] using wordTrace_append hprefix tailTrace_1276327
  have hstable : (prefixWord ++ tailWord_1276327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276327).length < 2 ^ (prefixWord ++ tailWord_1276327).sum := by decide
  have hdescent : baseEnd_1276327 < baseStart_1276327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276377 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 5, 1, 3]
def baseStart_1276377 : Nat := 118140960795 + 1276377 * 2 ^ 59
def prefixEnd_1276377 : Nat := 4983230072969 + 3 ^ 40 * 1276377 * 2
def baseEnd_1276377 : Nat := 655394897343857902817555

theorem tailTrace_1276377 : CollatzResearch.WordTrace tailWord_1276377 prefixEnd_1276377 655394897343857902817555 := by
  unfold tailWord_1276377
  simp only [CollatzResearch.WordTrace]
  refine ⟨46553293696911591681811385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31035529131274394454540923 46553293696911591681811385)
  ·
    refine ⟨34914970272683693761358539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46553293696911591681811385 34914970272683693761358539)
    ·
      refine ⟨52372455409025540642037809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34914970272683693761358539 52372455409025540642037809)
      ·
        refine ⟨39279341556769155481528357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52372455409025540642037809 39279341556769155481528357)
        ·
          refine ⟨7364876541894216652786567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39279341556769155481528357 7364876541894216652786567)
          ·
            refine ⟨11047314812841324979179851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7364876541894216652786567 11047314812841324979179851)
            ·
              refine ⟨16570972219261987468769777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11047314812841324979179851 16570972219261987468769777)
              ·
                refine ⟨12428229164446490601577333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16570972219261987468769777 12428229164446490601577333)
                ·
                  refine ⟨1165146484166858493897875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12428229164446490601577333 1165146484166858493897875)
                  ·
                    refine ⟨1747719726250287740846813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1165146484166858493897875 1747719726250287740846813)
                    ·
                      refine ⟨655394897343857902817555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1747719726250287740846813 655394897343857902817555)
                      ·
                        rfl

theorem cell23_1276377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_1276377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276377 prefixEnd_1276377 := by exact prefixLift 1276377
  have htrace : WordTrace (prefixWord ++ tailWord_1276377) baseStart_1276377 baseEnd_1276377 := by
    simpa [prefixWord, tailWord_1276377, baseEnd_1276377] using wordTrace_append hprefix tailTrace_1276377
  have hstable : (prefixWord ++ tailWord_1276377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276377).length < 2 ^ (prefixWord ++ tailWord_1276377).sum := by decide
  have hdescent : baseEnd_1276377 < baseStart_1276377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276394 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_1276394 : Nat := 118140960795 + 1276394 * 2 ^ 59
def prefixEnd_1276394 : Nat := 4983230072969 + 3 ^ 40 * 1276394 * 2
def baseEnd_1276394 : Nat := 655403626514984336304977

theorem tailTrace_1276394 : CollatzResearch.WordTrace tailWord_1276394 prefixEnd_1276394 655403626514984336304977 := by
  unfold tailWord_1276394
  simp only [CollatzResearch.WordTrace]
  refine ⟨11638478434462500896295059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31035942491900002390120157 11638478434462500896295059)
  ·
    refine ⟨17457717651693751344442589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11638478434462500896295059 17457717651693751344442589)
    ·
      refine ⟨6546644119385156754165971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17457717651693751344442589 6546644119385156754165971)
      ·
        refine ⟨9819966179077735131248957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6546644119385156754165971 9819966179077735131248957)
        ·
          refine ⟨3682487317154150674218359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9819966179077735131248957 3682487317154150674218359)
          ·
            refine ⟨5523730975731226011327539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3682487317154150674218359 5523730975731226011327539)
            ·
              refine ⟨8285596463596839016991309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5523730975731226011327539 8285596463596839016991309)
              ·
                refine ⟨3107098673848814631371741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8285596463596839016991309 3107098673848814631371741)
                ·
                  refine ⟨1165162002693305486764403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3107098673848814631371741 1165162002693305486764403)
                  ·
                    refine ⟨1747743004039958230146605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1165162002693305486764403 1747743004039958230146605)
                    ·
                      refine ⟨655403626514984336304977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1747743004039958230146605 655403626514984336304977)
                      ·
                        rfl

theorem cell23_1276394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_1276394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276394 prefixEnd_1276394 := by exact prefixLift 1276394
  have htrace : WordTrace (prefixWord ++ tailWord_1276394) baseStart_1276394 baseEnd_1276394 := by
    simpa [prefixWord, tailWord_1276394, baseEnd_1276394] using wordTrace_append hprefix tailTrace_1276394
  have hstable : (prefixWord ++ tailWord_1276394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276394).length < 2 ^ (prefixWord ++ tailWord_1276394).sum := by decide
  have hdescent : baseEnd_1276394 < baseStart_1276394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276410 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 1, 6]
def baseStart_1276410 : Nat := 118140960795 + 1276410 * 2 ^ 59
def prefixEnd_1276410 : Nat := 4983230072969 + 3 ^ 40 * 1276410 * 2
def baseEnd_1276410 : Nat := 218470614068485424568301

theorem tailTrace_1276410 : CollatzResearch.WordTrace tailWord_1276410 prefixEnd_1276410 218470614068485424568301 := by
  unfold tailWord_1276410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11638624326448009579440671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31036331537194692211841789 11638624326448009579440671)
  ·
    refine ⟨17457936489672014369161007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11638624326448009579440671 17457936489672014369161007)
    ·
      refine ⟨26186904734508021553741511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17457936489672014369161007 26186904734508021553741511)
      ·
        refine ⟨39280357101762032330612267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26186904734508021553741511 39280357101762032330612267)
        ·
          refine ⟨58920535652643048495918401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39280357101762032330612267 58920535652643048495918401)
          ·
            refine ⟨44190401739482286371938801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58920535652643048495918401 44190401739482286371938801)
            ·
              refine ⟨33142801304611714778954101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44190401739482286371938801 33142801304611714778954101)
              ·
                refine ⟨3107137622307348260526947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33142801304611714778954101 3107137622307348260526947)
                ·
                  refine ⟨4660706433461022390790421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3107137622307348260526947 4660706433461022390790421)
                  ·
                    refine ⟨218470614068485424568301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4660706433461022390790421 218470614068485424568301)
                    ·
                      rfl

theorem cell23_1276410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_1276410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276410 prefixEnd_1276410 := by exact prefixLift 1276410
  have htrace : WordTrace (prefixWord ++ tailWord_1276410) baseStart_1276410 baseEnd_1276410 := by
    simpa [prefixWord, tailWord_1276410, baseEnd_1276410] using wordTrace_append hprefix tailTrace_1276410
  have hstable : (prefixWord ++ tailWord_1276410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276410).length < 2 ^ (prefixWord ++ tailWord_1276410).sum := by decide
  have hdescent : baseEnd_1276410 < baseStart_1276410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276422 : List Nat := [6, 2, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1276422 : Nat := 118140960795 + 1276422 * 2 ^ 59
def prefixEnd_1276422 : Nat := 4983230072969 + 3 ^ 40 * 1276422 * 2
def baseEnd_1276422 : Nat := 218472667991103408918283

theorem tailTrace_1276422 : CollatzResearch.WordTrace tailWord_1276422 prefixEnd_1276422 218472667991103408918283 := by
  unfold tailWord_1276422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1454841718179642636474985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31036623321165709578133013 1454841718179642636474985)
  ·
    refine ⟨1091131288634731977356239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1454841718179642636474985 1091131288634731977356239)
    ·
      refine ⟨1636696932952097966034359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1091131288634731977356239 1636696932952097966034359)
      ·
        refine ⟨2455045399428146949051539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1636696932952097966034359 2455045399428146949051539)
        ·
          refine ⟨3682568099142220423577309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455045399428146949051539 3682568099142220423577309)
          ·
            refine ⟨1380963037178332658841491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3682568099142220423577309 1380963037178332658841491)
            ·
              refine ⟨2071444555767498988262237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380963037178332658841491 2071444555767498988262237)
              ·
                refine ⟨776791708412812120598339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2071444555767498988262237 776791708412812120598339)
                ·
                  refine ⟨1165187562619218180897509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776791708412812120598339 1165187562619218180897509)
                  ·
                    refine ⟨218472667991103408918283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1165187562619218180897509 218472667991103408918283)
                    ·
                      rfl

theorem cell23_1276422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1276422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276422 prefixEnd_1276422 := by exact prefixLift 1276422
  have htrace : WordTrace (prefixWord ++ tailWord_1276422) baseStart_1276422 baseEnd_1276422 := by
    simpa [prefixWord, tailWord_1276422, baseEnd_1276422] using wordTrace_append hprefix tailTrace_1276422
  have hstable : (prefixWord ++ tailWord_1276422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276422).length < 2 ^ (prefixWord ++ tailWord_1276422).sum := by decide
  have hdescent : baseEnd_1276422 < baseStart_1276422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276427 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 4, 4]
def baseStart_1276427 : Nat := 118140960795 + 1276427 * 2 ^ 59
def prefixEnd_1276427 : Nat := 4983230072969 + 3 ^ 40 * 1276427 * 2
def baseEnd_1276427 : Nat := 218473523792194235730775

theorem tailTrace_1276427 : CollatzResearch.WordTrace tailWord_1276427 prefixEnd_1276427 218473523792194235730775 := by
  unfold tailWord_1276427
  simp only [CollatzResearch.WordTrace]
  refine ⟨46555117346730450221131535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31036744897820300147421023 46555117346730450221131535)
  ·
    refine ⟨69832676020095675331697303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46555117346730450221131535 69832676020095675331697303)
    ·
      refine ⟨104749014030143512997545955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69832676020095675331697303 104749014030143512997545955)
      ·
        refine ⟨157123521045215269496318933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104749014030143512997545955 157123521045215269496318933)
        ·
          refine ⟨3682582524497232878819975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 157123521045215269496318933 3682582524497232878819975)
          ·
            refine ⟨5523873786745849318229963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3682582524497232878819975 5523873786745849318229963)
            ·
              refine ⟨8285810680118773977344945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5523873786745849318229963 8285810680118773977344945)
              ·
                refine ⟨6214358010089080483008709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8285810680118773977344945 6214358010089080483008709)
                ·
                  refine ⟨1165192126891702590564133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6214358010089080483008709 1165192126891702590564133)
                  ·
                    refine ⟨218473523792194235730775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1165192126891702590564133 218473523792194235730775)
                    ·
                      rfl

theorem cell23_1276427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 4].length) (baseStart_1276427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276427 prefixEnd_1276427 := by exact prefixLift 1276427
  have htrace : WordTrace (prefixWord ++ tailWord_1276427) baseStart_1276427 baseEnd_1276427 := by
    simpa [prefixWord, tailWord_1276427, baseEnd_1276427] using wordTrace_append hprefix tailTrace_1276427
  have hstable : (prefixWord ++ tailWord_1276427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276427).length < 2 ^ (prefixWord ++ tailWord_1276427).sum := by decide
  have hdescent : baseEnd_1276427 < baseStart_1276427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276428 : List Nat := [2, 2, 1, 2, 4, 3, 1, 3, 1, 1, 3]
def baseStart_1276428 : Nat := 118140960795 + 1276428 * 2 ^ 59
def prefixEnd_1276428 : Nat := 4983230072969 + 3 ^ 40 * 1276428 * 2
def baseEnd_1276428 : Nat := 655421084857237203279821

theorem tailTrace_1276428 : CollatzResearch.WordTrace tailWord_1276428 prefixEnd_1276428 655421084857237203279821 := by
  unfold tailWord_1276428
  simp only [CollatzResearch.WordTrace]
  refine ⟨23277576909863413695958969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31036769213151218261278625 23277576909863413695958969)
  ·
    refine ⟨17458182682397560271969227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23277576909863413695958969 17458182682397560271969227)
    ·
      refine ⟨26187274023596340407953841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17458182682397560271969227 26187274023596340407953841)
      ·
        refine ⟨19640455517697255305965381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26187274023596340407953841 19640455517697255305965381)
        ·
          refine ⟨3682585409568235369868509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19640455517697255305965381 3682585409568235369868509)
          ·
            refine ⟨1380969528588088263700691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3682585409568235369868509 1380969528588088263700691)
            ·
              refine ⟨2071454292882132395551037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380969528588088263700691 2071454292882132395551037)
              ·
                refine ⟨776795359830799648331639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2071454292882132395551037 776795359830799648331639)
                ·
                  refine ⟨1165193039746199472497459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776795359830799648331639 1165193039746199472497459)
                  ·
                    refine ⟨1747789559619299208746189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1165193039746199472497459 1747789559619299208746189)
                    ·
                      refine ⟨655421084857237203279821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1747789559619299208746189 655421084857237203279821)
                      ·
                        rfl

theorem cell23_1276428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_1276428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276428 prefixEnd_1276428 := by exact prefixLift 1276428
  have htrace : WordTrace (prefixWord ++ tailWord_1276428) baseStart_1276428 baseEnd_1276428 := by
    simpa [prefixWord, tailWord_1276428, baseEnd_1276428] using wordTrace_append hprefix tailTrace_1276428
  have hstable : (prefixWord ++ tailWord_1276428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276428).length < 2 ^ (prefixWord ++ tailWord_1276428).sum := by decide
  have hdescent : baseEnd_1276428 < baseStart_1276428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276437 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_1276437 : Nat := 118140960795 + 1276437 * 2 ^ 59
def prefixEnd_1276437 : Nat := 4983230072969 + 3 ^ 40 * 1276437 * 2
def baseEnd_1276437 : Nat := 655425706183127668067279

theorem tailTrace_1276437 : CollatzResearch.WordTrace tailWord_1276437 prefixEnd_1276437 655425706183127668067279 := by
  unfold tailWord_1276437
  simp only [CollatzResearch.WordTrace]
  refine ⟨46555482076694221928995565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31036988051129481285997043 46555482076694221928995565)
  ·
    refine ⟨17458305778760333223373337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46555482076694221928995565 17458305778760333223373337)
    ·
      refine ⟨13093729334070249917530003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17458305778760333223373337 13093729334070249917530003)
      ·
        refine ⟨19640594001105374876295005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13093729334070249917530003 19640594001105374876295005)
        ·
          refine ⟨7365222750414515578610627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19640594001105374876295005 7365222750414515578610627)
          ·
            refine ⟨11047834125621773367915941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7365222750414515578610627 11047834125621773367915941)
            ·
              refine ⟨2071468898554082506484239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11047834125621773367915941 2071468898554082506484239)
              ·
                refine ⟨3107203347831123759726359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2071468898554082506484239 3107203347831123759726359)
                ·
                  refine ⟨4660805021746685639589539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3107203347831123759726359 4660805021746685639589539)
                  ·
                    refine ⟨6991207532620028459384309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4660805021746685639589539 6991207532620028459384309)
                    ·
                      refine ⟨655425706183127668067279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6991207532620028459384309 655425706183127668067279)
                      ·
                        rfl

theorem cell23_1276437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_1276437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276437 prefixEnd_1276437 := by exact prefixLift 1276437
  have htrace : WordTrace (prefixWord ++ tailWord_1276437) baseStart_1276437 baseEnd_1276437 := by
    simpa [prefixWord, tailWord_1276437, baseEnd_1276437] using wordTrace_append hprefix tailTrace_1276437
  have hstable : (prefixWord ++ tailWord_1276437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276437).length < 2 ^ (prefixWord ++ tailWord_1276437).sum := by decide
  have hdescent : baseEnd_1276437 < baseStart_1276437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276440 : List Nat := [2, 1, 2, 3, 3, 1, 11]
def baseStart_1276440 : Nat := 118140960795 + 1276440 * 2 ^ 59
def prefixEnd_1276440 : Nat := 4983230072969 + 3 ^ 40 * 1276440 * 2
def baseEnd_1276440 : Nat := 8091694402778903164565

theorem tailTrace_1276440 : CollatzResearch.WordTrace tailWord_1276440 prefixEnd_1276440 8091694402778903164565 := by
  unfold tailWord_1276440
  simp only [CollatzResearch.WordTrace]
  refine ⟨23277795747841676720677387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31037060997122235627569849 23277795747841676720677387)
  ·
    refine ⟨34916693621762515081016081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23277795747841676720677387 34916693621762515081016081)
    ·
      refine ⟨26187520216321886310762061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34916693621762515081016081 26187520216321886310762061)
      ·
        refine ⟨9820320081120707366535773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26187520216321886310762061 9820320081120707366535773)
        ·
          refine ⟨3682620030420265262450915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9820320081120707366535773 3682620030420265262450915)
          ·
            refine ⟨5523930045630397893676373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3682620030420265262450915 5523930045630397893676373)
            ·
              refine ⟨8091694402778903164565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5523930045630397893676373 8091694402778903164565)
              ·
                rfl

theorem cell23_1276440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 11].length) (baseStart_1276440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276440 prefixEnd_1276440 := by exact prefixLift 1276440
  have htrace : WordTrace (prefixWord ++ tailWord_1276440) baseStart_1276440 baseEnd_1276440 := by
    simpa [prefixWord, tailWord_1276440, baseEnd_1276440] using wordTrace_append hprefix tailTrace_1276440
  have hstable : (prefixWord ++ tailWord_1276440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276440).length < 2 ^ (prefixWord ++ tailWord_1276440).sum := by decide
  have hdescent : baseEnd_1276440 < baseStart_1276440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276451 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 3, 2, 2]
def baseStart_1276451 : Nat := 118140960795 + 1276451 * 2 ^ 59
def prefixEnd_1276451 : Nat := 4983230072969 + 3 ^ 40 * 1276451 * 2
def baseEnd_1276451 : Nat := 655432894912290613292215

theorem tailTrace_1276451 : CollatzResearch.WordTrace tailWord_1276451 prefixEnd_1276451 655432894912290613292215 := by
  unfold tailWord_1276451
  simp only [CollatzResearch.WordTrace]
  refine ⟨46555992698643502320005207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31037328465762334880003471 46555992698643502320005207)
  ·
    refine ⟨69833989047965253480007811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46555992698643502320005207 69833989047965253480007811)
    ·
      refine ⟨104750983571947880220011717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69833989047965253480007811 104750983571947880220011717)
      ·
        refine ⟨19640809419740227541252197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104750983571947880220011717 19640809419740227541252197)
        ·
          refine ⟨3682651766201292663984787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19640809419740227541252197 3682651766201292663984787)
          ·
            refine ⟨5523977649301938995977181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3682651766201292663984787 5523977649301938995977181)
            ·
              refine ⟨2071491618488227123491443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5523977649301938995977181 2071491618488227123491443)
              ·
                refine ⟨3107237427732340685237165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2071491618488227123491443 3107237427732340685237165)
                ·
                  refine ⟨1165214035399627756963937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3107237427732340685237165 1165214035399627756963937)
                  ·
                    refine ⟨873910526549720817722953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1165214035399627756963937 873910526549720817722953)
                    ·
                      refine ⟨655432894912290613292215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 873910526549720817722953 655432894912290613292215)
                      ·
                        rfl

theorem cell23_1276451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_1276451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276451 prefixEnd_1276451 := by exact prefixLift 1276451
  have htrace : WordTrace (prefixWord ++ tailWord_1276451) baseStart_1276451 baseEnd_1276451 := by
    simpa [prefixWord, tailWord_1276451, baseEnd_1276451] using wordTrace_append hprefix tailTrace_1276451
  have hstable : (prefixWord ++ tailWord_1276451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276451).length < 2 ^ (prefixWord ++ tailWord_1276451).sum := by decide
  have hdescent : baseEnd_1276451 < baseStart_1276451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276467 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 3]
def baseStart_1276467 : Nat := 118140960795 + 1276467 * 2 ^ 59
def prefixEnd_1276467 : Nat := 4983230072969 + 3 ^ 40 * 1276467 * 2
def baseEnd_1276467 : Nat := 655441110602762550692141

theorem tailTrace_1276467 : CollatzResearch.WordTrace tailWord_1276467 prefixEnd_1276467 655441110602762550692141 := by
  unfold tailWord_1276467
  simp only [CollatzResearch.WordTrace]
  refine ⟨46556576266585537052587655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31037717511057024701725103 46556576266585537052587655)
  ·
    refine ⟨69834864399878305578881483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46556576266585537052587655 69834864399878305578881483)
    ·
      refine ⟨104752296599817458368322225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69834864399878305578881483 104752296599817458368322225)
      ·
        refine ⟨78564222449863093776241669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104752296599817458368322225 78564222449863093776241669)
        ·
          refine ⟨14730791709349330083045313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78564222449863093776241669 14730791709349330083045313)
          ·
            refine ⟨11048093782011997562283985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14730791709349330083045313 11048093782011997562283985)
            ·
              refine ⟨8286070336508998171712989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11048093782011997562283985 8286070336508998171712989)
              ·
                refine ⟨3107276376190874314392371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8286070336508998171712989 3107276376190874314392371)
                ·
                  refine ⟨4660914564286311471588557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3107276376190874314392371 4660914564286311471588557)
                  ·
                    refine ⟨1747842961607366801845709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4660914564286311471588557 1747842961607366801845709)
                    ·
                      refine ⟨655441110602762550692141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1747842961607366801845709 655441110602762550692141)
                      ·
                        rfl

theorem cell23_1276467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 3].length) (baseStart_1276467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276467 prefixEnd_1276467 := by exact prefixLift 1276467
  have htrace : WordTrace (prefixWord ++ tailWord_1276467) baseStart_1276467 baseEnd_1276467 := by
    simpa [prefixWord, tailWord_1276467, baseEnd_1276467] using wordTrace_append hprefix tailTrace_1276467
  have hstable : (prefixWord ++ tailWord_1276467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276467).length < 2 ^ (prefixWord ++ tailWord_1276467).sum := by decide
  have hdescent : baseEnd_1276467 < baseStart_1276467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276480 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 5]
def baseStart_1276480 : Nat := 118140960795 + 1276480 * 2 ^ 59
def prefixEnd_1276480 : Nat := 4983230072969 + 3 ^ 40 * 1276480 * 2
def baseEnd_1276480 : Nat := 655447785851270999829581

theorem tailTrace_1276480 : CollatzResearch.WordTrace tailWord_1276480 prefixEnd_1276480 655447785851270999829581 := by
  unfold tailWord_1276480
  simp only [CollatzResearch.WordTrace]
  refine ⟨23278525207769220136405447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31038033610358960181873929 23278525207769220136405447)
  ·
    refine ⟨34917787811653830204608171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23278525207769220136405447 34917787811653830204608171)
    ·
      refine ⟨52376681717480745306912257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34917787811653830204608171 52376681717480745306912257)
      ·
        refine ⟨39282511288110558980184193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52376681717480745306912257 39282511288110558980184193)
        ·
          refine ⟨29461883466082919235138145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39282511288110558980184193 29461883466082919235138145)
          ·
            refine ⟨22096412599562189426353609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29461883466082919235138145 22096412599562189426353609)
            ·
              refine ⟨16572309449671642069765207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22096412599562189426353609 16572309449671642069765207)
              ·
                refine ⟨24858464174507463104647811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16572309449671642069765207 24858464174507463104647811)
                ·
                  refine ⟨37287696261761194656971717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24858464174507463104647811 37287696261761194656971717)
                  ·
                    refine ⟨6991443049080223998182197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37287696261761194656971717 6991443049080223998182197)
                    ·
                      refine ⟨655447785851270999829581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6991443049080223998182197 655447785851270999829581)
                      ·
                        rfl

theorem cell23_1276480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_1276480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276480 prefixEnd_1276480 := by exact prefixLift 1276480
  have htrace : WordTrace (prefixWord ++ tailWord_1276480) baseStart_1276480 baseEnd_1276480 := by
    simpa [prefixWord, tailWord_1276480, baseEnd_1276480] using wordTrace_append hprefix tailTrace_1276480
  have hstable : (prefixWord ++ tailWord_1276480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276480).length < 2 ^ (prefixWord ++ tailWord_1276480).sum := by decide
  have hdescent : baseEnd_1276480 < baseStart_1276480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276524 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 1, 4, 2]
def baseStart_1276524 : Nat := 118140960795 + 1276524 * 2 ^ 59
def prefixEnd_1276524 : Nat := 4983230072969 + 3 ^ 40 * 1276524 * 2
def baseEnd_1276524 : Nat := 655470379000068827679379

theorem tailTrace_1276524 : CollatzResearch.WordTrace tailWord_1276524 prefixEnd_1276524 655470379000068827679379 := by
  unfold tailWord_1276524
  simp only [CollatzResearch.WordTrace]
  refine ⟨23279327613689517893706313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31039103484919357191608417 23279327613689517893706313)
  ·
    refine ⟨17459495710267138420279735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23279327613689517893706313 17459495710267138420279735)
    ·
      refine ⟨26189243565400707630419603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17459495710267138420279735 26189243565400707630419603)
      ·
        refine ⟨39283865348101061445629405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26189243565400707630419603 39283865348101061445629405)
        ·
          refine ⟨14731449505537898042111027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39283865348101061445629405 14731449505537898042111027)
          ·
            refine ⟨22097174258306847063166541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14731449505537898042111027 22097174258306847063166541)
            ·
              refine ⟨8286440346865067648687453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22097174258306847063166541 8286440346865067648687453)
              ·
                refine ⟨3107415130074400368257795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8286440346865067648687453 3107415130074400368257795)
                ·
                  refine ⟨4661122695111600552386693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3107415130074400368257795 4661122695111600552386693)
                  ·
                    refine ⟨873960505333425103572505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4661122695111600552386693 873960505333425103572505)
                    ·
                      refine ⟨655470379000068827679379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 873960505333425103572505 655470379000068827679379)
                      ·
                        rfl

theorem cell23_1276524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 4, 2].length) (baseStart_1276524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276524 prefixEnd_1276524 := by exact prefixLift 1276524
  have htrace : WordTrace (prefixWord ++ tailWord_1276524) baseStart_1276524 baseEnd_1276524 := by
    simpa [prefixWord, tailWord_1276524, baseEnd_1276524] using wordTrace_append hprefix tailTrace_1276524
  have hstable : (prefixWord ++ tailWord_1276524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276524).length < 2 ^ (prefixWord ++ tailWord_1276524).sum := by decide
  have hdescent : baseEnd_1276524 < baseStart_1276524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276564 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 7]
def baseStart_1276564 : Nat := 118140960795 + 1276564 * 2 ^ 59
def prefixEnd_1276564 : Nat := 4983230072969 + 3 ^ 40 * 1276564 * 2
def baseEnd_1276564 : Nat := 72832324247360963464355

theorem tailTrace_1276564 : CollatzResearch.WordTrace tailWord_1276564 prefixEnd_1276564 72832324247360963464355 := by
  unfold tailWord_1276564
  simp only [CollatzResearch.WordTrace]
  refine ⟨23280057073617061309434373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31040076098156081745912497 23280057073617061309434373)
  ·
    refine ⟨4365010701303198995518945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23280057073617061309434373 4365010701303198995518945)
    ·
      refine ⟨3273758025977399246639209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4365010701303198995518945 3273758025977399246639209)
      ·
        refine ⟨2455318519483049434979407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3273758025977399246639209 2455318519483049434979407)
        ·
          refine ⟨3682977779224574152469111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455318519483049434979407 3682977779224574152469111)
          ·
            refine ⟨5524466668836861228703667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3682977779224574152469111 5524466668836861228703667)
            ·
              refine ⟨8286700003255291843055501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5524466668836861228703667 8286700003255291843055501)
              ·
                refine ⟨3107512501220734441145813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8286700003255291843055501 3107512501220734441145813)
                ·
                  refine ⟨72832324247360963464355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3107512501220734441145813 72832324247360963464355)
                  ·
                    rfl

theorem cell23_1276564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_1276564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276564 prefixEnd_1276564 := by exact prefixLift 1276564
  have htrace : WordTrace (prefixWord ++ tailWord_1276564) baseStart_1276564 baseEnd_1276564 := by
    simpa [prefixWord, tailWord_1276564, baseEnd_1276564] using wordTrace_append hprefix tailTrace_1276564
  have hstable : (prefixWord ++ tailWord_1276564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276564).length < 2 ^ (prefixWord ++ tailWord_1276564).sum := by decide
  have hdescent : baseEnd_1276564 < baseStart_1276564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276617 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 2, 8, 3]
def baseStart_1276617 : Nat := 118140960795 + 1276617 * 2 ^ 59
def prefixEnd_1276617 : Nat := 4983230072969 + 3 ^ 40 * 1276617 * 2
def baseEnd_1276617 : Nat := 655518132700936963816451

theorem tailTrace_1276617 : CollatzResearch.WordTrace tailWord_1276617 prefixEnd_1276617 655518132700936963816451 := by
  unfold tailWord_1276617
  simp only [CollatzResearch.WordTrace]
  refine ⟨46562047216042112670548105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31041364810694741780365403 46562047216042112670548105)
  ·
    refine ⟨34921535412031584502911079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46562047216042112670548105 34921535412031584502911079)
    ·
      refine ⟨52382303118047376754366619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34921535412031584502911079 52382303118047376754366619)
      ·
        refine ⟨78573454677071065131549929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52382303118047376754366619 78573454677071065131549929)
        ·
          refine ⟨58930091007803298848662447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78573454677071065131549929 58930091007803298848662447)
          ·
            refine ⟨88395136511704948272993671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58930091007803298848662447 88395136511704948272993671)
            ·
              refine ⟨132592704767557422409490507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88395136511704948272993671 132592704767557422409490507)
              ·
                refine ⟨198889057151336133614235761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132592704767557422409490507 198889057151336133614235761)
                ·
                  refine ⟨149166792863502100210676821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198889057151336133614235761 149166792863502100210676821)
                  ·
                    refine ⟨1748048353869165236843869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 149166792863502100210676821 1748048353869165236843869)
                    ·
                      refine ⟨655518132700936963816451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1748048353869165236843869 655518132700936963816451)
                      ·
                        rfl

theorem cell23_1276617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 8, 3].length) (baseStart_1276617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276617 prefixEnd_1276617 := by exact prefixLift 1276617
  have htrace : WordTrace (prefixWord ++ tailWord_1276617) baseStart_1276617 baseEnd_1276617 := by
    simpa [prefixWord, tailWord_1276617, baseEnd_1276617] using wordTrace_append hprefix tailTrace_1276617
  have hstable : (prefixWord ++ tailWord_1276617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276617).length < 2 ^ (prefixWord ++ tailWord_1276617).sum := by decide
  have hdescent : baseEnd_1276617 < baseStart_1276617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276634 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3]
def baseStart_1276634 : Nat := 118140960795 + 1276634 * 2 ^ 59
def prefixEnd_1276634 : Nat := 4983230072969 + 3 ^ 40 * 1276634 * 2
def baseEnd_1276634 : Nat := 655526861872063397303873

theorem tailTrace_1276634 : CollatzResearch.WordTrace tailWord_1276634 prefixEnd_1276634 655526861872063397303873 := by
  unfold tailWord_1276634
  simp only [CollatzResearch.WordTrace]
  refine ⟨11640666814245131143479239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31041778171320349715944637 11640666814245131143479239)
  ·
    refine ⟨17461000221367696715218859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11640666814245131143479239 17461000221367696715218859)
    ·
      refine ⟨26191500332051545072828289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17461000221367696715218859 26191500332051545072828289)
      ·
        refine ⟨19643625249038658804621217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26191500332051545072828289 19643625249038658804621217)
        ·
          refine ⟨14732718936778994103465913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19643625249038658804621217 14732718936778994103465913)
          ·
            refine ⟨11049539202584245577599435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14732718936778994103465913 11049539202584245577599435)
            ·
              refine ⟨16574308803876368366399153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11049539202584245577599435 16574308803876368366399153)
              ·
                refine ⟨12430731602907276274799365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16574308803876368366399153 12430731602907276274799365)
                ·
                  refine ⟨2330762175545114301524881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12430731602907276274799365 2330762175545114301524881)
                  ·
                    refine ⟨1748071631658835726143661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2330762175545114301524881 1748071631658835726143661)
                    ·
                      refine ⟨655526861872063397303873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1748071631658835726143661 655526861872063397303873)
                      ·
                        rfl

theorem cell23_1276634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_1276634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276634 prefixEnd_1276634 := by exact prefixLift 1276634
  have htrace : WordTrace (prefixWord ++ tailWord_1276634) baseStart_1276634 baseEnd_1276634 := by
    simpa [prefixWord, tailWord_1276634, baseEnd_1276634] using wordTrace_append hprefix tailTrace_1276634
  have hstable : (prefixWord ++ tailWord_1276634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276634).length < 2 ^ (prefixWord ++ tailWord_1276634).sum := by decide
  have hdescent : baseEnd_1276634 < baseStart_1276634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276677 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_1276677 : Nat := 118140960795 + 1276677 * 2 ^ 59
def prefixEnd_1276677 : Nat := 4983230072969 + 3 ^ 40 * 1276677 * 2
def baseEnd_1276677 : Nat := 655548941540206729066175

theorem tailTrace_1276677 : CollatzResearch.WordTrace tailWord_1276677 prefixEnd_1276677 655548941540206729066175 := by
  unfold tailWord_1276677
  simp only [CollatzResearch.WordTrace]
  refine ⟨46564235595824742917732285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31042823730549828611821523 46564235595824742917732285)
  ·
    refine ⟨17461588348434278594149607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46564235595824742917732285 17461588348434278594149607)
    ·
      refine ⟨26192382522651417891224411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17461588348434278594149607 26192382522651417891224411)
      ·
        refine ⟨39288573783977126836836617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26192382522651417891224411 39288573783977126836836617)
        ·
          refine ⟨29466430337982845127627463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39288573783977126836836617 29466430337982845127627463)
          ·
            refine ⟨44199645506974267691441195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29466430337982845127627463 44199645506974267691441195)
            ·
              refine ⟨66299468260461401537161793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44199645506974267691441195 66299468260461401537161793)
              ·
                refine ⟨49724601195346051152871345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66299468260461401537161793 49724601195346051152871345)
                ·
                  refine ⟨37293450896509538364653509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49724601195346051152871345 37293450896509538364653509)
                  ·
                    refine ⟨6992522043095538443372533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37293450896509538364653509 6992522043095538443372533)
                    ·
                      refine ⟨655548941540206729066175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6992522043095538443372533 655548941540206729066175)
                      ·
                        rfl

theorem cell23_1276677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_1276677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276677 prefixEnd_1276677 := by exact prefixLift 1276677
  have htrace : WordTrace (prefixWord ++ tailWord_1276677) baseStart_1276677 baseEnd_1276677 := by
    simpa [prefixWord, tailWord_1276677, baseEnd_1276677] using wordTrace_append hprefix tailTrace_1276677
  have hstable : (prefixWord ++ tailWord_1276677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276677).length < 2 ^ (prefixWord ++ tailWord_1276677).sum := by decide
  have hdescent : baseEnd_1276677 < baseStart_1276677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276708 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 1, 5, 2]
def baseStart_1276708 : Nat := 118140960795 + 1276708 * 2 ^ 59
def prefixEnd_1276708 : Nat := 4983230072969 + 3 ^ 40 * 1276708 * 2
def baseEnd_1276708 : Nat := 655564859440496107778533

theorem tailTrace_1276708 : CollatzResearch.WordTrace tailWord_1276708 prefixEnd_1276708 655564859440496107778533 := by
  unfold tailWord_1276708
  simp only [CollatzResearch.WordTrace]
  refine ⟨23282683129356217606055389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31043577505808290141407185 23282683129356217606055389)
  ·
    refine ⟨8731006173508581602270771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23282683129356217606055389 8731006173508581602270771)
    ·
      refine ⟨13096509260262872403406157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8731006173508581602270771 13096509260262872403406157)
      ·
        refine ⟨4911190972598577151277309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13096509260262872403406157 4911190972598577151277309)
        ·
          refine ⟨1841696614724466431728991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4911190972598577151277309 1841696614724466431728991)
          ·
            refine ⟨2762544922086699647593487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841696614724466431728991 2762544922086699647593487)
            ·
              refine ⟨4143817383130049471390231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2762544922086699647593487 4143817383130049471390231)
              ·
                refine ⟨6215726074695074207085347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4143817383130049471390231 6215726074695074207085347)
                ·
                  refine ⟨9323589112042611310628021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6215726074695074207085347 9323589112042611310628021)
                  ·
                    refine ⟨874086479253994810371377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9323589112042611310628021 874086479253994810371377)
                    ·
                      refine ⟨655564859440496107778533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 874086479253994810371377 655564859440496107778533)
                      ·
                        rfl

theorem cell23_1276708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_1276708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276708 prefixEnd_1276708 := by exact prefixLift 1276708
  have htrace : WordTrace (prefixWord ++ tailWord_1276708) baseStart_1276708 baseEnd_1276708 := by
    simpa [prefixWord, tailWord_1276708, baseEnd_1276708] using wordTrace_append hprefix tailTrace_1276708
  have hstable : (prefixWord ++ tailWord_1276708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276708).length < 2 ^ (prefixWord ++ tailWord_1276708).sum := by decide
  have hdescent : baseEnd_1276708 < baseStart_1276708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276718 : List Nat := [4, 1, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_1276718 : Nat := 118140960795 + 1276718 * 2 ^ 59
def prefixEnd_1276718 : Nat := 4983230072969 + 3 ^ 40 * 1276718 * 2
def baseEnd_1276718 : Nat := 218523331415680356217829

theorem tailTrace_1276718 : CollatzResearch.WordTrace tailWord_1276718 prefixEnd_1276718 218523331415680356217829 := by
  unfold tailWord_1276718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5820716373584525864996851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31043820659117471279983205 5820716373584525864996851)
  ·
    refine ⟨8731074560376788797495277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5820716373584525864996851 8731074560376788797495277)
    ·
      refine ⟨3274152960141295799060729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8731074560376788797495277 3274152960141295799060729)
      ·
        refine ⟨2455614720105971849295547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3274152960141295799060729 2455614720105971849295547)
        ·
          refine ⟨3683422080158957773943321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455614720105971849295547 3683422080158957773943321)
          ·
            refine ⟨2762566560119218330457491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3683422080158957773943321 2762566560119218330457491)
            ·
              refine ⟨4143849840178827495686237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2762566560119218330457491 4143849840178827495686237)
              ·
                refine ⟨1553943690067060310882339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4143849840178827495686237 1553943690067060310882339)
                ·
                  refine ⟨2330915535100590466323509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553943690067060310882339 2330915535100590466323509)
                  ·
                    refine ⟨218523331415680356217829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2330915535100590466323509 218523331415680356217829)
                    ·
                      rfl

theorem cell23_1276718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_1276718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276718 prefixEnd_1276718 := by exact prefixLift 1276718
  have htrace : WordTrace (prefixWord ++ tailWord_1276718) baseStart_1276718 baseEnd_1276718 := by
    simpa [prefixWord, tailWord_1276718, baseEnd_1276718] using wordTrace_append hprefix tailTrace_1276718
  have hstable : (prefixWord ++ tailWord_1276718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276718).length < 2 ^ (prefixWord ++ tailWord_1276718).sum := by decide
  have hdescent : baseEnd_1276718 < baseStart_1276718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276721 : List Nat := [1, 2, 2, 3, 2, 1, 3, 3, 1, 1, 4]
def baseStart_1276721 : Nat := 118140960795 + 1276721 * 2 ^ 59
def prefixEnd_1276721 : Nat := 4983230072969 + 3 ^ 40 * 1276721 * 2
def baseEnd_1276721 : Nat := 655571534689004556915973

theorem tailTrace_1276721 : CollatzResearch.WordTrace tailWord_1276721 prefixEnd_1276721 655571534689004556915973 := by
  unfold tailWord_1276721
  simp only [CollatzResearch.WordTrace]
  refine ⟨46565840407665338432334017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31043893605110225621556011 46565840407665338432334017)
  ·
    refine ⟨34924380305749003824250513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46565840407665338432334017 34924380305749003824250513)
    ·
      refine ⟨26193285229311752868187885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34924380305749003824250513 26193285229311752868187885)
      ·
        refine ⟨9822481960991907325570457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26193285229311752868187885 9822481960991907325570457)
        ·
          refine ⟨7366861470743930494177843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9822481960991907325570457 7366861470743930494177843)
          ·
            refine ⟨11050292206115895741266765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7366861470743930494177843 11050292206115895741266765)
            ·
              refine ⟨4143859577293460902975037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11050292206115895741266765 4143859577293460902975037)
              ·
                refine ⟨1553947341485047838615639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4143859577293460902975037 1553947341485047838615639)
                ·
                  refine ⟨2330921012227571757923459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553947341485047838615639 2330921012227571757923459)
                  ·
                    refine ⟨3496381518341357636885189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2330921012227571757923459 3496381518341357636885189)
                    ·
                      refine ⟨655571534689004556915973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3496381518341357636885189 655571534689004556915973)
                      ·
                        rfl

theorem cell23_1276721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_1276721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276721 prefixEnd_1276721 := by exact prefixLift 1276721
  have htrace : WordTrace (prefixWord ++ tailWord_1276721) baseStart_1276721 baseEnd_1276721 := by
    simpa [prefixWord, tailWord_1276721, baseEnd_1276721] using wordTrace_append hprefix tailTrace_1276721
  have hstable : (prefixWord ++ tailWord_1276721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276721).length < 2 ^ (prefixWord ++ tailWord_1276721).sum := by decide
  have hdescent : baseEnd_1276721 < baseStart_1276721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276727 : List Nat := [1, 1, 3, 1, 2, 1, 14]
def baseStart_1276727 : Nat := 118140960795 + 1276727 * 2 ^ 59
def prefixEnd_1276727 : Nat := 4983230072969 + 3 ^ 40 * 1276727 * 2
def baseEnd_1276727 : Nat := 8093513772505327573345

theorem tailTrace_1276727 : CollatzResearch.WordTrace tailWord_1276727 prefixEnd_1276727 8093513772505327573345 := by
  unfold tailWord_1276727
  simp only [CollatzResearch.WordTrace]
  refine ⟨46566059245643601457052435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31044039497095734304701623 46566059245643601457052435)
  ·
    refine ⟨69849088868465402185578653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46566059245643601457052435 69849088868465402185578653)
    ·
      refine ⟨26193408325674525819591995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69849088868465402185578653 26193408325674525819591995)
      ·
        refine ⟨39290112488511788729387993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26193408325674525819591995 39290112488511788729387993)
        ·
          refine ⟨29467584366383841547040995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39290112488511788729387993 29467584366383841547040995)
          ·
            refine ⟨44201376549575762320561493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29467584366383841547040995 44201376549575762320561493)
            ·
              refine ⟨8093513772505327573345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 44201376549575762320561493 8093513772505327573345)
              ·
                rfl

theorem cell23_1276727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 14].length) (baseStart_1276727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276727 prefixEnd_1276727 := by exact prefixLift 1276727
  have htrace : WordTrace (prefixWord ++ tailWord_1276727) baseStart_1276727 baseEnd_1276727 := by
    simpa [prefixWord, tailWord_1276727, baseEnd_1276727] using wordTrace_append hprefix tailTrace_1276727
  have hstable : (prefixWord ++ tailWord_1276727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276727).length < 2 ^ (prefixWord ++ tailWord_1276727).sum := by decide
  have hdescent : baseEnd_1276727 < baseStart_1276727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276761 : List Nat := [1, 2, 1, 2, 2, 6, 2, 7]
def baseStart_1276761 : Nat := 118140960795 + 1276761 * 2 ^ 59
def prefixEnd_1276761 : Nat := 4983230072969 + 3 ^ 40 * 1276761 * 2
def baseEnd_1276761 : Nat := 24281187922784607422807

theorem tailTrace_1276761 : CollatzResearch.WordTrace tailWord_1276761 prefixEnd_1276761 24281187922784607422807 := by
  unfold tailWord_1276761
  simp only [CollatzResearch.WordTrace]
  refine ⟨46567299327520425263790137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31044866218346950175860091 46567299327520425263790137)
  ·
    refine ⟨34925474495640318947842603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46567299327520425263790137 34925474495640318947842603)
    ·
      refine ⟨52388211743460478421763905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34925474495640318947842603 52388211743460478421763905)
      ·
        refine ⟨39291158807595358816322929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52388211743460478421763905 39291158807595358816322929)
        ·
          refine ⟨29468369105696519112242197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39291158807595358816322929 29468369105696519112242197)
          ·
            refine ⟨1381329801829524333386353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29468369105696519112242197 1381329801829524333386353)
            ·
              refine ⟨1035997351372143250039765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1381329801829524333386353 1035997351372143250039765)
              ·
                refine ⟨24281187922784607422807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1035997351372143250039765 24281187922784607422807)
                ·
                  rfl

theorem cell23_1276761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 7].length) (baseStart_1276761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276761 prefixEnd_1276761 := by exact prefixLift 1276761
  have htrace : WordTrace (prefixWord ++ tailWord_1276761) baseStart_1276761 baseEnd_1276761 := by
    simpa [prefixWord, tailWord_1276761, baseEnd_1276761] using wordTrace_append hprefix tailTrace_1276761
  have hstable : (prefixWord ++ tailWord_1276761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276761).length < 2 ^ (prefixWord ++ tailWord_1276761).sum := by decide
  have hdescent : baseEnd_1276761 < baseStart_1276761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276772 : List Nat := [2, 3, 1, 1, 4, 1, 3, 3, 1, 2, 2]
def baseStart_1276772 : Nat := 118140960795 + 1276772 * 2 ^ 59
def prefixEnd_1276772 : Nat := 4983230072969 + 3 ^ 40 * 1276772 * 2
def baseEnd_1276772 : Nat := 655597722202383857378239

theorem tailTrace_1276772 : CollatzResearch.WordTrace tailWord_1276772 prefixEnd_1276772 655597722202383857378239 := by
  unfold tailWord_1276772
  simp only [CollatzResearch.WordTrace]
  refine ⟨23283850265240287071220285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31045133686987049428293713 23283850265240287071220285)
  ·
    refine ⟨8731443849465107651707607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23283850265240287071220285 8731443849465107651707607)
    ·
      refine ⟨13097165774197661477561411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8731443849465107651707607 13097165774197661477561411)
      ·
        refine ⟨19645748661296492216342117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13097165774197661477561411 19645748661296492216342117)
        ·
          refine ⟨3683577873993092290564147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19645748661296492216342117 3683577873993092290564147)
          ·
            refine ⟨5525366810989638435846221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3683577873993092290564147 5525366810989638435846221)
            ·
              refine ⟨2072012554121114413442333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5525366810989638435846221 2072012554121114413442333)
              ·
                refine ⟨777004707795417905040875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2072012554121114413442333 777004707795417905040875)
                ·
                  refine ⟨1165507061693126857561313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777004707795417905040875 1165507061693126857561313)
                  ·
                    refine ⟨874130296269845143170985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1165507061693126857561313 874130296269845143170985)
                    ·
                      refine ⟨655597722202383857378239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 874130296269845143170985 655597722202383857378239)
                      ·
                        rfl

theorem cell23_1276772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_1276772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276772 prefixEnd_1276772 := by exact prefixLift 1276772
  have htrace : WordTrace (prefixWord ++ tailWord_1276772) baseStart_1276772 baseEnd_1276772 := by
    simpa [prefixWord, tailWord_1276772, baseEnd_1276772] using wordTrace_append hprefix tailTrace_1276772
  have hstable : (prefixWord ++ tailWord_1276772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276772).length < 2 ^ (prefixWord ++ tailWord_1276772).sum := by decide
  have hdescent : baseEnd_1276772 < baseStart_1276772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276789 : List Nat := [1, 3, 4, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_1276789 : Nat := 118140960795 + 1276789 * 2 ^ 59
def prefixEnd_1276789 : Nat := 4983230072969 + 3 ^ 40 * 1276789 * 2
def baseEnd_1276789 : Nat := 655606451373510290865661

theorem tailTrace_1276789 : CollatzResearch.WordTrace tailWord_1276789 prefixEnd_1276789 655606451373510290865661 := by
  unfold tailWord_1276789
  simp only [CollatzResearch.WordTrace]
  refine ⟨46568320571418986045809421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31045547047612657363872947 46568320571418986045809421)
  ·
    refine ⟨17463120214282119767178533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46568320571418986045809421 17463120214282119767178533)
    ·
      refine ⟨3274335040177897456345975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17463120214282119767178533 3274335040177897456345975)
      ·
        refine ⟨4911502560266846184518963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3274335040177897456345975 4911502560266846184518963)
        ·
          refine ⟨7367253840400269276778445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4911502560266846184518963 7367253840400269276778445)
          ·
            refine ⟨2762720190150100978791917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7367253840400269276778445 2762720190150100978791917)
            ·
              refine ⟨1036020071306287867046969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2762720190150100978791917 1036020071306287867046969)
              ·
                refine ⟨777015053479715900285227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1036020071306287867046969 777015053479715900285227)
                ·
                  refine ⟨1165522580219573850427841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777015053479715900285227 1165522580219573850427841)
                  ·
                    refine ⟨874141935164680387820881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1165522580219573850427841 874141935164680387820881)
                    ·
                      refine ⟨655606451373510290865661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 874141935164680387820881 655606451373510290865661)
                      ·
                        rfl

theorem cell23_1276789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_1276789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276789 prefixEnd_1276789 := by exact prefixLift 1276789
  have htrace : WordTrace (prefixWord ++ tailWord_1276789) baseStart_1276789 baseEnd_1276789 := by
    simpa [prefixWord, tailWord_1276789, baseEnd_1276789] using wordTrace_append hprefix tailTrace_1276789
  have hstable : (prefixWord ++ tailWord_1276789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276789).length < 2 ^ (prefixWord ++ tailWord_1276789).sum := by decide
  have hdescent : baseEnd_1276789 < baseStart_1276789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276794 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_1276794 : Nat := 118140960795 + 1276794 * 2 ^ 59
def prefixEnd_1276794 : Nat := 4983230072969 + 3 ^ 40 * 1276794 * 2
def baseEnd_1276794 : Nat := 655609018776782771303137

theorem tailTrace_1276794 : CollatzResearch.WordTrace tailWord_1276794 prefixEnd_1276794 655609018776782771303137 := by
  unfold tailWord_1276794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11642125734100217974935359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31045668624267247933160957 11642125734100217974935359)
  ·
    refine ⟨17463188601150326962403039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11642125734100217974935359 17463188601150326962403039)
    ·
      refine ⟨26194782901725490443604559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17463188601150326962403039 26194782901725490443604559)
      ·
        refine ⟨39292174352588235665406839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26194782901725490443604559 39292174352588235665406839)
        ·
          refine ⟨58938261528882353498110259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39292174352588235665406839 58938261528882353498110259)
          ·
            refine ⟨88407392293323530247165389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58938261528882353498110259 88407392293323530247165389)
            ·
              refine ⟨33152772109996323842687021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88407392293323530247165389 33152772109996323842687021)
              ·
                refine ⟨12432289541248621441007633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33152772109996323842687021 12432289541248621441007633)
                ·
                  refine ⟨9324217155936466080755725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12432289541248621441007633 9324217155936466080755725)
                  ·
                    refine ⟨3496581433476174780283397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9324217155936466080755725 3496581433476174780283397)
                    ·
                      refine ⟨655609018776782771303137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3496581433476174780283397 655609018776782771303137)
                      ·
                        rfl

theorem cell23_1276794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_1276794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276794 prefixEnd_1276794 := by exact prefixLift 1276794
  have htrace : WordTrace (prefixWord ++ tailWord_1276794) baseStart_1276794 baseEnd_1276794 := by
    simpa [prefixWord, tailWord_1276794, baseEnd_1276794] using wordTrace_append hprefix tailTrace_1276794
  have hstable : (prefixWord ++ tailWord_1276794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276794).length < 2 ^ (prefixWord ++ tailWord_1276794).sum := by decide
  have hdescent : baseEnd_1276794 < baseStart_1276794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276804 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_1276804 : Nat := 118140960795 + 1276804 * 2 ^ 59
def prefixEnd_1276804 : Nat := 4983230072969 + 3 ^ 40 * 1276804 * 2
def baseEnd_1276804 : Nat := 218538051194442577392697

theorem tailTrace_1276804 : CollatzResearch.WordTrace tailWord_1276804 prefixEnd_1276804 218538051194442577392697 := by
  unfold tailWord_1276804
  simp only [CollatzResearch.WordTrace]
  refine ⟨23284433833182321803802733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31045911777576429071736977 23284433833182321803802733)
  ·
    refine ⟨8731662687443370676426025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23284433833182321803802733 8731662687443370676426025)
    ·
      refine ⟨6548747015582528007319519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8731662687443370676426025 6548747015582528007319519)
      ·
        refine ⟨9823120523373792010979279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6548747015582528007319519 9823120523373792010979279)
        ·
          refine ⟨14734680785060688016468919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9823120523373792010979279 14734680785060688016468919)
          ·
            refine ⟨22102021177591032024703379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14734680785060688016468919 22102021177591032024703379)
            ·
              refine ⟨33153031766386548037055069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22102021177591032024703379 33153031766386548037055069)
              ·
                refine ⟨12432386912394955513895651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33153031766386548037055069 12432386912394955513895651)
                ·
                  refine ⟨18648580368592433270843477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12432386912394955513895651 18648580368592433270843477)
                  ·
                    refine ⟨218538051194442577392697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18648580368592433270843477 218538051194442577392697)
                    ·
                      rfl

theorem cell23_1276804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_1276804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276804 prefixEnd_1276804 := by exact prefixLift 1276804
  have htrace : WordTrace (prefixWord ++ tailWord_1276804) baseStart_1276804 baseEnd_1276804 := by
    simpa [prefixWord, tailWord_1276804, baseEnd_1276804] using wordTrace_append hprefix tailTrace_1276804
  have hstable : (prefixWord ++ tailWord_1276804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276804).length < 2 ^ (prefixWord ++ tailWord_1276804).sum := by decide
  have hdescent : baseEnd_1276804 < baseStart_1276804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276805 : List Nat := [1, 3, 1, 1, 3, 3, 4, 1, 2, 1, 3]
def baseStart_1276805 : Nat := 118140960795 + 1276805 * 2 ^ 59
def prefixEnd_1276805 : Nat := 4983230072969 + 3 ^ 40 * 1276805 * 2
def baseEnd_1276805 : Nat := 655614667063982228265587

theorem tailTrace_1276805 : CollatzResearch.WordTrace tailWord_1276805 prefixEnd_1276805 655614667063982228265587 := by
  unfold tailWord_1276805
  simp only [CollatzResearch.WordTrace]
  refine ⟨46568904139361020778391869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31045936092907347185594579 46568904139361020778391869)
  ·
    refine ⟨17463339052260382791896951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46568904139361020778391869 17463339052260382791896951)
    ·
      refine ⟨26195008578390574187845427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17463339052260382791896951 26195008578390574187845427)
      ·
        refine ⟨39292512867585861281768141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26195008578390574187845427 39292512867585861281768141)
        ·
          refine ⟨14734692325344697980663053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39292512867585861281768141 14734692325344697980663053)
          ·
            refine ⟨5525509622004261742748645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14734692325344697980663053 5525509622004261742748645)
            ·
              refine ⟨1036033054125799076765371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5525509622004261742748645 1036033054125799076765371)
              ·
                refine ⟨1554049581188698615148057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036033054125799076765371 1554049581188698615148057)
                ·
                  refine ⟨1165537185891523961361043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1554049581188698615148057 1165537185891523961361043)
                  ·
                    refine ⟨1748305778837285942041565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1165537185891523961361043 1748305778837285942041565)
                    ·
                      refine ⟨655614667063982228265587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1748305778837285942041565 655614667063982228265587)
                      ·
                        rfl

theorem cell23_1276805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 2, 1, 3].length) (baseStart_1276805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276805 prefixEnd_1276805 := by exact prefixLift 1276805
  have htrace : WordTrace (prefixWord ++ tailWord_1276805) baseStart_1276805 baseEnd_1276805 := by
    simpa [prefixWord, tailWord_1276805, baseEnd_1276805] using wordTrace_append hprefix tailTrace_1276805
  have hstable : (prefixWord ++ tailWord_1276805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276805).length < 2 ^ (prefixWord ++ tailWord_1276805).sum := by decide
  have hdescent : baseEnd_1276805 < baseStart_1276805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276822 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1276822 : Nat := 118140960795 + 1276822 * 2 ^ 59
def prefixEnd_1276822 : Nat := 4983230072969 + 3 ^ 40 * 1276822 * 2
def baseEnd_1276822 : Nat := 655623396235108661753009

theorem tailTrace_1276822 : CollatzResearch.WordTrace tailWord_1276822 prefixEnd_1276822 655623396235108661753009 := by
  unfold tailWord_1276822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2910595261268714542610045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31046349453532955121173813 2910595261268714542610045)
  ·
    refine ⟨1091473222975767953478767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2910595261268714542610045 1091473222975767953478767)
    ·
      refine ⟨1637209834463651930218151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1091473222975767953478767 1637209834463651930218151)
      ·
        refine ⟨2455814751695477895327227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637209834463651930218151 2455814751695477895327227)
        ·
          refine ⟨3683722127543216842990841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455814751695477895327227 3683722127543216842990841)
          ·
            refine ⟨2762791595657412632243131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3683722127543216842990841 2762791595657412632243131)
            ·
              refine ⟨4144187393486118948364697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2762791595657412632243131 4144187393486118948364697)
              ·
                refine ⟨3108140545114589211273523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4144187393486118948364697 3108140545114589211273523)
                ·
                  refine ⟨4662210817671883816910285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108140545114589211273523 4662210817671883816910285)
                  ·
                    refine ⟨1748329056626956431341357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4662210817671883816910285 1748329056626956431341357)
                    ·
                      refine ⟨655623396235108661753009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1748329056626956431341357 655623396235108661753009)
                      ·
                        rfl

theorem cell23_1276822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1276822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276822 prefixEnd_1276822 := by exact prefixLift 1276822
  have htrace : WordTrace (prefixWord ++ tailWord_1276822) baseStart_1276822 baseEnd_1276822 := by
    simpa [prefixWord, tailWord_1276822, baseEnd_1276822] using wordTrace_append hprefix tailTrace_1276822
  have hstable : (prefixWord ++ tailWord_1276822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276822).length < 2 ^ (prefixWord ++ tailWord_1276822).sum := by decide
  have hdescent : baseEnd_1276822 < baseStart_1276822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276831 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1276831 : Nat := 118140960795 + 1276831 * 2 ^ 59
def prefixEnd_1276831 : Nat := 4983230072969 + 3 ^ 40 * 1276831 * 2
def baseEnd_1276831 : Nat := 655628017560999126540467

theorem tailTrace_1276831 : CollatzResearch.WordTrace tailWord_1276831 prefixEnd_1276831 655628017560999126540467 := by
  unfold tailWord_1276831
  simp only [CollatzResearch.WordTrace]
  refine ⟨46569852437266827218838347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31046568291511218145892231 46569852437266827218838347)
  ·
    refine ⟨69854778655900240828257521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46569852437266827218838347 69854778655900240828257521)
    ·
      refine ⟨52391083991925180621193141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69854778655900240828257521 52391083991925180621193141)
      ·
        refine ⟨4911664124242985683236857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52391083991925180621193141 4911664124242985683236857)
        ·
          refine ⟨3683748093182239262427643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4911664124242985683236857 3683748093182239262427643)
          ·
            refine ⟨5525622139773358893641465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3683748093182239262427643 5525622139773358893641465)
            ·
              refine ⟨4144216604830019170231099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5525622139773358893641465 4144216604830019170231099)
              ·
                refine ⟨6216324907245028755346649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4144216604830019170231099 6216324907245028755346649)
                ·
                  refine ⟨4662243680433771566509987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6216324907245028755346649 4662243680433771566509987)
                  ·
                    refine ⟨6993365520650657349764981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4662243680433771566509987 6993365520650657349764981)
                    ·
                      refine ⟨655628017560999126540467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6993365520650657349764981 655628017560999126540467)
                      ·
                        rfl

theorem cell23_1276831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1276831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276831 prefixEnd_1276831 := by exact prefixLift 1276831
  have htrace : WordTrace (prefixWord ++ tailWord_1276831) baseStart_1276831 baseEnd_1276831 := by
    simpa [prefixWord, tailWord_1276831, baseEnd_1276831] using wordTrace_append hprefix tailTrace_1276831
  have hstable : (prefixWord ++ tailWord_1276831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276831).length < 2 ^ (prefixWord ++ tailWord_1276831).sum := by decide
  have hdescent : baseEnd_1276831 < baseStart_1276831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276885 : List Nat := [1, 3, 2, 3, 3, 1, 2, 3, 5]
def baseStart_1276885 : Nat := 118140960795 + 1276885 * 2 ^ 59
def prefixEnd_1276885 : Nat := 4983230072969 + 3 ^ 40 * 1276885 * 2
def baseEnd_1276885 : Nat := 72850638390704657251691

theorem tailTrace_1276885 : CollatzResearch.WordTrace tailWord_1276885 prefixEnd_1276885 72850638390704657251691 := by
  unfold tailWord_1276885
  simp only [CollatzResearch.WordTrace]
  refine ⟨46571821979071194441304109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31047881319380796294202739 46571821979071194441304109)
  ·
    refine ⟨17464433242151697915489041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46571821979071194441304109 17464433242151697915489041)
    ·
      refine ⟨13098324931613773436616781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17464433242151697915489041 13098324931613773436616781)
      ·
        refine ⟨4911871849355165038731293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13098324931613773436616781 4911871849355165038731293)
        ·
          refine ⟨1841951943508186889524235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4911871849355165038731293 1841951943508186889524235)
          ·
            refine ⟨2762927915262280334286353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841951943508186889524235 2762927915262280334286353)
            ·
              refine ⟨2072195936446710250714765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2762927915262280334286353 2072195936446710250714765)
              ·
                refine ⟨777073476167516344018037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2072195936446710250714765 777073476167516344018037)
                ·
                  refine ⟨72850638390704657251691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 777073476167516344018037 72850638390704657251691)
                  ·
                    rfl

theorem cell23_1276885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 5].length) (baseStart_1276885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276885 prefixEnd_1276885 := by exact prefixLift 1276885
  have htrace : WordTrace (prefixWord ++ tailWord_1276885) baseStart_1276885 baseEnd_1276885 := by
    simpa [prefixWord, tailWord_1276885, baseEnd_1276885] using wordTrace_append hprefix tailTrace_1276885
  have hstable : (prefixWord ++ tailWord_1276885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276885).length < 2 ^ (prefixWord ++ tailWord_1276885).sum := by decide
  have hdescent : baseEnd_1276885 < baseStart_1276885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276918 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1276918 : Nat := 118140960795 + 1276918 * 2 ^ 59
def prefixEnd_1276918 : Nat := 4983230072969 + 3 ^ 40 * 1276918 * 2
def baseEnd_1276918 : Nat := 655672690377940286152567

theorem tailTrace_1276918 : CollatzResearch.WordTrace tailWord_1276918 prefixEnd_1276918 655672690377940286152567 := by
  unfold tailWord_1276918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2910814099246977567328463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31048683725301094051503605 2910814099246977567328463)
  ·
    refine ⟨4366221148870466350992695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2910814099246977567328463 4366221148870466350992695)
    ·
      refine ⟨6549331723305699526489043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4366221148870466350992695 6549331723305699526489043)
      ·
        refine ⟨9823997584958549289733565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6549331723305699526489043 9823997584958549289733565)
        ·
          refine ⟨3683999094359455983650087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9823997584958549289733565 3683999094359455983650087)
          ·
            refine ⟨5525998641539183975475131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3683999094359455983650087 5525998641539183975475131)
            ·
              refine ⟨8288997962308775963212697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5525998641539183975475131 8288997962308775963212697)
              ·
                refine ⟨6216748471731581972409523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8288997962308775963212697 6216748471731581972409523)
                ·
                  refine ⟨9325122707597372958614285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6216748471731581972409523 9325122707597372958614285)
                  ·
                    refine ⟨3496921015349014859480357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9325122707597372958614285 3496921015349014859480357)
                    ·
                      refine ⟨655672690377940286152567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3496921015349014859480357 655672690377940286152567)
                      ·
                        rfl

theorem cell23_1276918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1276918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276918 prefixEnd_1276918 := by exact prefixLift 1276918
  have htrace : WordTrace (prefixWord ++ tailWord_1276918) baseStart_1276918 baseEnd_1276918 := by
    simpa [prefixWord, tailWord_1276918, baseEnd_1276918] using wordTrace_append hprefix tailTrace_1276918
  have hstable : (prefixWord ++ tailWord_1276918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276918).length < 2 ^ (prefixWord ++ tailWord_1276918).sum := by decide
  have hdescent : baseEnd_1276918 < baseStart_1276918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276921 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 3, 4, 3]
def baseStart_1276921 : Nat := 118140960795 + 1276921 * 2 ^ 59
def prefixEnd_1276921 : Nat := 4983230072969 + 3 ^ 40 * 1276921 * 2
def baseEnd_1276921 : Nat := 655674230819903774415053

theorem tailTrace_1276921 : CollatzResearch.WordTrace tailWord_1276921 prefixEnd_1276921 655674230819903774415053 := by
  unfold tailWord_1276921
  simp only [CollatzResearch.WordTrace]
  refine ⟨46573135006940772589614617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31048756671293848393076411 46573135006940772589614617)
  ·
    refine ⟨34929851255205579442210963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46573135006940772589614617 34929851255205579442210963)
    ·
      refine ⟨52394776882808369163316445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34929851255205579442210963 52394776882808369163316445)
      ·
        refine ⟨19648041331053138436243667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52394776882808369163316445 19648041331053138436243667)
        ·
          refine ⟨29472061996579707654365501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19648041331053138436243667 29472061996579707654365501)
          ·
            refine ⟨11052023248717390370387063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29472061996579707654365501 11052023248717390370387063)
            ·
              refine ⟨16578034873076085555580595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11052023248717390370387063 16578034873076085555580595)
              ·
                refine ⟨24867052309614128333370893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16578034873076085555580595 24867052309614128333370893)
                ·
                  refine ⟨9325144616105298125014085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24867052309614128333370893 9325144616105298125014085)
                  ·
                    refine ⟨1748464615519743398440141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9325144616105298125014085 1748464615519743398440141)
                    ·
                      refine ⟨655674230819903774415053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1748464615519743398440141 655674230819903774415053)
                      ·
                        rfl

theorem cell23_1276921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_1276921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276921 prefixEnd_1276921 := by exact prefixLift 1276921
  have htrace : WordTrace (prefixWord ++ tailWord_1276921) baseStart_1276921 baseEnd_1276921 := by
    simpa [prefixWord, tailWord_1276921, baseEnd_1276921] using wordTrace_append hprefix tailTrace_1276921
  have hstable : (prefixWord ++ tailWord_1276921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276921).length < 2 ^ (prefixWord ++ tailWord_1276921).sum := by decide
  have hdescent : baseEnd_1276921 < baseStart_1276921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276938 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_1276938 : Nat := 118140960795 + 1276938 * 2 ^ 59
def prefixEnd_1276938 : Nat := 4983230072969 + 3 ^ 40 * 1276938 * 2
def baseEnd_1276938 : Nat := 655682959991030207902475

theorem tailTrace_1276938 : CollatzResearch.WordTrace tailWord_1276938 prefixEnd_1276938 655682959991030207902475 := by
  unfold tailWord_1276938
  simp only [CollatzResearch.WordTrace]
  refine ⟨11643438761969796123245867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31049170031919456328655645 11643438761969796123245867)
  ·
    refine ⟨17465158142954694184868801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11643438761969796123245867 17465158142954694184868801)
    ·
      refine ⟨13098868607216020638651601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17465158142954694184868801 13098868607216020638651601)
      ·
        refine ⟨9824151455412015478988701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13098868607216020638651601 9824151455412015478988701)
        ·
          refine ⟨3684056795779505804620763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9824151455412015478988701 3684056795779505804620763)
          ·
            refine ⟨5526085193669258706931145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3684056795779505804620763 5526085193669258706931145)
            ·
              refine ⟨4144563895251944030198359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5526085193669258706931145 4144563895251944030198359)
              ·
                refine ⟨6216845842877916045297539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4144563895251944030198359 6216845842877916045297539)
                ·
                  refine ⟨9325268764316874067946309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6216845842877916045297539 9325268764316874067946309)
                  ·
                    refine ⟨1748487893309413887739933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9325268764316874067946309 1748487893309413887739933)
                    ·
                      refine ⟨655682959991030207902475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1748487893309413887739933 655682959991030207902475)
                      ·
                        rfl

theorem cell23_1276938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_1276938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276938 prefixEnd_1276938 := by exact prefixLift 1276938
  have htrace : WordTrace (prefixWord ++ tailWord_1276938) baseStart_1276938 baseEnd_1276938 := by
    simpa [prefixWord, tailWord_1276938, baseEnd_1276938] using wordTrace_append hprefix tailTrace_1276938
  have hstable : (prefixWord ++ tailWord_1276938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276938).length < 2 ^ (prefixWord ++ tailWord_1276938).sum := by decide
  have hdescent : baseEnd_1276938 < baseStart_1276938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276971 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 3, 5]
def baseStart_1276971 : Nat := 118140960795 + 1276971 * 2 ^ 59
def prefixEnd_1276971 : Nat := 4983230072969 + 3 ^ 40 * 1276971 * 2
def baseEnd_1276971 : Nat := 218566634950876192929941

theorem tailTrace_1276971 : CollatzResearch.WordTrace tailWord_1276971 prefixEnd_1276971 218566634950876192929941 := by
  unfold tailWord_1276971
  simp only [CollatzResearch.WordTrace]
  refine ⟨46574958656759631128934767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31049972437839754085956511 46574958656759631128934767)
  ·
    refine ⟨69862437985139446693402151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46574958656759631128934767 69862437985139446693402151)
    ·
      refine ⟨104793656977709170040103227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69862437985139446693402151 104793656977709170040103227)
      ·
        refine ⟨157190485466563755060154841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104793656977709170040103227 157190485466563755060154841)
        ·
          refine ⟨117892864099922816295116131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157190485466563755060154841 117892864099922816295116131)
          ·
            refine ⟨176839296149884224442674197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117892864099922816295116131 176839296149884224442674197)
            ·
              refine ⟨8289342007025823020750353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 176839296149884224442674197 8289342007025823020750353)
              ·
                refine ⟨6217006505269367265562765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8289342007025823020750353 6217006505269367265562765)
                ·
                  refine ⟨2331377439476012724586037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6217006505269367265562765 2331377439476012724586037)
                  ·
                    refine ⟨218566634950876192929941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2331377439476012724586037 218566634950876192929941)
                    ·
                      rfl

theorem cell23_1276971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 5].length) (baseStart_1276971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276971 prefixEnd_1276971 := by exact prefixLift 1276971
  have htrace : WordTrace (prefixWord ++ tailWord_1276971) baseStart_1276971 baseEnd_1276971 := by
    simpa [prefixWord, tailWord_1276971, baseEnd_1276971] using wordTrace_append hprefix tailTrace_1276971
  have hstable : (prefixWord ++ tailWord_1276971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276971).length < 2 ^ (prefixWord ++ tailWord_1276971).sum := by decide
  have hdescent : baseEnd_1276971 < baseStart_1276971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276988 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 3, 5]
def baseStart_1276988 : Nat := 118140960795 + 1276988 * 2 ^ 59
def prefixEnd_1276988 : Nat := 4983230072969 + 3 ^ 40 * 1276988 * 2
def baseEnd_1276988 : Nat := 218569544674585004092415

theorem tailTrace_1276988 : CollatzResearch.WordTrace tailWord_1276988 prefixEnd_1276988 218569544674585004092415 := by
  unfold tailWord_1276988
  simp only [CollatzResearch.WordTrace]
  refine ⟨23287789348849021516151809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31050385798465362021535745 23287789348849021516151809)
  ·
    refine ⟨17465842011636766137113857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23287789348849021516151809 17465842011636766137113857)
    ·
      refine ⟨13099381508727574602835393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17465842011636766137113857 13099381508727574602835393)
      ·
        refine ⟨9824536131545680952126545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13099381508727574602835393 9824536131545680952126545)
        ·
          refine ⟨7368402098659260714094909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9824536131545680952126545 7368402098659260714094909)
          ·
            refine ⟨2763150786997222767785591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7368402098659260714094909 2763150786997222767785591)
            ·
              refine ⟨4144726180495834151678387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2763150786997222767785591 4144726180495834151678387)
              ·
                refine ⟨6217089270743751227517581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4144726180495834151678387 6217089270743751227517581)
                ·
                  refine ⟨2331408476528906710319093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6217089270743751227517581 2331408476528906710319093)
                  ·
                    refine ⟨218569544674585004092415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2331408476528906710319093 218569544674585004092415)
                    ·
                      rfl

theorem cell23_1276988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_1276988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276988 prefixEnd_1276988 := by exact prefixLift 1276988
  have htrace : WordTrace (prefixWord ++ tailWord_1276988) baseStart_1276988 baseEnd_1276988 := by
    simpa [prefixWord, tailWord_1276988, baseEnd_1276988] using wordTrace_append hprefix tailTrace_1276988
  have hstable : (prefixWord ++ tailWord_1276988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276988).length < 2 ^ (prefixWord ++ tailWord_1276988).sum := by decide
  have hdescent : baseEnd_1276988 < baseStart_1276988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276995 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 2, 3, 2]
def baseStart_1276995 : Nat := 118140960795 + 1276995 * 2 ^ 59
def prefixEnd_1276995 : Nat := 4983230072969 + 3 ^ 40 * 1276995 * 2
def baseEnd_1276995 : Nat := 655712228388336484889713

theorem tailTrace_1276995 : CollatzResearch.WordTrace tailWord_1276995 prefixEnd_1276995 655712228388336484889713 := by
  unfold tailWord_1276995
  simp only [CollatzResearch.WordTrace]
  refine ⟨46575834008672683227808439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31050556005781788818538959 46575834008672683227808439)
  ·
    refine ⟨69863751013009024841712659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46575834008672683227808439 69863751013009024841712659)
    ·
      refine ⟨104795626519513537262568989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69863751013009024841712659 104795626519513537262568989)
      ·
        refine ⟨39298359944817576473463371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104795626519513537262568989 39298359944817576473463371)
        ·
          refine ⟨58947539917226364710195057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39298359944817576473463371 58947539917226364710195057)
          ·
            refine ⟨44210654937919773532646293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58947539917226364710195057 44210654937919773532646293)
            ·
              refine ⟨2072374450214989384342795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44210654937919773532646293 2072374450214989384342795)
              ·
                refine ⟨3108561675322484076514193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2072374450214989384342795 3108561675322484076514193)
                ·
                  refine ⟨2331421256491863057385645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3108561675322484076514193 2331421256491863057385645)
                  ·
                    refine ⟨874282971184448646519617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2331421256491863057385645 874282971184448646519617)
                    ·
                      refine ⟨655712228388336484889713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 874282971184448646519617 655712228388336484889713)
                      ·
                        rfl

theorem cell23_1276995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 3, 2].length) (baseStart_1276995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1276995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1276995 prefixEnd_1276995 := by exact prefixLift 1276995
  have htrace : WordTrace (prefixWord ++ tailWord_1276995) baseStart_1276995 baseEnd_1276995 := by
    simpa [prefixWord, tailWord_1276995, baseEnd_1276995] using wordTrace_append hprefix tailTrace_1276995
  have hstable : (prefixWord ++ tailWord_1276995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276995).length < 2 ^ (prefixWord ++ tailWord_1276995).sum := by decide
  have hdescent : baseEnd_1276995 < baseStart_1276995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277008 : List Nat := [2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 4]
def baseStart_1277008 : Nat := 118140960795 + 1277008 * 2 ^ 59
def prefixEnd_1277008 : Nat := 4983230072969 + 3 ^ 40 * 1277008 * 2
def baseEnd_1277008 : Nat := 655718903636844934027153

theorem tailTrace_1277008 : CollatzResearch.WordTrace tailWord_1277008 prefixEnd_1277008 655718903636844934027153 := by
  unfold tailWord_1277008
  simp only [CollatzResearch.WordTrace]
  refine ⟨23288154078812793224015839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31050872105083724298687785 23288154078812793224015839)
  ·
    refine ⟨34932231118219189836023759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23288154078812793224015839 34932231118219189836023759)
    ·
      refine ⟨52398346677328784754035639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34932231118219189836023759 52398346677328784754035639)
      ·
        refine ⟨78597520015993177131053459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52398346677328784754035639 78597520015993177131053459)
        ·
          refine ⟨117896280023989765696580189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78597520015993177131053459 117896280023989765696580189)
          ·
            refine ⟨44211105008996162136217571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117896280023989765696580189 44211105008996162136217571)
            ·
              refine ⟨66316657513494243204326357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44211105008996162136217571 66316657513494243204326357)
              ·
                refine ⟨1554296660472521325101399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66316657513494243204326357 1554296660472521325101399)
                ·
                  refine ⟨2331444990708781987652099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554296660472521325101399 2331444990708781987652099)
                  ·
                    refine ⟨3497167486063172981478149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2331444990708781987652099 3497167486063172981478149)
                    ·
                      refine ⟨655718903636844934027153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3497167486063172981478149 655718903636844934027153)
                      ·
                        rfl

theorem cell23_1277008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 4].length) (baseStart_1277008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277008 prefixEnd_1277008 := by exact prefixLift 1277008
  have htrace : WordTrace (prefixWord ++ tailWord_1277008) baseStart_1277008 baseEnd_1277008 := by
    simpa [prefixWord, tailWord_1277008, baseEnd_1277008] using wordTrace_append hprefix tailTrace_1277008
  have hstable : (prefixWord ++ tailWord_1277008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277008).length < 2 ^ (prefixWord ++ tailWord_1277008).sum := by decide
  have hdescent : baseEnd_1277008 < baseStart_1277008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277022 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1277022 : Nat := 118140960795 + 1277022 * 2 ^ 59
def prefixEnd_1277022 : Nat := 4983230072969 + 3 ^ 40 * 1277022 * 2
def baseEnd_1277022 : Nat := 218575364122002626417363

theorem tailTrace_1277022 : CollatzResearch.WordTrace tailWord_1277022 prefixEnd_1277022 218575364122002626417363 := by
  unfold tailWord_1277022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5822102347446858354880165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31051212519716577892694213 5822102347446858354880165)
  ·
    refine ⟨1091644190146285941540031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5822102347446858354880165 1091644190146285941540031)
    ·
      refine ⟨1637466285219428912310047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1091644190146285941540031 1637466285219428912310047)
      ·
        refine ⟨2456199427829143368465071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637466285219428912310047 2456199427829143368465071)
        ·
          refine ⟨3684299141743715052697607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2456199427829143368465071 3684299141743715052697607)
          ·
            refine ⟨5526448712615572579046411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3684299141743715052697607 5526448712615572579046411)
            ·
              refine ⟨8289673068923358868569617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5526448712615572579046411 8289673068923358868569617)
              ·
                refine ⟨6217254801692519151427213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8289673068923358868569617 6217254801692519151427213)
                ·
                  refine ⟨2331470550634694681785205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6217254801692519151427213 2331470550634694681785205)
                  ·
                    refine ⟨218575364122002626417363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2331470550634694681785205 218575364122002626417363)
                    ·
                      rfl

theorem cell23_1277022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1277022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277022 prefixEnd_1277022 := by exact prefixLift 1277022
  have htrace : WordTrace (prefixWord ++ tailWord_1277022) baseStart_1277022 baseEnd_1277022 := by
    simpa [prefixWord, tailWord_1277022, baseEnd_1277022] using wordTrace_append hprefix tailTrace_1277022
  have hstable : (prefixWord ++ tailWord_1277022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277022).length < 2 ^ (prefixWord ++ tailWord_1277022).sum := by decide
  have hdescent : baseEnd_1277022 < baseStart_1277022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277042 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 3, 2, 2]
def baseStart_1277042 : Nat := 118140960795 + 1277042 * 2 ^ 59
def prefixEnd_1277042 : Nat := 4983230072969 + 3 ^ 40 * 1277042 * 2
def baseEnd_1277042 : Nat := 655736361979097801001997

theorem tailTrace_1277042 : CollatzResearch.WordTrace tailWord_1277042 prefixEnd_1277042 655736361979097801001997 := by
  unfold tailWord_1277042
  simp only [CollatzResearch.WordTrace]
  refine ⟨11644387059875602563692345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31051698826334940169846253 11644387059875602563692345)
  ·
    refine ⟨8733290294906701922769259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11644387059875602563692345 8733290294906701922769259)
    ·
      refine ⟨13099935442360052884153889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8733290294906701922769259 13099935442360052884153889)
      ·
        refine ⟨9824951581770039663115417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13099935442360052884153889 9824951581770039663115417)
        ·
          refine ⟨7368713686327529747336563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9824951581770039663115417 7368713686327529747336563)
          ·
            refine ⟨11053070529491294621004845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7368713686327529747336563 11053070529491294621004845)
            ·
              refine ⟨4144901448559235482876817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11053070529491294621004845 4144901448559235482876817)
              ·
                refine ⟨3108676086419426612157613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4144901448559235482876817 3108676086419426612157613)
                ·
                  refine ⟨1165753532407284979559105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3108676086419426612157613 1165753532407284979559105)
                  ·
                    refine ⟨874315149305463734669329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1165753532407284979559105 874315149305463734669329)
                    ·
                      refine ⟨655736361979097801001997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 874315149305463734669329 655736361979097801001997)
                      ·
                        rfl

theorem cell23_1277042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_1277042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277042 prefixEnd_1277042 := by exact prefixLift 1277042
  have htrace : WordTrace (prefixWord ++ tailWord_1277042) baseStart_1277042 baseEnd_1277042 := by
    simpa [prefixWord, tailWord_1277042, baseEnd_1277042] using wordTrace_append hprefix tailTrace_1277042
  have hstable : (prefixWord ++ tailWord_1277042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277042).length < 2 ^ (prefixWord ++ tailWord_1277042).sum := by decide
  have hdescent : baseEnd_1277042 < baseStart_1277042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277059 : List Nat := [1, 1, 1, 3, 3, 2, 4, 3, 1, 2, 2]
def baseStart_1277059 : Nat := 118140960795 + 1277059 * 2 ^ 59
def prefixEnd_1277059 : Nat := 4983230072969 + 3 ^ 40 * 1277059 * 2
def baseEnd_1277059 : Nat := 655745091150224234489419

theorem tailTrace_1277059 : CollatzResearch.WordTrace tailWord_1277059 prefixEnd_1277059 655745091150224234489419 := by
  unfold tailWord_1277059
  simp only [CollatzResearch.WordTrace]
  refine ⟨46578168280440822158138231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31052112186960548105425487 46578168280440822158138231)
  ·
    refine ⟨69867252420661233237207347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46578168280440822158138231 69867252420661233237207347)
    ·
      refine ⟨104800878630991849855811021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69867252420661233237207347 104800878630991849855811021)
      ·
        refine ⟨39300329486621943695929133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104800878630991849855811021 39300329486621943695929133)
        ·
          refine ⟨14737623557483228885973425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39300329486621943695929133 14737623557483228885973425)
          ·
            refine ⟨11053217668112421664480069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14737623557483228885973425 11053217668112421664480069)
            ·
              refine ⟨2072478312771079062090013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11053217668112421664480069 2072478312771079062090013)
              ·
                refine ⟨777179367289154648283755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2072478312771079062090013 777179367289154648283755)
                ·
                  refine ⟨1165769050933731972425633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777179367289154648283755 1165769050933731972425633)
                  ·
                    refine ⟨874326788200298979319225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1165769050933731972425633 874326788200298979319225)
                    ·
                      refine ⟨655745091150224234489419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 874326788200298979319225 655745091150224234489419)
                      ·
                        rfl

theorem cell23_1277059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 1, 2, 2].length) (baseStart_1277059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277059 prefixEnd_1277059 := by exact prefixLift 1277059
  have htrace : WordTrace (prefixWord ++ tailWord_1277059) baseStart_1277059 baseEnd_1277059 := by
    simpa [prefixWord, tailWord_1277059, baseEnd_1277059] using wordTrace_append hprefix tailTrace_1277059
  have hstable : (prefixWord ++ tailWord_1277059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277059).length < 2 ^ (prefixWord ++ tailWord_1277059).sum := by decide
  have hdescent : baseEnd_1277059 < baseStart_1277059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277092 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 1, 3, 3]
def baseStart_1277092 : Nat := 118140960795 + 1277092 * 2 ^ 59
def prefixEnd_1277092 : Nat := 4983230072969 + 3 ^ 40 * 1277092 * 2
def baseEnd_1277092 : Nat := 655762036011822605376767

theorem tailTrace_1277092 : CollatzResearch.WordTrace tailWord_1277092 prefixEnd_1277092 655762036011822605376767 := by
  unfold tailWord_1277092
  simp only [CollatzResearch.WordTrace]
  refine ⟨23289685944660634397044765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31052914592880845862726353 23289685944660634397044765)
  ·
    refine ⟨8733632229247737898891787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23289685944660634397044765 8733632229247737898891787)
    ·
      refine ⟨13100448343871606848337681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8733632229247737898891787 13100448343871606848337681)
      ·
        refine ⟨9825336257903705136253261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13100448343871606848337681 9825336257903705136253261)
        ·
          refine ⟨3684501096713889426094973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9825336257903705136253261 3684501096713889426094973)
          ·
            refine ⟨1381687911267708534785615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3684501096713889426094973 1381687911267708534785615)
            ·
              refine ⟨2072531866901562802178423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381687911267708534785615 2072531866901562802178423)
              ·
                refine ⟨3108797800352344203267635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2072531866901562802178423 3108797800352344203267635)
                ·
                  refine ⟨4663196700528516304901453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108797800352344203267635 4663196700528516304901453)
                  ·
                    refine ⟨1748698762698193614338045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4663196700528516304901453 1748698762698193614338045)
                    ·
                      refine ⟨655762036011822605376767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1748698762698193614338045 655762036011822605376767)
                      ·
                        rfl

theorem cell23_1277092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_1277092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277092 prefixEnd_1277092 := by exact prefixLift 1277092
  have htrace : WordTrace (prefixWord ++ tailWord_1277092) baseStart_1277092 baseEnd_1277092 := by
    simpa [prefixWord, tailWord_1277092, baseEnd_1277092] using wordTrace_append hprefix tailTrace_1277092
  have hstable : (prefixWord ++ tailWord_1277092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277092).length < 2 ^ (prefixWord ++ tailWord_1277092).sum := by decide
  have hdescent : baseEnd_1277092 < baseStart_1277092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277128 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_1277128 : Nat := 118140960795 + 1277128 * 2 ^ 59
def prefixEnd_1277128 : Nat := 4983230072969 + 3 ^ 40 * 1277128 * 2
def baseEnd_1277128 : Nat := 655780521315384464526601

theorem tailTrace_1277128 : CollatzResearch.WordTrace tailWord_1277128 prefixEnd_1277128 655780521315384464526601 := by
  unfold tailWord_1277128
  simp only [CollatzResearch.WordTrace]
  refine ⟨23290342458595423471200019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31053789944793897961600025 23290342458595423471200019)
  ·
    refine ⟨34935513687893135206800029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23290342458595423471200019 34935513687893135206800029)
    ·
      refine ⟨13100817632959925702550011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34935513687893135206800029 13100817632959925702550011)
      ·
        refine ⟨19651226449439888553825017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13100817632959925702550011 19651226449439888553825017)
        ·
          refine ⟨14738419837079916415368763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19651226449439888553825017 14738419837079916415368763)
          ·
            refine ⟨22107629755619874623053145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14738419837079916415368763 22107629755619874623053145)
            ·
              refine ⟨16580722316714905967289859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22107629755619874623053145 16580722316714905967289859)
              ·
                refine ⟨24871083475072358950934789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16580722316714905967289859 24871083475072358950934789)
                ·
                  refine ⟨4663328151576067303300273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24871083475072358950934789 4663328151576067303300273)
                  ·
                    refine ⟨3497496113682050477475205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4663328151576067303300273 3497496113682050477475205)
                    ·
                      refine ⟨655780521315384464526601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3497496113682050477475205 655780521315384464526601)
                      ·
                        rfl

theorem cell23_1277128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_1277128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277128 prefixEnd_1277128 := by exact prefixLift 1277128
  have htrace : WordTrace (prefixWord ++ tailWord_1277128) baseStart_1277128 baseEnd_1277128 := by
    simpa [prefixWord, tailWord_1277128, baseEnd_1277128] using wordTrace_append hprefix tailTrace_1277128
  have hstable : (prefixWord ++ tailWord_1277128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277128).length < 2 ^ (prefixWord ++ tailWord_1277128).sum := by decide
  have hdescent : baseEnd_1277128 < baseStart_1277128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277178 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_1277178 : Nat := 118140960795 + 1277178 * 2 ^ 59
def prefixEnd_1277178 : Nat := 4983230072969 + 3 ^ 40 * 1277178 * 2
def baseEnd_1277178 : Nat := 655806195348109268901371

theorem tailTrace_1277178 : CollatzResearch.WordTrace tailWord_1277178 prefixEnd_1277178 655806195348109268901371 := by
  unfold tailWord_1277178
  simp only [CollatzResearch.WordTrace]
  refine ⟨11645627141752426370430047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31055005711339803654480125 11645627141752426370430047)
  ·
    refine ⟨17468440712628639555645071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11645627141752426370430047 17468440712628639555645071)
    ·
      refine ⟨26202661068942959333467607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17468440712628639555645071 26202661068942959333467607)
      ·
        refine ⟨39303991603414439000201411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26202661068942959333467607 39303991603414439000201411)
        ·
          refine ⟨58955987405121658500302117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39303991603414439000201411 58955987405121658500302117)
          ·
            refine ⟨11054247638460310968806647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58955987405121658500302117 11054247638460310968806647)
            ·
              refine ⟨16581371457690466453209971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11054247638460310968806647 16581371457690466453209971)
              ·
                refine ⟨24872057186535699679814957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16581371457690466453209971 24872057186535699679814957)
                ·
                  refine ⟨9327021444950887379930609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24872057186535699679814957 9327021444950887379930609)
                  ·
                    refine ⟨6995266083713165534947957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9327021444950887379930609 6995266083713165534947957)
                    ·
                      refine ⟨655806195348109268901371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6995266083713165534947957 655806195348109268901371)
                      ·
                        rfl

theorem cell23_1277178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_1277178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277178 prefixEnd_1277178 := by exact prefixLift 1277178
  have htrace : WordTrace (prefixWord ++ tailWord_1277178) baseStart_1277178 baseEnd_1277178 := by
    simpa [prefixWord, tailWord_1277178, baseEnd_1277178] using wordTrace_append hprefix tailTrace_1277178
  have hstable : (prefixWord ++ tailWord_1277178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277178).length < 2 ^ (prefixWord ++ tailWord_1277178).sum := by decide
  have hdescent : baseEnd_1277178 < baseStart_1277178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277185 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 2, 5]
def baseStart_1277185 : Nat := 118140960795 + 1277185 * 2 ^ 59
def prefixEnd_1277185 : Nat := 4983230072969 + 3 ^ 40 * 1277185 * 2
def baseEnd_1277185 : Nat := 218603263237563580504613

theorem tailTrace_1277185 : CollatzResearch.WordTrace tailWord_1277185 prefixEnd_1277185 218603263237563580504613 := by
  unfold tailWord_1277185
  simp only [CollatzResearch.WordTrace]
  refine ⟨46582763877984345677225009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31055175918656230451483339 46582763877984345677225009)
  ·
    refine ⟨34937072908488259257918757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46582763877984345677225009 34937072908488259257918757)
    ·
      refine ⟨6550701170341548610859767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34937072908488259257918757 6550701170341548610859767)
      ·
        refine ⟨9826051755512322916289651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6550701170341548610859767 9826051755512322916289651)
        ·
          refine ⟨14739077633268484374434477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9826051755512322916289651 14739077633268484374434477)
          ·
            refine ⟨5527154112475681640412929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14739077633268484374434477 5527154112475681640412929)
            ·
              refine ⟨4145365584356761230309697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5527154112475681640412929 4145365584356761230309697)
              ·
                refine ⟨3109024188267570922732273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4145365584356761230309697 3109024188267570922732273)
                ·
                  refine ⟨2331768141200678192049205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3109024188267570922732273 2331768141200678192049205)
                  ·
                    refine ⟨218603263237563580504613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2331768141200678192049205 218603263237563580504613)
                    ·
                      rfl

theorem cell23_1277185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_1277185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277185 prefixEnd_1277185 := by exact prefixLift 1277185
  have htrace : WordTrace (prefixWord ++ tailWord_1277185) baseStart_1277185 baseEnd_1277185 := by
    simpa [prefixWord, tailWord_1277185, baseEnd_1277185] using wordTrace_append hprefix tailTrace_1277185
  have hstable : (prefixWord ++ tailWord_1277185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277185).length < 2 ^ (prefixWord ++ tailWord_1277185).sum := by decide
  have hdescent : baseEnd_1277185 < baseStart_1277185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277228 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 8]
def baseStart_1277228 : Nat := 118140960795 + 1277228 * 2 ^ 59
def prefixEnd_1277228 : Nat := 4983230072969 + 3 ^ 40 * 1277228 * 2
def baseEnd_1277228 : Nat := 72870207708981563697349

theorem tailTrace_1277228 : CollatzResearch.WordTrace tailWord_1277228 prefixEnd_1277228 72870207708981563697349 := by
  unfold tailWord_1277228
  simp only [CollatzResearch.WordTrace]
  refine ⟨23292166108414282010520169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31056221477885709347360225 23292166108414282010520169)
  ·
    refine ⟨17469124581310711507890127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23292166108414282010520169 17469124581310711507890127)
    ·
      refine ⟨26203686871966067261835191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17469124581310711507890127 26203686871966067261835191)
      ·
        refine ⟨39305530307949100892752787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26203686871966067261835191 39305530307949100892752787)
        ·
          refine ⟨58958295461923651339129181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39305530307949100892752787 58958295461923651339129181)
          ·
            refine ⟨22109360798221369252173443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58958295461923651339129181 22109360798221369252173443)
            ·
              refine ⟨33164041197332053878260165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22109360798221369252173443 33164041197332053878260165)
              ·
                refine ⟨6218257724499760102173781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33164041197332053878260165 6218257724499760102173781)
                ·
                  refine ⟨72870207708981563697349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6218257724499760102173781 72870207708981563697349)
                  ·
                    rfl

theorem cell23_1277228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_1277228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277228 prefixEnd_1277228 := by exact prefixLift 1277228
  have htrace : WordTrace (prefixWord ++ tailWord_1277228) baseStart_1277228 baseEnd_1277228 := by
    simpa [prefixWord, tailWord_1277228, baseEnd_1277228] using wordTrace_append hprefix tailTrace_1277228
  have hstable : (prefixWord ++ tailWord_1277228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277228).length < 2 ^ (prefixWord ++ tailWord_1277228).sum := by decide
  have hdescent : baseEnd_1277228 < baseStart_1277228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277248 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 8]
def baseStart_1277248 : Nat := 118140960795 + 1277248 * 2 ^ 59
def prefixEnd_1277248 : Nat := 4983230072969 + 3 ^ 40 * 1277248 * 2
def baseEnd_1277248 : Nat := 655842138993923995026049

theorem tailTrace_1277248 : CollatzResearch.WordTrace tailWord_1277248 prefixEnd_1277248 655842138993923995026049 := by
  unfold tailWord_1277248
  simp only [CollatzResearch.WordTrace]
  refine ⟨23292530838378053718384199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31056707784504071624512265 23292530838378053718384199)
  ·
    refine ⟨34938796257567080577576299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23292530838378053718384199 34938796257567080577576299)
    ·
      refine ⟨52408194386350620866364449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34938796257567080577576299 52408194386350620866364449)
      ·
        refine ⟨39306145789762965649773337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52408194386350620866364449 39306145789762965649773337)
        ·
          refine ⟨29479609342322224237330003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39306145789762965649773337 29479609342322224237330003)
          ·
            refine ⟨44219414013483336355995005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29479609342322224237330003 44219414013483336355995005)
            ·
              refine ⟨16582280255056251133498127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44219414013483336355995005 16582280255056251133498127)
              ·
                refine ⟨24873420382584376700247191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16582280255056251133498127 24873420382584376700247191)
                ·
                  refine ⟨37310130573876565050370787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24873420382584376700247191 37310130573876565050370787)
                  ·
                    refine ⟨55965195860814847575556181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37310130573876565050370787 55965195860814847575556181)
                    ·
                      refine ⟨655842138993923995026049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 55965195860814847575556181 655842138993923995026049)
                      ·
                        rfl

theorem cell23_1277248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_1277248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277248 prefixEnd_1277248 := by exact prefixLift 1277248
  have htrace : WordTrace (prefixWord ++ tailWord_1277248) baseStart_1277248 baseEnd_1277248 := by
    simpa [prefixWord, tailWord_1277248, baseEnd_1277248] using wordTrace_append hprefix tailTrace_1277248
  have hstable : (prefixWord ++ tailWord_1277248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277248).length < 2 ^ (prefixWord ++ tailWord_1277248).sum := by decide
  have hdescent : baseEnd_1277248 < baseStart_1277248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277249 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1277249 : Nat := 118140960795 + 1277249 * 2 ^ 59
def prefixEnd_1277249 : Nat := 4983230072969 + 3 ^ 40 * 1277249 * 2
def baseEnd_1277249 : Nat := 218614217491526163704515

theorem tailTrace_1277249 : CollatzResearch.WordTrace tailWord_1277249 prefixEnd_1277249 218614217491526163704515 := by
  unfold tailWord_1277249
  simp only [CollatzResearch.WordTrace]
  refine ⟨46585098149752484607554801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31056732099834989738369867 46585098149752484607554801)
  ·
    refine ⟨34938823612314363455666101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46585098149752484607554801 34938823612314363455666101)
    ·
      refine ⟨3275514713654471573968697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34938823612314363455666101 3275514713654471573968697)
      ·
        refine ⟨2456636035240853680476523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3275514713654471573968697 2456636035240853680476523)
        ·
          refine ⟨3684954052861280520714785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2456636035240853680476523 3684954052861280520714785)
          ·
            refine ⟨2763715539645960390536089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3684954052861280520714785 2763715539645960390536089)
            ·
              refine ⟨2072786654734470292902067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2763715539645960390536089 2072786654734470292902067)
              ·
                refine ⟨3109179982101705439353101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2072786654734470292902067 3109179982101705439353101)
                ·
                  refine ⟨1165942493288139539757413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3109179982101705439353101 1165942493288139539757413)
                  ·
                    refine ⟨218614217491526163704515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1165942493288139539757413 218614217491526163704515)
                    ·
                      rfl

theorem cell23_1277249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1277249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277249 prefixEnd_1277249 := by exact prefixLift 1277249
  have htrace : WordTrace (prefixWord ++ tailWord_1277249) baseStart_1277249 baseEnd_1277249 := by
    simpa [prefixWord, tailWord_1277249, baseEnd_1277249] using wordTrace_append hprefix tailTrace_1277249
  have hstable : (prefixWord ++ tailWord_1277249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277249).length < 2 ^ (prefixWord ++ tailWord_1277249).sum := by decide
  have hdescent : baseEnd_1277249 < baseStart_1277249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277262 : List Nat := [4, 1, 1, 1, 1, 1, 7, 1, 6]
def baseStart_1277262 : Nat := 118140960795 + 1277262 * 2 ^ 59
def prefixEnd_1277262 : Nat := 4983230072969 + 3 ^ 40 * 1277262 * 2
def baseEnd_1277262 : Nat := 72872147524787437805665

theorem tailTrace_1277262 : CollatzResearch.WordTrace tailWord_1277262 prefixEnd_1277262 72872147524787437805665 := by
  unfold tailWord_1277262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5823196537338173478472255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31057048199136925218518693 5823196537338173478472255)
  ·
    refine ⟨8734794806007260217708383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5823196537338173478472255 8734794806007260217708383)
    ·
      refine ⟨13102192209010890326562575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8734794806007260217708383 13102192209010890326562575)
      ·
        refine ⟨19653288313516335489843863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13102192209010890326562575 19653288313516335489843863)
        ·
          refine ⟨29479932470274503234765795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19653288313516335489843863 29479932470274503234765795)
          ·
            refine ⟨44219898705411754852148693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29479932470274503234765795 44219898705411754852148693)
            ·
              refine ⟨1036403875908088004347235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 44219898705411754852148693 1036403875908088004347235)
              ·
                refine ⟨1554605813862132006520853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036403875908088004347235 1554605813862132006520853)
                ·
                  refine ⟨72872147524787437805665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1554605813862132006520853 72872147524787437805665)
                  ·
                    rfl

theorem cell23_1277262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_1277262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277262 prefixEnd_1277262 := by exact prefixLift 1277262
  have htrace : WordTrace (prefixWord ++ tailWord_1277262) baseStart_1277262 baseEnd_1277262 := by
    simpa [prefixWord, tailWord_1277262, baseEnd_1277262] using wordTrace_append hprefix tailTrace_1277262
  have hstable : (prefixWord ++ tailWord_1277262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277262).length < 2 ^ (prefixWord ++ tailWord_1277262).sum := by decide
  have hdescent : baseEnd_1277262 < baseStart_1277262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277272 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 3, 1, 3]
def baseStart_1277272 : Nat := 118140960795 + 1277272 * 2 ^ 59
def prefixEnd_1277272 : Nat := 4983230072969 + 3 ^ 40 * 1277272 * 2
def baseEnd_1277272 : Nat := 655854462529631901125939

theorem tailTrace_1277272 : CollatzResearch.WordTrace tailWord_1277272 prefixEnd_1277272 655854462529631901125939 := by
  unfold tailWord_1277272
  simp only [CollatzResearch.WordTrace]
  refine ⟨23292968514334579767821035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31057291352446106357094713 23292968514334579767821035)
  ·
    refine ⟨34939452771501869651731553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23292968514334579767821035 34939452771501869651731553)
    ·
      refine ⟨26204589578626402238798665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34939452771501869651731553 26204589578626402238798665)
      ·
        refine ⟨19653442183969801679098999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26204589578626402238798665 19653442183969801679098999)
        ·
          refine ⟨29480163275954702518648499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19653442183969801679098999 29480163275954702518648499)
          ·
            refine ⟨44220244913932053777972749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29480163275954702518648499 44220244913932053777972749)
            ·
              refine ⟨16582591842724520166739781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44220244913932053777972749 16582591842724520166739781)
              ·
                refine ⟨3109235970510847531263709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16582591842724520166739781 3109235970510847531263709)
                ·
                  refine ⟨1165963488941567824223891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3109235970510847531263709 1165963488941567824223891)
                  ·
                    refine ⟨1748945233412351736335837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1165963488941567824223891 1748945233412351736335837)
                    ·
                      refine ⟨655854462529631901125939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1748945233412351736335837 655854462529631901125939)
                      ·
                        rfl

theorem cell23_1277272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_1277272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277272 prefixEnd_1277272 := by exact prefixLift 1277272
  have htrace : WordTrace (prefixWord ++ tailWord_1277272) baseStart_1277272 baseEnd_1277272 := by
    simpa [prefixWord, tailWord_1277272, baseEnd_1277272] using wordTrace_append hprefix tailTrace_1277272
  have hstable : (prefixWord ++ tailWord_1277272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277272).length < 2 ^ (prefixWord ++ tailWord_1277272).sum := by decide
  have hdescent : baseEnd_1277272 < baseStart_1277272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277289 : List Nat := [1, 2, 1, 1, 1, 3, 2, 7, 1, 1, 3]
def baseStart_1277289 : Nat := 118140960795 + 1277289 * 2 ^ 59
def prefixEnd_1277289 : Nat := 4983230072969 + 3 ^ 40 * 1277289 * 2
def baseEnd_1277289 : Nat := 655863191700758334613361

theorem tailTrace_1277289 : CollatzResearch.WordTrace tailWord_1277289 prefixEnd_1277289 655863191700758334613361 := by
  unfold tailWord_1277289
  simp only [CollatzResearch.WordTrace]
  refine ⟨46586557069607571439010921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31057704713071714292673947 46586557069607571439010921)
  ·
    refine ⟨34939917802205678579258191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46586557069607571439010921 34939917802205678579258191)
    ·
      refine ⟨52409876703308517868887287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34939917802205678579258191 52409876703308517868887287)
      ·
        refine ⟨78614815054962776803330931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52409876703308517868887287 78614815054962776803330931)
        ·
          refine ⟨117922222582444165204996397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78614815054962776803330931 117922222582444165204996397)
          ·
            refine ⟨44220833468416561951873649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117922222582444165204996397 44220833468416561951873649)
            ·
              refine ⟨33165625101312421463905237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44220833468416561951873649 33165625101312421463905237)
              ·
                refine ⟨777319338312009878060279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33165625101312421463905237 777319338312009878060279)
                ·
                  refine ⟨1165979007468014817090419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777319338312009878060279 1165979007468014817090419)
                  ·
                    refine ⟨1748968511202022225635629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1165979007468014817090419 1748968511202022225635629)
                    ·
                      refine ⟨655863191700758334613361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1748968511202022225635629 655863191700758334613361)
                      ·
                        rfl

theorem cell23_1277289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 1, 1, 3].length) (baseStart_1277289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277289 prefixEnd_1277289 := by exact prefixLift 1277289
  have htrace : WordTrace (prefixWord ++ tailWord_1277289) baseStart_1277289 baseEnd_1277289 := by
    simpa [prefixWord, tailWord_1277289, baseEnd_1277289] using wordTrace_append hprefix tailTrace_1277289
  have hstable : (prefixWord ++ tailWord_1277289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277289).length < 2 ^ (prefixWord ++ tailWord_1277289).sum := by decide
  have hdescent : baseEnd_1277289 < baseStart_1277289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277292 : List Nat := [2, 2, 1, 1, 5, 1, 2, 3, 1, 5]
def baseStart_1277292 : Nat := 118140960795 + 1277292 * 2 ^ 59
def prefixEnd_1277292 : Nat := 4983230072969 + 3 ^ 40 * 1277292 * 2
def baseEnd_1277292 : Nat := 218621577380907274291949

theorem tailTrace_1277292 : CollatzResearch.WordTrace tailWord_1277292 prefixEnd_1277292 218621577380907274291949 := by
  unfold tailWord_1277292
  simp only [CollatzResearch.WordTrace]
  refine ⟨23293333244298351475685065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31057777659064468634246753 23293333244298351475685065)
  ·
    refine ⟨17469999933223763606763799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23293333244298351475685065 17469999933223763606763799)
    ·
      refine ⟨26204999899835645410145699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17469999933223763606763799 26204999899835645410145699)
      ·
        refine ⟨39307499849753468115218549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26204999899835645410145699 39307499849753468115218549)
        ·
          refine ⟨3685078110914387635801739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39307499849753468115218549 3685078110914387635801739)
          ·
            refine ⟨5527617166371581453702609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3685078110914387635801739 5527617166371581453702609)
            ·
              refine ⟨4145712874778686090276957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5527617166371581453702609 4145712874778686090276957)
              ·
                refine ⟨1554642328042007283853859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4145712874778686090276957 1554642328042007283853859)
                ·
                  refine ⟨2331963492063010925780789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554642328042007283853859 2331963492063010925780789)
                  ·
                    refine ⟨218621577380907274291949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2331963492063010925780789 218621577380907274291949)
                    ·
                      rfl

theorem cell23_1277292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_1277292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277292 prefixEnd_1277292 := by exact prefixLift 1277292
  have htrace : WordTrace (prefixWord ++ tailWord_1277292) baseStart_1277292 baseEnd_1277292 := by
    simpa [prefixWord, tailWord_1277292, baseEnd_1277292] using wordTrace_append hprefix tailTrace_1277292
  have hstable : (prefixWord ++ tailWord_1277292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277292).length < 2 ^ (prefixWord ++ tailWord_1277292).sum := by decide
  have hdescent : baseEnd_1277292 < baseStart_1277292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277326 : List Nat := [4, 1, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_1277326 : Nat := 118140960795 + 1277326 * 2 ^ 59
def prefixEnd_1277326 : Nat := 4983230072969 + 3 ^ 40 * 1277326 * 2
def baseEnd_1277326 : Nat := 218627396828324896616897

theorem tailTrace_1277326 : CollatzResearch.WordTrace tailWord_1277326 prefixEnd_1277326 218627396828324896616897 := by
  unfold tailWord_1277326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5823488321309190844763479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31058604380315684505405221 5823488321309190844763479)
  ·
    refine ⟨8735232481963786267145219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5823488321309190844763479 8735232481963786267145219)
    ·
      refine ⟨13102848722945679400717829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8735232481963786267145219 13102848722945679400717829)
      ·
        refine ⟨2456784135552314887634593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13102848722945679400717829 2456784135552314887634593)
        ·
          refine ⟨1842588101664236165725945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2456784135552314887634593 1842588101664236165725945)
          ·
            refine ⟨1381941076248177124294459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1842588101664236165725945 1381941076248177124294459)
            ·
              refine ⟨2072911614372265686441689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381941076248177124294459 2072911614372265686441689)
              ·
                refine ⟨1554683710779199264831267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072911614372265686441689 1554683710779199264831267)
                ·
                  refine ⟨2332025566168798897246901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554683710779199264831267 2332025566168798897246901)
                  ·
                    refine ⟨218627396828324896616897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2332025566168798897246901 218627396828324896616897)
                    ·
                      rfl

theorem cell23_1277326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_1277326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277326 prefixEnd_1277326 := by exact prefixLift 1277326
  have htrace : WordTrace (prefixWord ++ tailWord_1277326) baseStart_1277326 baseEnd_1277326 := by
    simpa [prefixWord, tailWord_1277326, baseEnd_1277326] using wordTrace_append hprefix tailTrace_1277326
  have hstable : (prefixWord ++ tailWord_1277326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277326).length < 2 ^ (prefixWord ++ tailWord_1277326).sum := by decide
  have hdescent : baseEnd_1277326 < baseStart_1277326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277346 : List Nat := [3, 3, 1, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_1277346 : Nat := 118140960795 + 1277346 * 2 ^ 59
def prefixEnd_1277346 : Nat := 4983230072969 + 3 ^ 40 * 1277346 * 2
def baseEnd_1277346 : Nat := 655892460098064611600599

theorem tailTrace_1277346 : CollatzResearch.WordTrace tailWord_1277346 prefixEnd_1277346 655892460098064611600599 := by
  unfold tailWord_1277346
  simp only [CollatzResearch.WordTrace]
  refine ⟨11647159007600267543458973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31059090686934046782557261 11647159007600267543458973)
  ·
    refine ⟨4367684627850100328797115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11647159007600267543458973 4367684627850100328797115)
    ·
      refine ⟨6551526941775150493195673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4367684627850100328797115 6551526941775150493195673)
      ·
        refine ⟨4913645206331362869896755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6551526941775150493195673 4913645206331362869896755)
        ·
          refine ⟨7370467809497044304845133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4913645206331362869896755 7370467809497044304845133)
          ·
            refine ⟨2763925428561391614316925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7370467809497044304845133 2763925428561391614316925)
            ·
              refine ⟨1036472035710521855368847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2763925428561391614316925 1036472035710521855368847)
              ·
                refine ⟨1554708053565782783053271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036472035710521855368847 1554708053565782783053271)
                ·
                  refine ⟨2332062080348674174579907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554708053565782783053271 2332062080348674174579907)
                  ·
                    refine ⟨3498093120523011261869861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2332062080348674174579907 3498093120523011261869861)
                    ·
                      refine ⟨655892460098064611600599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3498093120523011261869861 655892460098064611600599)
                      ·
                        rfl

theorem cell23_1277346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_1277346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277346 prefixEnd_1277346 := by exact prefixLift 1277346
  have htrace : WordTrace (prefixWord ++ tailWord_1277346) baseStart_1277346 baseEnd_1277346 := by
    simpa [prefixWord, tailWord_1277346, baseEnd_1277346] using wordTrace_append hprefix tailTrace_1277346
  have hstable : (prefixWord ++ tailWord_1277346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277346).length < 2 ^ (prefixWord ++ tailWord_1277346).sum := by decide
  have hdescent : baseEnd_1277346 < baseStart_1277346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277352 : List Nat := [2, 1, 6, 1, 2, 11]
def baseStart_1277352 : Nat := 118140960795 + 1277352 * 2 ^ 59
def prefixEnd_1277352 : Nat := 4983230072969 + 3 ^ 40 * 1277352 * 2
def baseEnd_1277352 : Nat := 2699158604864162914097

theorem tailTrace_1277352 : CollatzResearch.WordTrace tailWord_1277352 prefixEnd_1277352 2699158604864162914097 := by
  unfold tailWord_1277352
  simp only [CollatzResearch.WordTrace]
  refine ⟨23294427434189666599277155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31059236578919555465702873 23294427434189666599277155)
  ·
    refine ⟨34941641151284499898915733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23294427434189666599277155 34941641151284499898915733)
    ·
      refine ⟨1637889428966460932761675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34941641151284499898915733 1637889428966460932761675)
      ·
        refine ⟨2456834143449691399142513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637889428966460932761675 2456834143449691399142513)
        ·
          refine ⟨1842625607587268549356885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2456834143449691399142513 1842625607587268549356885)
          ·
            refine ⟨2699158604864162914097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1842625607587268549356885 2699158604864162914097)
            ·
              rfl

theorem cell23_1277352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 11].length) (baseStart_1277352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277352 prefixEnd_1277352 := by exact prefixLift 1277352
  have htrace : WordTrace (prefixWord ++ tailWord_1277352) baseStart_1277352 baseEnd_1277352 := by
    simpa [prefixWord, tailWord_1277352, baseEnd_1277352] using wordTrace_append hprefix tailTrace_1277352
  have hstable : (prefixWord ++ tailWord_1277352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277352).length < 2 ^ (prefixWord ++ tailWord_1277352).sum := by decide
  have hdescent : baseEnd_1277352 < baseStart_1277352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277369 : List Nat := [1, 2, 1, 4, 5, 1, 1, 8]
def baseStart_1277369 : Nat := 118140960795 + 1277369 * 2 ^ 59
def prefixEnd_1277369 : Nat := 4983230072969 + 3 ^ 40 * 1277369 * 2
def baseEnd_1277369 : Nat := 24292750746411778578259

theorem tailTrace_1277369 : CollatzResearch.WordTrace tailWord_1277369 prefixEnd_1277369 24292750746411778578259 := by
  unfold tailWord_1277369
  simp only [CollatzResearch.WordTrace]
  refine ⟨46589474909317745101923161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31059649939545163401282107 46589474909317745101923161)
  ·
    refine ⟨34942106181988308826442371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46589474909317745101923161 34942106181988308826442371)
    ·
      refine ⟨52413159272982463239663557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34942106181988308826442371 52413159272982463239663557)
      ·
        refine ⟨9827467363684211857436917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52413159272982463239663557 9827467363684211857436917)
        ·
          refine ⟨921325065345394861634711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9827467363684211857436917 921325065345394861634711)
          ·
            refine ⟨1381987598018092292452067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 921325065345394861634711 1381987598018092292452067)
            ·
              refine ⟨2072981397027138438678101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381987598018092292452067 2072981397027138438678101)
              ·
                refine ⟨24292750746411778578259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2072981397027138438678101 24292750746411778578259)
                ·
                  rfl

theorem cell23_1277369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 8].length) (baseStart_1277369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277369 prefixEnd_1277369 := by exact prefixLift 1277369
  have htrace : WordTrace (prefixWord ++ tailWord_1277369) baseStart_1277369 baseEnd_1277369 := by
    simpa [prefixWord, tailWord_1277369, baseEnd_1277369] using wordTrace_append hprefix tailTrace_1277369
  have hstable : (prefixWord ++ tailWord_1277369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277369).length < 2 ^ (prefixWord ++ tailWord_1277369).sum := by decide
  have hdescent : baseEnd_1277369 < baseStart_1277369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277379 : List Nat := [1, 1, 1, 3, 1, 1, 6, 3, 2, 1, 3]
def baseStart_1277379 : Nat := 118140960795 + 1277379 * 2 ^ 59
def prefixEnd_1277379 : Nat := 4983230072969 + 3 ^ 40 * 1277379 * 2
def baseEnd_1277379 : Nat := 655909404959662982487947

theorem tailTrace_1277379 : CollatzResearch.WordTrace tailWord_1277379 prefixEnd_1277379 655909404959662982487947 := by
  unfold tailWord_1277379
  simp only [CollatzResearch.WordTrace]
  refine ⟨46589839639281516809787191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31059893092854344539858127 46589839639281516809787191)
  ·
    refine ⟨69884759458922275214680787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46589839639281516809787191 69884759458922275214680787)
    ·
      refine ⟨104827139188383412822021181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69884759458922275214680787 104827139188383412822021181)
      ·
        refine ⟨39310177195643779808257943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104827139188383412822021181 39310177195643779808257943)
        ·
          refine ⟨58965265793465669712386915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39310177195643779808257943 58965265793465669712386915)
          ·
            refine ⟨88447898690198504568580373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58965265793465669712386915 88447898690198504568580373)
            ·
              refine ⟨4145995251103054901652205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 88447898690198504568580373 4145995251103054901652205)
              ·
                refine ⟨1554748219163645588119577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4145995251103054901652205 1554748219163645588119577)
                ·
                  refine ⟨1166061164372734191089683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1554748219163645588119577 1166061164372734191089683)
                  ·
                    refine ⟨1749091746559101286634525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1166061164372734191089683 1749091746559101286634525)
                    ·
                      refine ⟨655909404959662982487947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1749091746559101286634525 655909404959662982487947)
                      ·
                        rfl

theorem cell23_1277379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_1277379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277379 prefixEnd_1277379 := by exact prefixLift 1277379
  have htrace : WordTrace (prefixWord ++ tailWord_1277379) baseStart_1277379 baseEnd_1277379 := by
    simpa [prefixWord, tailWord_1277379, baseEnd_1277379] using wordTrace_append hprefix tailTrace_1277379
  have hstable : (prefixWord ++ tailWord_1277379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277379).length < 2 ^ (prefixWord ++ tailWord_1277379).sum := by decide
  have hdescent : baseEnd_1277379 < baseStart_1277379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277385 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 4, 3, 4]
def baseStart_1277385 : Nat := 118140960795 + 1277385 * 2 ^ 59
def prefixEnd_1277385 : Nat := 4983230072969 + 3 ^ 40 * 1277385 * 2
def baseEnd_1277385 : Nat := 655912485843589959012919

theorem tailTrace_1277385 : CollatzResearch.WordTrace tailWord_1277385 prefixEnd_1277385 655912485843589959012919 := by
  unfold tailWord_1277385
  simp only [CollatzResearch.WordTrace]
  refine ⟨46590058477259779834505609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31060038984839853223003739 46590058477259779834505609)
  ·
    refine ⟨34942543857944834875879207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46590058477259779834505609 34942543857944834875879207)
    ·
      refine ⟨52413815786917252313818811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34942543857944834875879207 52413815786917252313818811)
      ·
        refine ⟨78620723680375878470728217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52413815786917252313818811 78620723680375878470728217)
        ·
          refine ⟨58965542760281908853046163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78620723680375878470728217 58965542760281908853046163)
          ·
            refine ⟨88448314140422863279569245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58965542760281908853046163 88448314140422863279569245)
            ·
              refine ⟨33168117802658573729838467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88448314140422863279569245 33168117802658573729838467)
              ·
                refine ⟨49752176703987860594757701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33168117802658573729838467 49752176703987860594757701)
                ·
                  refine ⟨9328533131997723861517069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49752176703987860594757701 9328533131997723861517069)
                  ·
                    refine ⟨3498199924499146448068901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9328533131997723861517069 3498199924499146448068901)
                    ·
                      refine ⟨655912485843589959012919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3498199924499146448068901 655912485843589959012919)
                      ·
                        rfl

theorem cell23_1277385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_1277385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277385 prefixEnd_1277385 := by exact prefixLift 1277385
  have htrace : WordTrace (prefixWord ++ tailWord_1277385) baseStart_1277385 baseEnd_1277385 := by
    simpa [prefixWord, tailWord_1277385, baseEnd_1277385] using wordTrace_append hprefix tailTrace_1277385
  have hstable : (prefixWord ++ tailWord_1277385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277385).length < 2 ^ (prefixWord ++ tailWord_1277385).sum := by decide
  have hdescent : baseEnd_1277385 < baseStart_1277385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277413 : List Nat := [1, 3, 1, 5, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1277413 : Nat := 118140960795 + 1277413 * 2 ^ 59
def prefixEnd_1277413 : Nat := 4983230072969 + 3 ^ 40 * 1277413 * 2
def baseEnd_1277413 : Nat := 655926863301915849462791

theorem tailTrace_1277413 : CollatzResearch.WordTrace tailWord_1277413 prefixEnd_1277413 655926863301915849462791 := by
  unfold tailWord_1277413
  simp only [CollatzResearch.WordTrace]
  refine ⟨46591079721158340616524893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31060719814105560411016595 46591079721158340616524893)
  ·
    refine ⟨17471654895434377731196835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46591079721158340616524893 17471654895434377731196835)
    ·
      refine ⟨26207482343151566596795253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17471654895434377731196835 26207482343151566596795253)
      ·
        refine ⟨2456951469670459368449555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26207482343151566596795253 2456951469670459368449555)
        ·
          refine ⟨3685427204505689052674333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2456951469670459368449555 3685427204505689052674333)
          ·
            refine ⟨1382035201689633394752875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3685427204505689052674333 1382035201689633394752875)
            ·
              refine ⟨2073052802534450092129313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1382035201689633394752875 2073052802534450092129313)
              ·
                refine ⟨1554789601900837569096985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2073052802534450092129313 1554789601900837569096985)
                ·
                  refine ⟨1166092201425628176822739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1554789601900837569096985 1166092201425628176822739)
                  ·
                    refine ⟨1749138302138442265234109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1166092201425628176822739 1749138302138442265234109)
                    ·
                      refine ⟨655926863301915849462791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1749138302138442265234109 655926863301915849462791)
                      ·
                        rfl

theorem cell23_1277413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1277413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277413 prefixEnd_1277413 := by exact prefixLift 1277413
  have htrace : WordTrace (prefixWord ++ tailWord_1277413) baseStart_1277413 baseEnd_1277413 := by
    simpa [prefixWord, tailWord_1277413, baseEnd_1277413] using wordTrace_append hprefix tailTrace_1277413
  have hstable : (prefixWord ++ tailWord_1277413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277413).length < 2 ^ (prefixWord ++ tailWord_1277413).sum := by decide
  have hdescent : baseEnd_1277413 < baseStart_1277413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277429 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1277429 : Nat := 118140960795 + 1277429 * 2 ^ 59
def prefixEnd_1277429 : Nat := 4983230072969 + 3 ^ 40 * 1277429 * 2
def baseEnd_1277429 : Nat := 218645026330795928954239

theorem tailTrace_1277429 : CollatzResearch.WordTrace tailWord_1277429 prefixEnd_1277429 218645026330795928954239 := by
  unfold tailWord_1277429
  simp only [CollatzResearch.WordTrace]
  refine ⟨46591663289100375349107341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31061108859400250232738227 46591663289100375349107341)
  ·
    refine ⟨17471873733412640755915253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46591663289100375349107341 17471873733412640755915253)
    ·
      refine ⟨1637988162507435070867055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17471873733412640755915253 1637988162507435070867055)
      ·
        refine ⟨2456982243761152606300583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637988162507435070867055 2456982243761152606300583)
        ·
          refine ⟨3685473365641728909450875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2456982243761152606300583 3685473365641728909450875)
          ·
            refine ⟨5528210048462593364176313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3685473365641728909450875 5528210048462593364176313)
            ·
              refine ⟨4146157536346945023132235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5528210048462593364176313 4146157536346945023132235)
              ·
                refine ⟨6219236304520417534698353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4146157536346945023132235 6219236304520417534698353)
                ·
                  refine ⟨4664427228390313151023765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6219236304520417534698353 4664427228390313151023765)
                  ·
                    refine ⟨218645026330795928954239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4664427228390313151023765 218645026330795928954239)
                    ·
                      rfl

theorem cell23_1277429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1277429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277429 prefixEnd_1277429 := by exact prefixLift 1277429
  have htrace : WordTrace (prefixWord ++ tailWord_1277429) baseStart_1277429 baseEnd_1277429 := by
    simpa [prefixWord, tailWord_1277429, baseEnd_1277429] using wordTrace_append hprefix tailTrace_1277429
  have hstable : (prefixWord ++ tailWord_1277429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277429).length < 2 ^ (prefixWord ++ tailWord_1277429).sum := by decide
  have hdescent : baseEnd_1277429 < baseStart_1277429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277432 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_1277432 : Nat := 118140960795 + 1277432 * 2 ^ 59
def prefixEnd_1277432 : Nat := 4983230072969 + 3 ^ 40 * 1277432 * 2
def baseEnd_1277432 : Nat := 655936619434351275125203

theorem tailTrace_1277432 : CollatzResearch.WordTrace tailWord_1277432 prefixEnd_1277432 655936619434351275125203 := by
  unfold tailWord_1277432
  simp only [CollatzResearch.WordTrace]
  refine ⟨23295886354044753430733275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31061181805393004574311033 23295886354044753430733275)
  ·
    refine ⟨34943829531067130146099913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23295886354044753430733275 34943829531067130146099913)
    ·
      refine ⟨26207872148300347609574935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34943829531067130146099913 26207872148300347609574935)
      ·
        refine ⟨39311808222450521414362403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26207872148300347609574935 39311808222450521414362403)
        ·
          refine ⟨58967712333675782121543605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39311808222450521414362403 58967712333675782121543605)
          ·
            refine ⟨5528223031282104573894713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58967712333675782121543605 5528223031282104573894713)
            ·
              refine ⟨4146167273461578430421035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5528223031282104573894713 4146167273461578430421035)
              ·
                refine ⟨6219250910192367645631553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4146167273461578430421035 6219250910192367645631553)
                ·
                  refine ⟨4664438182644275734223665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6219250910192367645631553 4664438182644275734223665)
                  ·
                    refine ⟨3498328636983206800667749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4664438182644275734223665 3498328636983206800667749)
                    ·
                      refine ⟨655936619434351275125203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3498328636983206800667749 655936619434351275125203)
                      ·
                        rfl

theorem cell23_1277432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_1277432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277432 prefixEnd_1277432 := by exact prefixLift 1277432
  have htrace : WordTrace (prefixWord ++ tailWord_1277432) baseStart_1277432 baseEnd_1277432 := by
    simpa [prefixWord, tailWord_1277432, baseEnd_1277432] using wordTrace_append hprefix tailTrace_1277432
  have hstable : (prefixWord ++ tailWord_1277432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277432).length < 2 ^ (prefixWord ++ tailWord_1277432).sum := by decide
  have hdescent : baseEnd_1277432 < baseStart_1277432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277436 : List Nat := [2, 2, 2, 1, 2, 1, 2, 5, 2, 2, 2]
def baseStart_1277436 : Nat := 118140960795 + 1277436 * 2 ^ 59
def prefixEnd_1277436 : Nat := 4983230072969 + 3 ^ 40 * 1277436 * 2
def baseEnd_1277436 : Nat := 655938673356969259475185

theorem tailTrace_1277436 : CollatzResearch.WordTrace tailWord_1277436 prefixEnd_1277436 655938673356969259475185 := by
  unfold tailWord_1277436
  simp only [CollatzResearch.WordTrace]
  refine ⟨23295959300037507772306081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31061279066716677029741441 23295959300037507772306081)
  ·
    refine ⟨17471969475028130829229561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23295959300037507772306081 17471969475028130829229561)
    ·
      refine ⟨13103977106271098121922171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17471969475028130829229561 13103977106271098121922171)
      ·
        refine ⟨19655965659406647182883257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13103977106271098121922171 19655965659406647182883257)
        ·
          refine ⟨14741974244554985387162443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19655965659406647182883257 14741974244554985387162443)
          ·
            refine ⟨22112961366832478080743665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14741974244554985387162443 22112961366832478080743665)
            ·
              refine ⟨16584721025124358560557749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22112961366832478080743665 16584721025124358560557749)
              ·
                refine ⟨1554817596105408615052289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16584721025124358560557749 1554817596105408615052289)
                ·
                  refine ⟨1166113197079056461289217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1554817596105408615052289 1166113197079056461289217)
                  ·
                    refine ⟨874584897809292345966913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1166113197079056461289217 874584897809292345966913)
                    ·
                      refine ⟨655938673356969259475185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 874584897809292345966913 655938673356969259475185)
                      ·
                        rfl

theorem cell23_1277436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_1277436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277436 prefixEnd_1277436 := by exact prefixLift 1277436
  have htrace : WordTrace (prefixWord ++ tailWord_1277436) baseStart_1277436 baseEnd_1277436 := by
    simpa [prefixWord, tailWord_1277436, baseEnd_1277436] using wordTrace_append hprefix tailTrace_1277436
  have hstable : (prefixWord ++ tailWord_1277436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277436).length < 2 ^ (prefixWord ++ tailWord_1277436).sum := by decide
  have hdescent : baseEnd_1277436 < baseStart_1277436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277455 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 5, 7]
def baseStart_1277455 : Nat := 118140960795 + 1277455 * 2 ^ 59
def prefixEnd_1277455 : Nat := 4983230072969 + 3 ^ 40 * 1277455 * 2
def baseEnd_1277455 : Nat := 218649476496468228379199

theorem tailTrace_1277455 : CollatzResearch.WordTrace tailWord_1277455 prefixEnd_1277455 218649476496468228379199 := by
  unfold tailWord_1277455
  simp only [CollatzResearch.WordTrace]
  refine ⟨46592611587006181789553819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31061741058004121193035879 46592611587006181789553819)
  ·
    refine ⟨69888917380509272684330729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46592611587006181789553819 69888917380509272684330729)
    ·
      refine ⟨52416688035381954513248047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69888917380509272684330729 52416688035381954513248047)
      ·
        refine ⟨78625032053072931769872071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52416688035381954513248047 78625032053072931769872071)
        ·
          refine ⟨117937548079609397654808107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78625032053072931769872071 117937548079609397654808107)
          ·
            refine ⟨176906322119414096482212161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117937548079609397654808107 176906322119414096482212161)
            ·
              refine ⟨132679741589560572361659121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176906322119414096482212161 132679741589560572361659121)
              ·
                refine ⟨99509806192170429271244341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132679741589560572361659121 99509806192170429271244341)
                ·
                  refine ⟨9329044330515977744179157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99509806192170429271244341 9329044330515977744179157)
                  ·
                    refine ⟨218649476496468228379199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9329044330515977744179157 218649476496468228379199)
                    ·
                      rfl

theorem cell23_1277455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_1277455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277455 prefixEnd_1277455 := by exact prefixLift 1277455
  have htrace : WordTrace (prefixWord ++ tailWord_1277455) baseStart_1277455 baseEnd_1277455 := by
    simpa [prefixWord, tailWord_1277455, baseEnd_1277455] using wordTrace_append hprefix tailTrace_1277455
  have hstable : (prefixWord ++ tailWord_1277455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277455).length < 2 ^ (prefixWord ++ tailWord_1277455).sum := by decide
  have hdescent : baseEnd_1277455 < baseStart_1277455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277459 : List Nat := [1, 1, 1, 2, 1, 6, 3, 3, 5]
def baseStart_1277459 : Nat := 118140960795 + 1277459 * 2 ^ 59
def prefixEnd_1277459 : Nat := 4983230072969 + 3 ^ 40 * 1277459 * 2
def baseEnd_1277459 : Nat := 72883387045780296609731

theorem tailTrace_1277459 : CollatzResearch.WordTrace tailWord_1277459 prefixEnd_1277459 72883387045780296609731 := by
  unfold tailWord_1277459
  simp only [CollatzResearch.WordTrace]
  refine ⟨46592757478991690472699431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31061838319327793648466287 46592757478991690472699431)
  ·
    refine ⟨69889136218487535709049147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46592757478991690472699431 69889136218487535709049147)
    ·
      refine ⟨104833704327731303563573721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69889136218487535709049147 104833704327731303563573721)
      ·
        refine ⟨78625278245798477672680291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104833704327731303563573721 78625278245798477672680291)
        ·
          refine ⟨117937917368697716509020437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78625278245798477672680291 117937917368697716509020437)
          ·
            refine ⟨5528339876657705461360333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117937917368697716509020437 5528339876657705461360333)
            ·
              refine ⟨2073127453746639548010125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5528339876657705461360333 2073127453746639548010125)
              ·
                refine ⟨777422795154989830503797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2073127453746639548010125 777422795154989830503797)
                ·
                  refine ⟨72883387045780296609731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 777422795154989830503797 72883387045780296609731)
                  ·
                    rfl

theorem cell23_1277459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 5].length) (baseStart_1277459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277459 prefixEnd_1277459 := by exact prefixLift 1277459
  have htrace : WordTrace (prefixWord ++ tailWord_1277459) baseStart_1277459 baseEnd_1277459 := by
    simpa [prefixWord, tailWord_1277459, baseEnd_1277459] using wordTrace_append hprefix tailTrace_1277459
  have hstable : (prefixWord ++ tailWord_1277459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277459).length < 2 ^ (prefixWord ++ tailWord_1277459).sum := by decide
  have hdescent : baseEnd_1277459 < baseStart_1277459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277509 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 2, 1, 4]
def baseStart_1277509 : Nat := 118140960795 + 1277509 * 2 ^ 59
def prefixEnd_1277509 : Nat := 4983230072969 + 3 ^ 40 * 1277509 * 2
def baseEnd_1277509 : Nat := 655976157444747473862349

theorem tailTrace_1277509 : CollatzResearch.WordTrace tailWord_1277509 prefixEnd_1277509 655976157444747473862349 := by
  unfold tailWord_1277509
  simp only [CollatzResearch.WordTrace]
  refine ⟨46594581128810549012019581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31063054085873699341346387 46594581128810549012019581)
  ·
    refine ⟨17472967923303955879507343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46594581128810549012019581 17472967923303955879507343)
    ·
      refine ⟨26209451884955933819261015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17472967923303955879507343 26209451884955933819261015)
      ·
        refine ⟨39314177827433900728891523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26209451884955933819261015 39314177827433900728891523)
        ·
          refine ⟨58971266741150851093337285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39314177827433900728891523 58971266741150851093337285)
          ·
            refine ⟨11057112513965784580000741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58971266741150851093337285 11057112513965784580000741)
            ·
              refine ⟨2073208596368584608750139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11057112513965784580000741 2073208596368584608750139)
              ·
                refine ⟨3109812894552876913125209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073208596368584608750139 3109812894552876913125209)
                ·
                  refine ⟨2332359670914657684843907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3109812894552876913125209 2332359670914657684843907)
                  ·
                    refine ⟨3498539506371986527265861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2332359670914657684843907 3498539506371986527265861)
                    ·
                      refine ⟨655976157444747473862349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3498539506371986527265861 655976157444747473862349)
                      ·
                        rfl

theorem cell23_1277509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_1277509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277509 prefixEnd_1277509 := by exact prefixLift 1277509
  have htrace : WordTrace (prefixWord ++ tailWord_1277509) baseStart_1277509 baseEnd_1277509 := by
    simpa [prefixWord, tailWord_1277509, baseEnd_1277509] using wordTrace_append hprefix tailTrace_1277509
  have hstable : (prefixWord ++ tailWord_1277509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277509).length < 2 ^ (prefixWord ++ tailWord_1277509).sum := by decide
  have hdescent : baseEnd_1277509 < baseStart_1277509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277579 : List Nat := [1, 1, 1, 1, 4, 1, 5, 3, 1, 5]
def baseStart_1277579 : Nat := 118140960795 + 1277579 * 2 ^ 59
def prefixEnd_1277579 : Nat := 4983230072969 + 3 ^ 40 * 1277579 * 2
def baseEnd_1277579 : Nat := 218670700363520733329009

theorem tailTrace_1277579 : CollatzResearch.WordTrace tailWord_1277579 prefixEnd_1277579 218670700363520733329009 := by
  unfold tailWord_1277579
  simp only [CollatzResearch.WordTrace]
  refine ⟨46597134238556950967067791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31064756159037967311378527 46597134238556950967067791)
  ·
    refine ⟨69895701357835426450601687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46597134238556950967067791 69895701357835426450601687)
    ·
      refine ⟨104843552036753139675902531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69895701357835426450601687 104843552036753139675902531)
      ·
        refine ⟨157265328055129709513853797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104843552036753139675902531 157265328055129709513853797)
        ·
          refine ⟨29487249010336820533847587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157265328055129709513853797 29487249010336820533847587)
          ·
            refine ⟨44230873515505230800771381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29487249010336820533847587 44230873515505230800771381)
            ·
              refine ⟨4146644392078615387572317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44230873515505230800771381 4146644392078615387572317)
              ·
                refine ⟨1554991647029480770339619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4146644392078615387572317 1554991647029480770339619)
                ·
                  refine ⟨2332487470544221155509429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554991647029480770339619 2332487470544221155509429)
                  ·
                    refine ⟨218670700363520733329009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2332487470544221155509429 218670700363520733329009)
                    ·
                      rfl

theorem cell23_1277579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 5].length) (baseStart_1277579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277579 prefixEnd_1277579 := by exact prefixLift 1277579
  have htrace : WordTrace (prefixWord ++ tailWord_1277579) baseStart_1277579 baseEnd_1277579 := by
    simpa [prefixWord, tailWord_1277579, baseEnd_1277579] using wordTrace_append hprefix tailTrace_1277579
  have hstable : (prefixWord ++ tailWord_1277579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277579).length < 2 ^ (prefixWord ++ tailWord_1277579).sum := by decide
  have hdescent : baseEnd_1277579 < baseStart_1277579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277629 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_1277629 : Nat := 118140960795 + 1277629 * 2 ^ 59
def prefixEnd_1277629 : Nat := 4983230072969 + 3 ^ 40 * 1277629 * 2
def baseEnd_1277629 : Nat := 656037775123287004361797

theorem tailTrace_1277629 : CollatzResearch.WordTrace tailWord_1277629 prefixEnd_1277629 656037775123287004361797 := by
  unfold tailWord_1277629
  simp only [CollatzResearch.WordTrace]
  refine ⟨46598957888375809506387941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31065971925583873004258627 46598957888375809506387941)
  ·
    refine ⟨8737304604070464282447739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46598957888375809506387941 8737304604070464282447739)
    ·
      refine ⟨13105956906105696423671609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8737304604070464282447739 13105956906105696423671609)
      ·
        refine ⟨9829467679579272317753707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13105956906105696423671609 9829467679579272317753707)
        ·
          refine ⟨14744201519368908476630561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9829467679579272317753707 14744201519368908476630561)
          ·
            refine ⟨11058151139526681357472921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14744201519368908476630561 11058151139526681357472921)
            ·
              refine ⟨8293613354645011018104691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11058151139526681357472921 8293613354645011018104691)
              ·
                refine ⟨12440420031967516527157037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8293613354645011018104691 12440420031967516527157037)
                ·
                  refine ⟨4665157511987818697683889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12440420031967516527157037 4665157511987818697683889)
                  ·
                    refine ⟨3498868133990864023262917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4665157511987818697683889 3498868133990864023262917)
                    ·
                      refine ⟨656037775123287004361797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3498868133990864023262917 656037775123287004361797)
                      ·
                        rfl

theorem cell23_1277629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_1277629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277629 prefixEnd_1277629 := by exact prefixLift 1277629
  have htrace : WordTrace (prefixWord ++ tailWord_1277629) baseStart_1277629 baseEnd_1277629 := by
    simpa [prefixWord, tailWord_1277629, baseEnd_1277629] using wordTrace_append hprefix tailTrace_1277629
  have hstable : (prefixWord ++ tailWord_1277629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277629).length < 2 ^ (prefixWord ++ tailWord_1277629).sum := by decide
  have hdescent : baseEnd_1277629 < baseStart_1277629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277636 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_1277636 : Nat := 118140960795 + 1277636 * 2 ^ 59
def prefixEnd_1277636 : Nat := 4983230072969 + 3 ^ 40 * 1277636 * 2
def baseEnd_1277636 : Nat := 656041369487868476974265

theorem tailTrace_1277636 : CollatzResearch.WordTrace tailWord_1277636 prefixEnd_1277636 656041369487868476974265 := by
  unfold tailWord_1277636
  simp only [CollatzResearch.WordTrace]
  refine ⟨23299606599675224850946381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31066142132900299801261841 23299606599675224850946381)
  ·
    refine ⟨8737352474878209319104893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23299606599675224850946381 8737352474878209319104893)
    ·
      refine ⟨3276507178079328494664335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8737352474878209319104893 3276507178079328494664335)
      ·
        refine ⟨4914760767118992741996503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3276507178079328494664335 4914760767118992741996503)
        ·
          refine ⟨7372141150678489112994755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4914760767118992741996503 7372141150678489112994755)
          ·
            refine ⟨11058211726017733669492133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7372141150678489112994755 11058211726017733669492133)
            ·
              refine ⟨2073414698628325063029775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11058211726017733669492133 2073414698628325063029775)
              ·
                refine ⟨3110122047942487594544663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073414698628325063029775 3110122047942487594544663)
                ·
                  refine ⟨4665183071913731391816995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3110122047942487594544663 4665183071913731391816995)
                  ·
                    refine ⟨6997774607870597087725493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4665183071913731391816995 6997774607870597087725493)
                    ·
                      refine ⟨656041369487868476974265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6997774607870597087725493 656041369487868476974265)
                      ·
                        rfl

theorem cell23_1277636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_1277636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277636 prefixEnd_1277636 := by exact prefixLift 1277636
  have htrace : WordTrace (prefixWord ++ tailWord_1277636) baseStart_1277636 baseEnd_1277636 := by
    simpa [prefixWord, tailWord_1277636, baseEnd_1277636] using wordTrace_append hprefix tailTrace_1277636
  have hstable : (prefixWord ++ tailWord_1277636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277636).length < 2 ^ (prefixWord ++ tailWord_1277636).sum := by decide
  have hdescent : baseEnd_1277636 < baseStart_1277636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277650 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_1277650 : Nat := 118140960795 + 1277650 * 2 ^ 59
def prefixEnd_1277650 : Nat := 4983230072969 + 3 ^ 40 * 1277650 * 2
def baseEnd_1277650 : Nat := 656048558217031422199201

theorem tailTrace_1277650 : CollatzResearch.WordTrace tailWord_1277650 prefixEnd_1277650 656048558217031422199201 := by
  unfold tailWord_1277650
  simp only [CollatzResearch.WordTrace]
  refine ⟨11649930955324932523225601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31066482547533153395268269 11649930955324932523225601)
  ·
    refine ⟨8737448216493699392419201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11649930955324932523225601 8737448216493699392419201)
    ·
      refine ⟨6553086162370274544314401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8737448216493699392419201 6553086162370274544314401)
      ·
        refine ⟨4914814621777705908235801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6553086162370274544314401 4914814621777705908235801)
        ·
          refine ⟨3686110966333279431176851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4914814621777705908235801 3686110966333279431176851)
          ·
            refine ⟨5529166449499919146765277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3686110966333279431176851 5529166449499919146765277)
            ·
              refine ⟨2073437418562469680036979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5529166449499919146765277 2073437418562469680036979)
              ·
                refine ⟨3110156127843704520055469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073437418562469680036979 3110156127843704520055469)
                ·
                  refine ⟨1166308547941389195020801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3110156127843704520055469 1166308547941389195020801)
                  ·
                    refine ⟨874731410956041896265601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1166308547941389195020801 874731410956041896265601)
                    ·
                      refine ⟨656048558217031422199201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 874731410956041896265601 656048558217031422199201)
                      ·
                        rfl

theorem cell23_1277650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_1277650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277650 prefixEnd_1277650 := by exact prefixLift 1277650
  have htrace : WordTrace (prefixWord ++ tailWord_1277650) baseStart_1277650 baseEnd_1277650 := by
    simpa [prefixWord, tailWord_1277650, baseEnd_1277650] using wordTrace_append hprefix tailTrace_1277650
  have hstable : (prefixWord ++ tailWord_1277650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277650).length < 2 ^ (prefixWord ++ tailWord_1277650).sum := by decide
  have hdescent : baseEnd_1277650 < baseStart_1277650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277660 : List Nat := [2, 2, 5, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1277660 : Nat := 118140960795 + 1277660 * 2 ^ 59
def prefixEnd_1277660 : Nat := 4983230072969 + 3 ^ 40 * 1277660 * 2
def baseEnd_1277660 : Nat := 218684564341192127691385

theorem tailTrace_1277660 : CollatzResearch.WordTrace tailWord_1277660 prefixEnd_1277660 218684564341192127691385 := by
  unfold tailWord_1277660
  simp only [CollatzResearch.WordTrace]
  refine ⟨23300044275631750900383217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31066725700842334533844289 23300044275631750900383217)
  ·
    refine ⟨17475033206723813175287413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23300044275631750900383217 17475033206723813175287413)
    ·
      refine ⟨1638284363130357485183195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17475033206723813175287413 1638284363130357485183195)
      ·
        refine ⟨2457426544695536227774793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638284363130357485183195 2457426544695536227774793)
        ·
          refine ⟨1843069908521652170831095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2457426544695536227774793 1843069908521652170831095)
          ·
            refine ⟨2764604862782478256246643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843069908521652170831095 2764604862782478256246643)
            ·
              refine ⟨4146907294173717384369965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2764604862782478256246643 4146907294173717384369965)
              ·
                refine ⟨1555090235315144019138737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4146907294173717384369965 1555090235315144019138737)
                ·
                  refine ⟨1166317676486358014354053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1555090235315144019138737 1166317676486358014354053)
                  ·
                    refine ⟨218684564341192127691385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1166317676486358014354053 218684564341192127691385)
                    ·
                      rfl

theorem cell23_1277660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1277660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277660 prefixEnd_1277660 := by exact prefixLift 1277660
  have htrace : WordTrace (prefixWord ++ tailWord_1277660) baseStart_1277660 baseEnd_1277660 := by
    simpa [prefixWord, tailWord_1277660, baseEnd_1277660] using wordTrace_append hprefix tailTrace_1277660
  have hstable : (prefixWord ++ tailWord_1277660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277660).length < 2 ^ (prefixWord ++ tailWord_1277660).sum := by decide
  have hdescent : baseEnd_1277660 < baseStart_1277660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277700 : List Nat := [2, 3, 2, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_1277700 : Nat := 118140960795 + 1277700 * 2 ^ 59
def prefixEnd_1277700 : Nat := 4983230072969 + 3 ^ 40 * 1277700 * 2
def baseEnd_1277700 : Nat := 656074232249756226573971

theorem tailTrace_1277700 : CollatzResearch.WordTrace tailWord_1277700 prefixEnd_1277700 656074232249756226573971 := by
  unfold tailWord_1277700
  simp only [CollatzResearch.WordTrace]
  refine ⟨23300773735559294316111277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31067698314079059088148369 23300773735559294316111277)
  ·
    refine ⟨8737790150834735368541729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23300773735559294316111277 8737790150834735368541729)
    ·
      refine ⟨6553342613126051526406297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8737790150834735368541729 6553342613126051526406297)
      ·
        refine ⟨4915006959844538644804723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6553342613126051526406297 4915006959844538644804723)
        ·
          refine ⟨7372510439766807967207085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4915006959844538644804723 7372510439766807967207085)
          ·
            refine ⟨2764691414912552987702657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7372510439766807967207085 2764691414912552987702657)
            ·
              refine ⟨2073518561184414740776993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2764691414912552987702657 2073518561184414740776993)
              ·
                refine ⟨1555138920888311055582745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2073518561184414740776993 1555138920888311055582745)
                ·
                  refine ⟨1166354190666233291687059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1555138920888311055582745 1166354190666233291687059)
                  ·
                    refine ⟨1749531285999349937530589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1166354190666233291687059 1749531285999349937530589)
                    ·
                      refine ⟨656074232249756226573971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1749531285999349937530589 656074232249756226573971)
                      ·
                        rfl

theorem cell23_1277700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_1277700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277700 prefixEnd_1277700 := by exact prefixLift 1277700
  have htrace : WordTrace (prefixWord ++ tailWord_1277700) baseStart_1277700 baseEnd_1277700 := by
    simpa [prefixWord, tailWord_1277700, baseEnd_1277700] using wordTrace_append hprefix tailTrace_1277700
  have hstable : (prefixWord ++ tailWord_1277700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277700).length < 2 ^ (prefixWord ++ tailWord_1277700).sum := by decide
  have hdescent : baseEnd_1277700 < baseStart_1277700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277729 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 9]
def baseStart_1277729 : Nat := 118140960795 + 1277729 * 2 ^ 59
def prefixEnd_1277729 : Nat := 4983230072969 + 3 ^ 40 * 1277729 * 2
def baseEnd_1277729 : Nat := 72898791465415179234593

theorem tailTrace_1277729 : CollatzResearch.WordTrace tailWord_1277729 prefixEnd_1277729 72898791465415179234593 := by
  unfold tailWord_1277729
  simp only [CollatzResearch.WordTrace]
  refine ⟨46602605188013526585028241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31068403458675684390018827 46602605188013526585028241)
  ·
    refine ⟨34951953891010144938771181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46602605188013526585028241 34951953891010144938771181)
    ·
      refine ⟨13106982709128804352039193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34951953891010144938771181 13106982709128804352039193)
      ·
        refine ⟨9830237031846603264029395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13106982709128804352039193 9830237031846603264029395)
        ·
          refine ⟨14745355547769904896044093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9830237031846603264029395 14745355547769904896044093)
          ·
            refine ⟨5529508330413714336016535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14745355547769904896044093 5529508330413714336016535)
            ·
              refine ⟨8294262495620571504024803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5529508330413714336016535 8294262495620571504024803)
              ·
                refine ⟨12441393743430857256037205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8294262495620571504024803 12441393743430857256037205)
                ·
                  refine ⟨72898791465415179234593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12441393743430857256037205 72898791465415179234593)
                  ·
                    rfl

theorem cell23_1277729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 9].length) (baseStart_1277729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277729 prefixEnd_1277729 := by exact prefixLift 1277729
  have htrace : WordTrace (prefixWord ++ tailWord_1277729) baseStart_1277729 baseEnd_1277729 := by
    simpa [prefixWord, tailWord_1277729, baseEnd_1277729] using wordTrace_append hprefix tailTrace_1277729
  have hstable : (prefixWord ++ tailWord_1277729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277729).length < 2 ^ (prefixWord ++ tailWord_1277729).sum := by decide
  have hdescent : baseEnd_1277729 < baseStart_1277729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277756 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_1277756 : Nat := 118140960795 + 1277756 * 2 ^ 59
def prefixEnd_1277756 : Nat := 4983230072969 + 3 ^ 40 * 1277756 * 2
def baseEnd_1277756 : Nat := 656102987166408007473713

theorem tailTrace_1277756 : CollatzResearch.WordTrace tailWord_1277756 prefixEnd_1277756 656102987166408007473713 := by
  unfold tailWord_1277756
  simp only [CollatzResearch.WordTrace]
  refine ⟨23301794979457855098130561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31069059972610473464174081 23301794979457855098130561)
  ·
    refine ⟨17476346234593391323597921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23301794979457855098130561 17476346234593391323597921)
    ·
      refine ⟨13107259675945043492698441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17476346234593391323597921 13107259675945043492698441)
      ·
        refine ⟨9830444756958782619523831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13107259675945043492698441 9830444756958782619523831)
        ·
          refine ⟨14745667135438173929285747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9830444756958782619523831 14745667135438173929285747)
          ·
            refine ⟨22118500703157260893928621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14745667135438173929285747 22118500703157260893928621)
            ·
              refine ⟨8294437763683972835223233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22118500703157260893928621 8294437763683972835223233)
              ·
                refine ⟨6220828322762979626417425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8294437763683972835223233 6220828322762979626417425)
                ·
                  refine ⟨4665621242072234719813069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6220828322762979626417425 4665621242072234719813069)
                  ·
                    refine ⟨1749607965777088019929901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4665621242072234719813069 1749607965777088019929901)
                    ·
                      refine ⟨656102987166408007473713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1749607965777088019929901 656102987166408007473713)
                      ·
                        rfl

theorem cell23_1277756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_1277756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277756 prefixEnd_1277756 := by exact prefixLift 1277756
  have htrace : WordTrace (prefixWord ++ tailWord_1277756) baseStart_1277756 baseEnd_1277756 := by
    simpa [prefixWord, tailWord_1277756, baseEnd_1277756] using wordTrace_append hprefix tailTrace_1277756
  have hstable : (prefixWord ++ tailWord_1277756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277756).length < 2 ^ (prefixWord ++ tailWord_1277756).sum := by decide
  have hdescent : baseEnd_1277756 < baseStart_1277756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277757 : List Nat := [1, 4, 1, 4, 1, 1, 3, 2, 2, 2, 2]
def baseStart_1277757 : Nat := 118140960795 + 1277757 * 2 ^ 59
def prefixEnd_1277757 : Nat := 4983230072969 + 3 ^ 40 * 1277757 * 2
def baseEnd_1277757 : Nat := 656103500647062503561209

theorem tailTrace_1277757 : CollatzResearch.WordTrace tailWord_1277757 prefixEnd_1277757 656103500647062503561209 := by
  unfold tailWord_1277757
  simp only [CollatzResearch.WordTrace]
  refine ⟨46603626431912087367047525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31069084287941391578031683 46603626431912087367047525)
  ·
    refine ⟨8738179955983516381321411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46603626431912087367047525 8738179955983516381321411)
    ·
      refine ⟨13107269933975274571982117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8738179955983516381321411 13107269933975274571982117)
      ·
        refine ⟨2457613112620363982246647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13107269933975274571982117 2457613112620363982246647)
        ·
          refine ⟨3686419668930545973369971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2457613112620363982246647 3686419668930545973369971)
          ·
            refine ⟨5529629503395818960054957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3686419668930545973369971 5529629503395818960054957)
            ·
              refine ⟨2073611063773432110020609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5529629503395818960054957 2073611063773432110020609)
              ·
                refine ⟨1555208297830074082515457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2073611063773432110020609 1555208297830074082515457)
                ·
                  refine ⟨1166406223372555561886593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1555208297830074082515457 1166406223372555561886593)
                  ·
                    refine ⟨874804667529416671414945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1166406223372555561886593 874804667529416671414945)
                    ·
                      refine ⟨656103500647062503561209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 874804667529416671414945 656103500647062503561209)
                      ·
                        rfl

theorem cell23_1277757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_1277757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277757 prefixEnd_1277757 := by exact prefixLift 1277757
  have htrace : WordTrace (prefixWord ++ tailWord_1277757) baseStart_1277757 baseEnd_1277757 := by
    simpa [prefixWord, tailWord_1277757, baseEnd_1277757] using wordTrace_append hprefix tailTrace_1277757
  have hstable : (prefixWord ++ tailWord_1277757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277757).length < 2 ^ (prefixWord ++ tailWord_1277757).sum := by decide
  have hdescent : baseEnd_1277757 < baseStart_1277757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277769 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 7]
def baseStart_1277769 : Nat := 118140960795 + 1277769 * 2 ^ 59
def prefixEnd_1277769 : Nat := 4983230072969 + 3 ^ 40 * 1277769 * 2
def baseEnd_1277769 : Nat := 656109662414916456611153

theorem tailTrace_1277769 : CollatzResearch.WordTrace tailWord_1277769 prefixEnd_1277769 656109662414916456611153 := by
  unfold tailWord_1277769
  simp only [CollatzResearch.WordTrace]
  refine ⟨46604064107868613416484361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31069376071912408944322907 46604064107868613416484361)
  ·
    refine ⟨34953048080901460062363271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46604064107868613416484361 34953048080901460062363271)
    ·
      refine ⟨52429572121352190093544907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34953048080901460062363271 52429572121352190093544907)
      ·
        refine ⟨78644358182028285140317361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52429572121352190093544907 78644358182028285140317361)
        ·
          refine ⟨58983268636521213855238021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78644358182028285140317361 58983268636521213855238021)
          ·
            refine ⟨11059362869347727597857129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58983268636521213855238021 11059362869347727597857129)
            ·
              refine ⟨8294522152010795698392847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11059362869347727597857129 8294522152010795698392847)
              ·
                refine ⟨12441783228016193547589271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8294522152010795698392847 12441783228016193547589271)
                ·
                  refine ⟨18662674842024290321383907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12441783228016193547589271 18662674842024290321383907)
                  ·
                    refine ⟨27994012263036435482075861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18662674842024290321383907 27994012263036435482075861)
                    ·
                      refine ⟨656109662414916456611153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27994012263036435482075861 656109662414916456611153)
                      ·
                        rfl

theorem cell23_1277769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_1277769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277769 prefixEnd_1277769 := by exact prefixLift 1277769
  have htrace : WordTrace (prefixWord ++ tailWord_1277769) baseStart_1277769 baseEnd_1277769 := by
    simpa [prefixWord, tailWord_1277769, baseEnd_1277769] using wordTrace_append hprefix tailTrace_1277769
  have hstable : (prefixWord ++ tailWord_1277769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277769).length < 2 ^ (prefixWord ++ tailWord_1277769).sum := by decide
  have hdescent : baseEnd_1277769 < baseStart_1277769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277813 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1277813 : Nat := 118140960795 + 1277813 * 2 ^ 59
def prefixEnd_1277813 : Nat := 4983230072969 + 3 ^ 40 * 1277813 * 2
def baseEnd_1277813 : Nat := 656132255563714284460951

theorem tailTrace_1277813 : CollatzResearch.WordTrace tailWord_1277813 prefixEnd_1277813 656132255563714284460951 := by
  unfold tailWord_1277813
  simp only [CollatzResearch.WordTrace]
  refine ⟨46605668919709208931086093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31070445946472805954057395 46605668919709208931086093)
  ·
    refine ⟨17477125844890953349157285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46605668919709208931086093 17477125844890953349157285)
    ·
      refine ⟨3276961095917053752966991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17477125844890953349157285 3276961095917053752966991)
      ·
        refine ⟨4915441643875580629450487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3276961095917053752966991 4915441643875580629450487)
        ·
          refine ⟨7373162465813370944175731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4915441643875580629450487 7373162465813370944175731)
          ·
            refine ⟨11059743698720056416263597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7373162465813370944175731 11059743698720056416263597)
            ·
              refine ⟨4147403887020021156098849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11059743698720056416263597 4147403887020021156098849)
              ·
                refine ⟨3110552915265015867074137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4147403887020021156098849 3110552915265015867074137)
                ·
                  refine ⟨2332914686448761900305603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3110552915265015867074137 2332914686448761900305603)
                  ·
                    refine ⟨3499372029673142850458405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2332914686448761900305603 3499372029673142850458405)
                    ·
                      refine ⟨656132255563714284460951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3499372029673142850458405 656132255563714284460951)
                      ·
                        rfl

theorem cell23_1277813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1277813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277813 prefixEnd_1277813 := by exact prefixLift 1277813
  have htrace : WordTrace (prefixWord ++ tailWord_1277813) baseStart_1277813 baseEnd_1277813 := by
    simpa [prefixWord, tailWord_1277813, baseEnd_1277813] using wordTrace_append hprefix tailTrace_1277813
  have hstable : (prefixWord ++ tailWord_1277813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277813).length < 2 ^ (prefixWord ++ tailWord_1277813).sum := by decide
  have hdescent : baseEnd_1277813 < baseStart_1277813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277839 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 8]
def baseStart_1277839 : Nat := 118140960795 + 1277839 * 2 ^ 59
def prefixEnd_1277839 : Nat := 4983230072969 + 3 ^ 40 * 1277839 * 2
def baseEnd_1277839 : Nat := 656145606060731182735831

theorem tailTrace_1277839 : CollatzResearch.WordTrace tailWord_1277839 prefixEnd_1277839 656145606060731182735831 := by
  unfold tailWord_1277839
  simp only [CollatzResearch.WordTrace]
  refine ⟨46606617217615015371532571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31071078145076676914355047 46606617217615015371532571)
  ·
    refine ⟨69909925826422523057298857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46606617217615015371532571 69909925826422523057298857)
    ·
      refine ⟨52432444369816892292974143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69909925826422523057298857 52432444369816892292974143)
      ·
        refine ⟨78648666554725338439461215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52432444369816892292974143 78648666554725338439461215)
        ·
          refine ⟨117972999832088007659191823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78648666554725338439461215 117972999832088007659191823)
          ·
            refine ⟨176959499748132011488787735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117972999832088007659191823 176959499748132011488787735)
            ·
              refine ⟨265439249622198017233181603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176959499748132011488787735 265439249622198017233181603)
              ·
                refine ⟨398158874433297025849772405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265439249622198017233181603 398158874433297025849772405)
                ·
                  refine ⟨37327394478121596173416163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 398158874433297025849772405 37327394478121596173416163)
                  ·
                    refine ⟨55991091717182394260124245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37327394478121596173416163 55991091717182394260124245)
                    ·
                      refine ⟨656145606060731182735831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 55991091717182394260124245 656145606060731182735831)
                      ·
                        rfl

theorem cell23_1277839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_1277839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277839 prefixEnd_1277839 := by exact prefixLift 1277839
  have htrace : WordTrace (prefixWord ++ tailWord_1277839) baseStart_1277839 baseEnd_1277839 := by
    simpa [prefixWord, tailWord_1277839, baseEnd_1277839] using wordTrace_append hprefix tailTrace_1277839
  have hstable : (prefixWord ++ tailWord_1277839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277839).length < 2 ^ (prefixWord ++ tailWord_1277839).sum := by decide
  have hdescent : baseEnd_1277839 < baseStart_1277839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277850 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3]
def baseStart_1277850 : Nat := 118140960795 + 1277850 * 2 ^ 59
def prefixEnd_1277850 : Nat := 4983230072969 + 3 ^ 40 * 1277850 * 2
def baseEnd_1277850 : Nat := 656151254347930639698281

theorem tailTrace_1277850 : CollatzResearch.WordTrace tailWord_1277850 prefixEnd_1277850 656151254347930639698281 := by
  unfold tailWord_1277850
  simp only [CollatzResearch.WordTrace]
  refine ⟨11651754605143791062545751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31071345613716776166788669 11651754605143791062545751)
  ·
    refine ⟨17477631907715686593818627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11651754605143791062545751 17477631907715686593818627)
    ·
      refine ⟨26216447861573529890727941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17477631907715686593818627 26216447861573529890727941)
      ·
        refine ⟨4915583974045036854511489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26216447861573529890727941 4915583974045036854511489)
        ·
          refine ⟨3686687980533777640883617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4915583974045036854511489 3686687980533777640883617)
          ·
            refine ⟨2765015985400333230662713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3686687980533777640883617 2765015985400333230662713)
            ·
              refine ⟨2073761989050249922997035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2765015985400333230662713 2073761989050249922997035)
              ·
                refine ⟨3110642983575374884495553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073761989050249922997035 3110642983575374884495553)
                ·
                  refine ⟨2332982237681531163371665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3110642983575374884495553 2332982237681531163371665)
                  ·
                    refine ⟨1749736678261148372528749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2332982237681531163371665 1749736678261148372528749)
                    ·
                      refine ⟨656151254347930639698281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1749736678261148372528749 656151254347930639698281)
                      ·
                        rfl

theorem cell23_1277850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_1277850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277850 prefixEnd_1277850 := by exact prefixLift 1277850
  have htrace : WordTrace (prefixWord ++ tailWord_1277850) baseStart_1277850 baseEnd_1277850 := by
    simpa [prefixWord, tailWord_1277850, baseEnd_1277850] using wordTrace_append hprefix tailTrace_1277850
  have hstable : (prefixWord ++ tailWord_1277850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277850).length < 2 ^ (prefixWord ++ tailWord_1277850).sum := by decide
  have hdescent : baseEnd_1277850 < baseStart_1277850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277903 : List Nat := [1, 1, 2, 1, 1, 5, 2, 4, 1, 1, 4]
def baseStart_1277903 : Nat := 118140960795 + 1277903 * 2 ^ 59
def prefixEnd_1277903 : Nat := 4983230072969 + 3 ^ 40 * 1277903 * 2
def baseEnd_1277903 : Nat := 656178468822618932335537

theorem tailTrace_1277903 : CollatzResearch.WordTrace tailWord_1277903 prefixEnd_1277903 656178468822618932335537 := by
  unfold tailWord_1277903
  simp only [CollatzResearch.WordTrace]
  refine ⟨46608951489383154301862363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31072634326255436201241575 46608951489383154301862363)
  ·
    refine ⟨69913427234074731452793545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46608951489383154301862363 69913427234074731452793545)
    ·
      refine ⟨52435070425556048589595159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69913427234074731452793545 52435070425556048589595159)
      ·
        refine ⟨78652605638334072884392739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52435070425556048589595159 78652605638334072884392739)
        ·
          refine ⟨117978908457501109326589109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78652605638334072884392739 117978908457501109326589109)
          ·
            refine ⟨11060522667890728999367729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117978908457501109326589109 11060522667890728999367729)
            ·
              refine ⟨8295392000918046749525797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11060522667890728999367729 8295392000918046749525797)
              ·
                refine ⟨1555386000172133765536087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8295392000918046749525797 1555386000172133765536087)
                ·
                  refine ⟨2333079000258200648304131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555386000172133765536087 2333079000258200648304131)
                  ·
                    refine ⟨3499618500387300972456197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2333079000258200648304131 3499618500387300972456197)
                    ·
                      refine ⟨656178468822618932335537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3499618500387300972456197 656178468822618932335537)
                      ·
                        rfl

theorem cell23_1277903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 1, 4].length) (baseStart_1277903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277903 prefixEnd_1277903 := by exact prefixLift 1277903
  have htrace : WordTrace (prefixWord ++ tailWord_1277903) baseStart_1277903 baseEnd_1277903 := by
    simpa [prefixWord, tailWord_1277903, baseEnd_1277903] using wordTrace_append hprefix tailTrace_1277903
  have hstable : (prefixWord ++ tailWord_1277903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277903).length < 2 ^ (prefixWord ++ tailWord_1277903).sum := by decide
  have hdescent : baseEnd_1277903 < baseStart_1277903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277914 : List Nat := [3, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3]
def baseStart_1277914 : Nat := 118140960795 + 1277914 * 2 ^ 59
def prefixEnd_1277914 : Nat := 4983230072969 + 3 ^ 40 * 1277914 * 2
def baseEnd_1277914 : Nat := 656184117109818389297987

theorem tailTrace_1277914 : CollatzResearch.WordTrace tailWord_1277914 prefixEnd_1277914 656184117109818389297987 := by
  unfold tailWord_1277914
  simp only [CollatzResearch.WordTrace]
  refine ⟨11652338173085825795128199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31072901794895535453675197 11652338173085825795128199)
  ·
    refine ⟨17478507259628738692692299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11652338173085825795128199 17478507259628738692692299)
    ·
      refine ⟨26217760889443108039038449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17478507259628738692692299 26217760889443108039038449)
      ·
        refine ⟨19663320667082331029278837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26217760889443108039038449 19663320667082331029278837)
        ·
          refine ⟨1843436312538968533994891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19663320667082331029278837 1843436312538968533994891)
          ·
            refine ⟨2765154468808452800992337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843436312538968533994891 2765154468808452800992337)
            ·
              refine ⟨2073865851606339600744253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2765154468808452800992337 2073865851606339600744253)
              ·
                refine ⟨777699694352377350279095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2073865851606339600744253 777699694352377350279095)
                ·
                  refine ⟨1166549541528566025418643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777699694352377350279095 1166549541528566025418643)
                  ·
                    refine ⟨1749824312292849038127965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1166549541528566025418643 1749824312292849038127965)
                    ·
                      refine ⟨656184117109818389297987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1749824312292849038127965 656184117109818389297987)
                      ·
                        rfl

theorem cell23_1277914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_1277914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277914 prefixEnd_1277914 := by exact prefixLift 1277914
  have htrace : WordTrace (prefixWord ++ tailWord_1277914) baseStart_1277914 baseEnd_1277914 := by
    simpa [prefixWord, tailWord_1277914, baseEnd_1277914] using wordTrace_append hprefix tailTrace_1277914
  have hstable : (prefixWord ++ tailWord_1277914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277914).length < 2 ^ (prefixWord ++ tailWord_1277914).sum := by decide
  have hdescent : baseEnd_1277914 < baseStart_1277914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277950 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1277950 : Nat := 118140960795 + 1277950 * 2 ^ 59
def prefixEnd_1277950 : Nat := 4983230072969 + 3 ^ 40 * 1277950 * 2
def baseEnd_1277950 : Nat := 656202602413380248447821

theorem tailTrace_1277950 : CollatzResearch.WordTrace tailWord_1277950 prefixEnd_1277950 656202602413380248447821 := by
  unfold tailWord_1277950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5826333215026610166102913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31073777146808587552548869 5826333215026610166102913)
  ·
    refine ⟨4369749911269957624577185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5826333215026610166102913 4369749911269957624577185)
    ·
      refine ⟨3277312433452468218432889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4369749911269957624577185 3277312433452468218432889)
      ·
        refine ⟨2457984325089351163824667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3277312433452468218432889 2457984325089351163824667)
        ·
          refine ⟨3686976487634026745737001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2457984325089351163824667 3686976487634026745737001)
          ·
            refine ⟨2765232365725520059302751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3686976487634026745737001 2765232365725520059302751)
            ·
              refine ⟨4147848548588280088954127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2765232365725520059302751 4147848548588280088954127)
              ·
                refine ⟨6221772822882420133431191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4147848548588280088954127 6221772822882420133431191)
                ·
                  refine ⟨9332659234323630200146787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6221772822882420133431191 9332659234323630200146787)
                  ·
                    refine ⟨13998988851485445300220181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9332659234323630200146787 13998988851485445300220181)
                    ·
                      refine ⟨656202602413380248447821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13998988851485445300220181 656202602413380248447821)
                      ·
                        rfl

theorem cell23_1277950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1277950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1277950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1277950 prefixEnd_1277950 := by exact prefixLift 1277950
  have htrace : WordTrace (prefixWord ++ tailWord_1277950) baseStart_1277950 baseEnd_1277950 := by
    simpa [prefixWord, tailWord_1277950, baseEnd_1277950] using wordTrace_append hprefix tailTrace_1277950
  have hstable : (prefixWord ++ tailWord_1277950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277950).length < 2 ^ (prefixWord ++ tailWord_1277950).sum := by decide
  have hdescent : baseEnd_1277950 < baseStart_1277950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
