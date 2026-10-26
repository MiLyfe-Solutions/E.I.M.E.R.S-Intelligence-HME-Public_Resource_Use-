import V185TrunkScan23Chunk0614

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3637101 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_3637101 : Nat := 118140960795 + 3637101 * 2 ^ 59
def prefixEnd_3637101 : Nat := 4983230072969 + 3 ^ 40 * 3637101 * 2
def baseEnd_3637101 : Nat := 1867581001948479559310783

theorem tailTrace_3637101 : CollatzResearch.WordTrace tailWord_3637101 prefixEnd_3637101 1867581001948479559310783 := by
  unfold tailWord_3637101
  simp only [CollatzResearch.WordTrace]
  refine ⟨132655971596411719242247157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88437314397607812828164771 132655971596411719242247157)
  ·
    refine ⟨12436497337163598678960671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132655971596411719242247157 12436497337163598678960671)
    ·
      refine ⟨18654746005745398018441007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12436497337163598678960671 18654746005745398018441007)
      ·
        refine ⟨27982119008618097027661511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18654746005745398018441007 27982119008618097027661511)
        ·
          refine ⟨41973178512927145541492267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27982119008618097027661511 41973178512927145541492267)
          ·
            refine ⟨62959767769390718312238401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41973178512927145541492267 62959767769390718312238401)
            ·
              refine ⟨47219825827043038734178801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62959767769390718312238401 47219825827043038734178801)
              ·
                refine ⟨35414869370282279050634101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47219825827043038734178801 35414869370282279050634101)
                ·
                  refine ⟨3320144003463963660996947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35414869370282279050634101 3320144003463963660996947)
                  ·
                    refine ⟨4980216005195945491495421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3320144003463963660996947 4980216005195945491495421)
                    ·
                      refine ⟨1867581001948479559310783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4980216005195945491495421 1867581001948479559310783)
                      ·
                        rfl

theorem cell23_3637101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_3637101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637101 prefixEnd_3637101 := by exact prefixLift 3637101
  have htrace : WordTrace (prefixWord ++ tailWord_3637101) baseStart_3637101 baseEnd_3637101 := by
    simpa [prefixWord, tailWord_3637101, baseEnd_3637101] using wordTrace_append hprefix tailTrace_3637101
  have hstable : (prefixWord ++ tailWord_3637101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637101).length < 2 ^ (prefixWord ++ tailWord_3637101).sum := by decide
  have hdescent : baseEnd_3637101 < baseStart_3637101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637138 : List Nat := [3, 2, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_3637138 : Nat := 118140960795 + 3637138 * 2 ^ 59
def prefixEnd_3637138 : Nat := 4983230072969 + 3 ^ 40 * 3637138 * 2
def baseEnd_3637138 : Nat := 622533333577565304849371

theorem tailTrace_3637138 : CollatzResearch.WordTrace tailWord_3637138 prefixEnd_3637138 622533333577565304849371 := by
  unfold tailWord_3637138
  simp only [CollatzResearch.WordTrace]
  refine ⟨33164330274319418640336017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88438214064851783040896045 33164330274319418640336017)
  ·
    refine ⟨24873247705739563980252013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33164330274319418640336017 24873247705739563980252013)
    ·
      refine ⟨9327467889652336492594505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24873247705739563980252013 9327467889652336492594505)
      ·
        refine ⟨6995600917239252369445879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9327467889652336492594505 6995600917239252369445879)
        ·
          refine ⟨10493401375858878554168819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6995600917239252369445879 10493401375858878554168819)
          ·
            refine ⟨15740102063788317831253229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10493401375858878554168819 15740102063788317831253229)
            ·
              refine ⟨5902538273920619186719961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15740102063788317831253229 5902538273920619186719961)
              ·
                refine ⟨4426903705440464390039971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5902538273920619186719961 4426903705440464390039971)
                ·
                  refine ⟨6640355558160696585059957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4426903705440464390039971 6640355558160696585059957)
                  ·
                    refine ⟨622533333577565304849371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6640355558160696585059957 622533333577565304849371)
                    ·
                      rfl

theorem cell23_3637138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_3637138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637138 prefixEnd_3637138 := by exact prefixLift 3637138
  have htrace : WordTrace (prefixWord ++ tailWord_3637138) baseStart_3637138 baseEnd_3637138 := by
    simpa [prefixWord, tailWord_3637138, baseEnd_3637138] using wordTrace_append hprefix tailTrace_3637138
  have hstable : (prefixWord ++ tailWord_3637138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637138).length < 2 ^ (prefixWord ++ tailWord_3637138).sum := by decide
  have hdescent : baseEnd_3637138 < baseStart_3637138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637151 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 1, 6]
def baseStart_3637151 : Nat := 118140960795 + 3637151 * 2 ^ 59
def prefixEnd_3637151 : Nat := 4983230072969 + 3 ^ 40 * 3637151 * 2
def baseEnd_3637151 : Nat := 622535558660401454561851

theorem tailTrace_3637151 : CollatzResearch.WordTrace tailWord_3637151 prefixEnd_3637151 622535558660401454561851 := by
  unfold tailWord_3637151
  simp only [CollatzResearch.WordTrace]
  refine ⟨132657795246230577781567307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88438530164153718521044871 132657795246230577781567307)
  ·
    refine ⟨198986692869345866672350961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132657795246230577781567307 198986692869345866672350961)
    ·
      refine ⟨149240019652009400004263221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198986692869345866672350961 149240019652009400004263221)
      ·
        refine ⟨13991251842375881250399677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149240019652009400004263221 13991251842375881250399677)
        ·
          refine ⟨5246719440890955468899879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13991251842375881250399677 5246719440890955468899879)
          ·
            refine ⟨7870079161336433203349819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5246719440890955468899879 7870079161336433203349819)
            ·
              refine ⟨11805118742004649805024729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7870079161336433203349819 11805118742004649805024729)
              ·
                refine ⟨8853839056503487353768547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11805118742004649805024729 8853839056503487353768547)
                ·
                  refine ⟨13280758584755231030652821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8853839056503487353768547 13280758584755231030652821)
                  ·
                    refine ⟨622535558660401454561851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13280758584755231030652821 622535558660401454561851)
                    ·
                      rfl

theorem cell23_3637151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 6].length) (baseStart_3637151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637151 prefixEnd_3637151 := by exact prefixLift 3637151
  have htrace : WordTrace (prefixWord ++ tailWord_3637151) baseStart_3637151 baseEnd_3637151 := by
    simpa [prefixWord, tailWord_3637151, baseEnd_3637151] using wordTrace_append hprefix tailTrace_3637151
  have hstable : (prefixWord ++ tailWord_3637151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637151).length < 2 ^ (prefixWord ++ tailWord_3637151).sum := by decide
  have hdescent : baseEnd_3637151 < baseStart_3637151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637181 : List Nat := [1, 4, 1, 2, 3, 3, 1, 8]
def baseStart_3637181 : Nat := 118140960795 + 3637181 * 2 ^ 59
def prefixEnd_3637181 : Nat := 4983230072969 + 3 ^ 40 * 3637181 * 2
def baseEnd_3637181 : Nat := 69171188162994046159645

theorem tailTrace_3637181 : CollatzResearch.WordTrace tailWord_3637181 prefixEnd_3637181 69171188162994046159645 := by
  unfold tailWord_3637181
  simp only [CollatzResearch.WordTrace]
  refine ⟨132658889436121892905159397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88439259624081261936772931 132658889436121892905159397)
  ·
    refine ⟨24873541769272854919717387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132658889436121892905159397 24873541769272854919717387)
    ·
      refine ⟨37310312653909282379576081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24873541769272854919717387 37310312653909282379576081)
      ·
        refine ⟨27982734490431961784682061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37310312653909282379576081 27982734490431961784682061)
        ·
          refine ⟨10493525433911985669255773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27982734490431961784682061 10493525433911985669255773)
          ·
            refine ⟨3935072037716994625970915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10493525433911985669255773 3935072037716994625970915)
            ·
              refine ⟨5902608056575491938956373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3935072037716994625970915 5902608056575491938956373)
              ·
                refine ⟨69171188162994046159645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5902608056575491938956373 69171188162994046159645)
                ·
                  rfl

theorem cell23_3637181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 8].length) (baseStart_3637181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637181 prefixEnd_3637181 := by exact prefixLift 3637181
  have htrace : WordTrace (prefixWord ++ tailWord_3637181) baseStart_3637181 baseEnd_3637181 := by
    simpa [prefixWord, tailWord_3637181, baseEnd_3637181] using wordTrace_append hprefix tailTrace_3637181
  have hstable : (prefixWord ++ tailWord_3637181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637181).length < 2 ^ (prefixWord ++ tailWord_3637181).sum := by decide
  have hdescent : baseEnd_3637181 < baseStart_3637181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637191 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 6, 1, 3]
def baseStart_3637191 : Nat := 118140960795 + 3637191 * 2 ^ 59
def prefixEnd_3637191 : Nat := 4983230072969 + 3 ^ 40 * 3637191 * 2
def baseEnd_3637191 : Nat := 1867627215207384207185369

theorem tailTrace_3637191 : CollatzResearch.WordTrace tailWord_3637191 prefixEnd_3637191 1867627215207384207185369 := by
  unfold tailWord_3637191
  simp only [CollatzResearch.WordTrace]
  refine ⟨132659254166085664613023427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88439502777390443075348951 132659254166085664613023427)
  ·
    refine ⟨198988881249128496919535141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132659254166085664613023427 198988881249128496919535141)
    ·
      refine ⟨37310415234211593172412839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198988881249128496919535141 37310415234211593172412839)
      ·
        refine ⟨55965622851317389758619259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37310415234211593172412839 55965622851317389758619259)
        ·
          refine ⟨83948434276976084637928889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55965622851317389758619259 83948434276976084637928889)
          ·
            refine ⟨62961325707732063478446667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83948434276976084637928889 62961325707732063478446667)
            ·
              refine ⟨94441988561598095217670001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62961325707732063478446667 94441988561598095217670001)
              ·
                refine ⟨70831491421198571413252501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94441988561598095217670001 70831491421198571413252501)
                ·
                  refine ⟨3320226160368683034996211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70831491421198571413252501 3320226160368683034996211)
                  ·
                    refine ⟨4980339240553024552494317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3320226160368683034996211 4980339240553024552494317)
                    ·
                      refine ⟨1867627215207384207185369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4980339240553024552494317 1867627215207384207185369)
                      ·
                        rfl

theorem cell23_3637191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_3637191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637191 prefixEnd_3637191 := by exact prefixLift 3637191
  have htrace : WordTrace (prefixWord ++ tailWord_3637191) baseStart_3637191 baseEnd_3637191 := by
    simpa [prefixWord, tailWord_3637191, baseEnd_3637191] using wordTrace_append hprefix tailTrace_3637191
  have hstable : (prefixWord ++ tailWord_3637191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637191).length < 2 ^ (prefixWord ++ tailWord_3637191).sum := by decide
  have hdescent : baseEnd_3637191 < baseStart_3637191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637338 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2]
def baseStart_3637338 : Nat := 118140960795 + 3637338 * 2 ^ 59
def prefixEnd_3637338 : Nat := 4983230072969 + 3 ^ 40 * 3637338 * 2
def baseEnd_3637338 : Nat := 1867702696863595132047193

theorem tailTrace_3637338 : CollatzResearch.WordTrace tailWord_3637338 prefixEnd_3637338 1867702696863595132047193 := by
  unfold tailWord_3637338
  simp only [CollatzResearch.WordTrace]
  refine ⟨33166153924138277179656167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88443077131035405812416445 33166153924138277179656167)
  ·
    refine ⟨49749230886207415769484251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33166153924138277179656167 49749230886207415769484251)
    ·
      refine ⟨74623846329311123654226377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49749230886207415769484251 74623846329311123654226377)
      ·
        refine ⟨55967884746983342740669783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74623846329311123654226377 55967884746983342740669783)
        ·
          refine ⟨83951827120475014111004675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55967884746983342740669783 83951827120475014111004675)
          ·
            refine ⟨125927740680712521166507013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83951827120475014111004675 125927740680712521166507013)
            ·
              refine ⟨23611451377633597718720065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125927740680712521166507013 23611451377633597718720065)
              ·
                refine ⟨17708588533225198289040049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23611451377633597718720065 17708588533225198289040049)
                ·
                  refine ⟨13281441399918898716780037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17708588533225198289040049 13281441399918898716780037)
                  ·
                    refine ⟨2490270262484793509396257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13281441399918898716780037 2490270262484793509396257)
                    ·
                      refine ⟨1867702696863595132047193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2490270262484793509396257 1867702696863595132047193)
                      ·
                        rfl

theorem cell23_3637338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_3637338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637338 prefixEnd_3637338 := by exact prefixLift 3637338
  have htrace : WordTrace (prefixWord ++ tailWord_3637338) baseStart_3637338 baseEnd_3637338 := by
    simpa [prefixWord, tailWord_3637338, baseEnd_3637338] using wordTrace_append hprefix tailTrace_3637338
  have hstable : (prefixWord ++ tailWord_3637338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637338).length < 2 ^ (prefixWord ++ tailWord_3637338).sum := by decide
  have hdescent : baseEnd_3637338 < baseStart_3637338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637358 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_3637358 : Nat := 118140960795 + 3637358 * 2 ^ 59
def prefixEnd_3637358 : Nat := 4983230072969 + 3 ^ 40 * 3637358 * 2
def baseEnd_3637358 : Nat := 1867712966476685053797101

theorem tailTrace_3637358 : CollatzResearch.WordTrace tailWord_3637358 prefixEnd_3637358 1867712966476685053797101 := by
  unfold tailWord_3637358
  simp only [CollatzResearch.WordTrace]
  refine ⟨16583168144560081516794091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88443563437653768089568485 16583168144560081516794091)
  ·
    refine ⟨24874752216840122275191137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16583168144560081516794091 24874752216840122275191137)
    ·
      refine ⟨18656064162630091706393353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24874752216840122275191137 18656064162630091706393353)
      ·
        refine ⟨13992048121972568779795015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18656064162630091706393353 13992048121972568779795015)
        ·
          refine ⟨20988072182958853169692523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13992048121972568779795015 20988072182958853169692523)
          ·
            refine ⟨31482108274438279754538785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20988072182958853169692523 31482108274438279754538785)
            ·
              refine ⟨23611581205828709815904089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31482108274438279754538785 23611581205828709815904089)
              ·
                refine ⟨17708685904371532361928067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23611581205828709815904089 17708685904371532361928067)
                ·
                  refine ⟨26563028856557298542892101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17708685904371532361928067 26563028856557298542892101)
                  ·
                    refine ⟨4980567910604493476792269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26563028856557298542892101 4980567910604493476792269)
                    ·
                      refine ⟨1867712966476685053797101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4980567910604493476792269 1867712966476685053797101)
                      ·
                        rfl

theorem cell23_3637358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_3637358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637358 prefixEnd_3637358 := by exact prefixLift 3637358
  have htrace : WordTrace (prefixWord ++ tailWord_3637358) baseStart_3637358 baseEnd_3637358 := by
    simpa [prefixWord, tailWord_3637358, baseEnd_3637358] using wordTrace_append hprefix tailTrace_3637358
  have hstable : (prefixWord ++ tailWord_3637358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637358).length < 2 ^ (prefixWord ++ tailWord_3637358).sum := by decide
  have hdescent : baseEnd_3637358 < baseStart_3637358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637361 : List Nat := [1, 2, 2, 2, 1, 1, 3, 5, 6]
def baseStart_3637361 : Nat := 118140960795 + 3637361 * 2 ^ 59
def prefixEnd_3637361 : Nat := 4983230072969 + 3 ^ 40 * 3637361 * 2
def baseEnd_3637361 : Nat := 207523834102072060228843

theorem tailTrace_3637361 : CollatzResearch.WordTrace tailWord_3637361 prefixEnd_3637361 207523834102072060228843 := by
  unfold tailWord_3637361
  simp only [CollatzResearch.WordTrace]
  refine ⟨132665454575469783646711937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88443636383646522431141291 132665454575469783646711937)
  ·
    refine ⟨99499090931602337735033953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132665454575469783646711937 99499090931602337735033953)
    ·
      refine ⟨74624318198701753301275465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99499090931602337735033953 74624318198701753301275465)
      ·
        refine ⟨55968238649026314975956599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74624318198701753301275465 55968238649026314975956599)
        ·
          refine ⟨83952357973539472463934899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55968238649026314975956599 83952357973539472463934899)
          ·
            refine ⟨125928536960309208695902349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83952357973539472463934899 125928536960309208695902349)
            ·
              refine ⟨47223201360115953260963381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125928536960309208695902349 47223201360115953260963381)
              ·
                refine ⟨4427175127510870618215317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47223201360115953260963381 4427175127510870618215317)
                ·
                  refine ⟨207523834102072060228843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4427175127510870618215317 207523834102072060228843)
                  ·
                    rfl

theorem cell23_3637361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 6].length) (baseStart_3637361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637361 prefixEnd_3637361 := by exact prefixLift 3637361
  have htrace : WordTrace (prefixWord ++ tailWord_3637361) baseStart_3637361 baseEnd_3637361 := by
    simpa [prefixWord, tailWord_3637361, baseEnd_3637361] using wordTrace_append hprefix tailTrace_3637361
  have hstable : (prefixWord ++ tailWord_3637361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637361).length < 2 ^ (prefixWord ++ tailWord_3637361).sum := by decide
  have hdescent : baseEnd_3637361 < baseStart_3637361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637405 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_3637405 : Nat := 118140960795 + 3637405 * 2 ^ 59
def prefixEnd_3637405 : Nat := 4983230072969 + 3 ^ 40 * 3637405 * 2
def baseEnd_3637405 : Nat := 1867737100067446369909385

theorem tailTrace_3637405 : CollatzResearch.WordTrace tailWord_3637405 prefixEnd_3637405 1867737100067446369909385 := by
  unfold tailWord_3637405
  simp only [CollatzResearch.WordTrace]
  refine ⟨132667059387310379161313669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88444706258206919440875779 132667059387310379161313669)
  ·
    refine ⟨24875073635120696092746313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132667059387310379161313669 24875073635120696092746313)
    ·
      refine ⟨18656305226340522069559735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24875073635120696092746313 18656305226340522069559735)
      ·
        refine ⟨27984457839510783104339603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18656305226340522069559735 27984457839510783104339603)
        ·
          refine ⟨41976686759266174656509405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27984457839510783104339603 41976686759266174656509405)
          ·
            refine ⟨15741257534724815496191027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41976686759266174656509405 15741257534724815496191027)
            ·
              refine ⟨23611886302087223244286541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15741257534724815496191027 23611886302087223244286541)
              ·
                refine ⟨8854457363282708716607453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23611886302087223244286541 8854457363282708716607453)
                ·
                  refine ⟨3320421511231015768727795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8854457363282708716607453 3320421511231015768727795)
                  ·
                    refine ⟨4980632266846523653091693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3320421511231015768727795 4980632266846523653091693)
                    ·
                      refine ⟨1867737100067446369909385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4980632266846523653091693 1867737100067446369909385)
                      ·
                        rfl

theorem cell23_3637405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_3637405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637405 prefixEnd_3637405 := by exact prefixLift 3637405
  have htrace : WordTrace (prefixWord ++ tailWord_3637405) baseStart_3637405 baseEnd_3637405 := by
    simpa [prefixWord, tailWord_3637405, baseEnd_3637405] using wordTrace_append hprefix tailTrace_3637405
  have hstable : (prefixWord ++ tailWord_3637405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637405).length < 2 ^ (prefixWord ++ tailWord_3637405).sum := by decide
  have hdescent : baseEnd_3637405 < baseStart_3637405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637445 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 5, 2, 2]
def baseStart_3637445 : Nat := 118140960795 + 3637445 * 2 ^ 59
def prefixEnd_3637445 : Nat := 4983230072969 + 3 ^ 40 * 3637445 * 2
def baseEnd_3637445 : Nat := 1867757639293626213409201

theorem tailTrace_3637445 : CollatzResearch.WordTrace tailWord_3637445 prefixEnd_3637445 1867757639293626213409201 := by
  unfold tailWord_3637445
  simp only [CollatzResearch.WordTrace]
  refine ⟨132668518307165465992769789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88445678871443643995179859 132668518307165465992769789)
  ·
    refine ⟨49750694365187049747288671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132668518307165465992769789 49750694365187049747288671)
    ·
      refine ⟨74626041547780574620933007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49750694365187049747288671 74626041547780574620933007)
      ·
        refine ⟨111939062321670861931399511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74626041547780574620933007 111939062321670861931399511)
        ·
          refine ⟨167908593482506292897099267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111939062321670861931399511 167908593482506292897099267)
          ·
            refine ⟨251862890223759439345648901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167908593482506292897099267 251862890223759439345648901)
            ·
              refine ⟨47224291916954894877309169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251862890223759439345648901 47224291916954894877309169)
              ·
                refine ⟨35418218937716171157981877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47224291916954894877309169 35418218937716171157981877)
                ·
                  refine ⟨3320458025410891046060801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35418218937716171157981877 3320458025410891046060801)
                  ·
                    refine ⟨2490343519058168284545601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3320458025410891046060801 2490343519058168284545601)
                    ·
                      refine ⟨1867757639293626213409201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2490343519058168284545601 1867757639293626213409201)
                      ·
                        rfl

theorem cell23_3637445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 2, 2].length) (baseStart_3637445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637445 prefixEnd_3637445 := by exact prefixLift 3637445
  have htrace : WordTrace (prefixWord ++ tailWord_3637445) baseStart_3637445 baseEnd_3637445 := by
    simpa [prefixWord, tailWord_3637445, baseEnd_3637445] using wordTrace_append hprefix tailTrace_3637445
  have hstable : (prefixWord ++ tailWord_3637445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637445).length < 2 ^ (prefixWord ++ tailWord_3637445).sum := by decide
  have hdescent : baseEnd_3637445 < baseStart_3637445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637448 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_3637448 : Nat := 118140960795 + 3637448 * 2 ^ 59
def prefixEnd_3637448 : Nat := 4983230072969 + 3 ^ 40 * 3637448 * 2
def baseEnd_3637448 : Nat := 1867759179735589701671687

theorem tailTrace_3637448 : CollatzResearch.WordTrace tailWord_3637448 prefixEnd_3637448 1867759179735589701671687 := by
  unfold tailWord_3637448
  simp only [CollatzResearch.WordTrace]
  refine ⟨66334313863077298752564499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88445751817436398336752665 66334313863077298752564499)
  ·
    refine ⟨99501470794615948128846749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66334313863077298752564499 99501470794615948128846749)
    ·
      refine ⟨37313051547980980548317531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99501470794615948128846749 37313051547980980548317531)
      ·
        refine ⟨55969577321971470822476297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37313051547980980548317531 55969577321971470822476297)
        ·
          refine ⟨41977182991478603116857223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55969577321971470822476297 41977182991478603116857223)
          ·
            refine ⟨62965774487217904675285835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41977182991478603116857223 62965774487217904675285835)
            ·
              refine ⟨94448661730826857012928753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62965774487217904675285835 94448661730826857012928753)
              ·
                refine ⟨70836496298120142759696565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94448661730826857012928753 70836496298120142759696565)
                ·
                  refine ⟨6640921527948763383721553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70836496298120142759696565 6640921527948763383721553)
                  ·
                    refine ⟨4980691145961572537791165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6640921527948763383721553 4980691145961572537791165)
                    ·
                      refine ⟨1867759179735589701671687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4980691145961572537791165 1867759179735589701671687)
                      ·
                        rfl

theorem cell23_3637448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_3637448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637448 prefixEnd_3637448 := by exact prefixLift 3637448
  have htrace : WordTrace (prefixWord ++ tailWord_3637448) baseStart_3637448 baseEnd_3637448 := by
    simpa [prefixWord, tailWord_3637448, baseEnd_3637448] using wordTrace_append hprefix tailTrace_3637448
  have hstable : (prefixWord ++ tailWord_3637448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637448).length < 2 ^ (prefixWord ++ tailWord_3637448).sum := by decide
  have hdescent : baseEnd_3637448 < baseStart_3637448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637458 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3637458 : Nat := 118140960795 + 3637458 * 2 ^ 59
def prefixEnd_3637458 : Nat := 4983230072969 + 3 ^ 40 * 3637458 * 2
def baseEnd_3637458 : Nat := 1867764314542134662546641

theorem tailTrace_3637458 : CollatzResearch.WordTrace tailWord_3637458 prefixEnd_3637458 1867764314542134662546641 := by
  unfold tailWord_3637458
  simp only [CollatzResearch.WordTrace]
  refine ⟨33167248114029592303248257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88445994970745579475328685 33167248114029592303248257)
  ·
    refine ⟨24875436085522194227436193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33167248114029592303248257 24875436085522194227436193)
    ·
      refine ⟨18656577064141645670577145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24875436085522194227436193 18656577064141645670577145)
      ·
        refine ⟨13992432798106234252932859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18656577064141645670577145 13992432798106234252932859)
        ·
          refine ⟨20988649197159351379399289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13992432798106234252932859 20988649197159351379399289)
          ·
            refine ⟨15741486897869513534549467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20988649197159351379399289 15741486897869513534549467)
            ·
              refine ⟨23612230346804270301824201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15741486897869513534549467 23612230346804270301824201)
              ·
                refine ⟨17709172760103202726368151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23612230346804270301824201 17709172760103202726368151)
                ·
                  refine ⟨26563759140154804089552227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17709172760103202726368151 26563759140154804089552227)
                  ·
                    refine ⟨39845638710232206134328341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26563759140154804089552227 39845638710232206134328341)
                    ·
                      refine ⟨1867764314542134662546641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39845638710232206134328341 1867764314542134662546641)
                      ·
                        rfl

theorem cell23_3637458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3637458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637458 prefixEnd_3637458 := by exact prefixLift 3637458
  have htrace : WordTrace (prefixWord ++ tailWord_3637458) baseStart_3637458 baseEnd_3637458 := by
    simpa [prefixWord, tailWord_3637458, baseEnd_3637458] using wordTrace_append hprefix tailTrace_3637458
  have hstable : (prefixWord ++ tailWord_3637458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637458).length < 2 ^ (prefixWord ++ tailWord_3637458).sum := by decide
  have hdescent : baseEnd_3637458 < baseStart_3637458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637471 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 6]
def baseStart_3637471 : Nat := 118140960795 + 3637471 * 2 ^ 59
def prefixEnd_3637471 : Nat := 4983230072969 + 3 ^ 40 * 3637471 * 2
def baseEnd_3637471 : Nat := 1867770989790643111684081

theorem tailTrace_3637471 : CollatzResearch.WordTrace tailWord_3637471 prefixEnd_3637471 1867770989790643111684081 := by
  unfold tailWord_3637471
  simp only [CollatzResearch.WordTrace]
  refine ⟨132669466605071272433216267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88446311070047514955477511 132669466605071272433216267)
  ·
    refine ⟨199004199907606908649824401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132669466605071272433216267 199004199907606908649824401)
    ·
      refine ⟨149253149930705181487368301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199004199907606908649824401 149253149930705181487368301)
      ·
        refine ⟨55969931224014443057763113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149253149930705181487368301 55969931224014443057763113)
        ·
          refine ⟨41977448418010832293322335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55969931224014443057763113 41977448418010832293322335)
          ·
            refine ⟨62966172627016248439983503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41977448418010832293322335 62966172627016248439983503)
            ·
              refine ⟨94449258940524372659975255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62966172627016248439983503 94449258940524372659975255)
              ·
                refine ⟨141673888410786558989962883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94449258940524372659975255 141673888410786558989962883)
                ·
                  refine ⟨212510832616179838484944325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141673888410786558989962883 212510832616179838484944325)
                  ·
                    refine ⟨39845781115533719715927061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 212510832616179838484944325 39845781115533719715927061)
                    ·
                      refine ⟨1867770989790643111684081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39845781115533719715927061 1867770989790643111684081)
                      ·
                        rfl

theorem cell23_3637471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_3637471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637471 prefixEnd_3637471 := by exact prefixLift 3637471
  have htrace : WordTrace (prefixWord ++ tailWord_3637471) baseStart_3637471 baseEnd_3637471 := by
    simpa [prefixWord, tailWord_3637471, baseEnd_3637471] using wordTrace_append hprefix tailTrace_3637471
  have hstable : (prefixWord ++ tailWord_3637471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637471).length < 2 ^ (prefixWord ++ tailWord_3637471).sum := by decide
  have hdescent : baseEnd_3637471 < baseStart_3637471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637481 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 2, 7]
def baseStart_3637481 : Nat := 118140960795 + 3637481 * 2 ^ 59
def prefixEnd_3637481 : Nat := 4983230072969 + 3 ^ 40 * 3637481 * 2
def baseEnd_3637481 : Nat := 622592041532396024186345

theorem tailTrace_3637481 : CollatzResearch.WordTrace tailWord_3637481 prefixEnd_3637481 622592041532396024186345 := by
  unfold tailWord_3637481
  simp only [CollatzResearch.WordTrace]
  refine ⟨132669831335035044141080297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88446554223356696094053531 132669831335035044141080297)
  ·
    refine ⟨99502373501276283105810223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132669831335035044141080297 99502373501276283105810223)
    ·
      refine ⟨149253560251914424658715335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99502373501276283105810223 149253560251914424658715335)
      ·
        refine ⟨223880340377871636988073003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149253560251914424658715335 223880340377871636988073003)
        ·
          refine ⟨335820510566807455482109505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223880340377871636988073003 335820510566807455482109505)
          ·
            refine ⟨251865382925105591611582129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335820510566807455482109505 251865382925105591611582129)
            ·
              refine ⟨188899037193829193708686597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251865382925105591611582129 188899037193829193708686597)
              ·
                refine ⟨35418569473842973820378737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188899037193829193708686597 35418569473842973820378737)
                ·
                  refine ⟨26563927105382230365284053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35418569473842973820378737 26563927105382230365284053)
                  ·
                    refine ⟨622592041532396024186345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26563927105382230365284053 622592041532396024186345)
                    ·
                      rfl

theorem cell23_3637481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_3637481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637481 prefixEnd_3637481 := by exact prefixLift 3637481
  have htrace : WordTrace (prefixWord ++ tailWord_3637481) baseStart_3637481 baseEnd_3637481 := by
    simpa [prefixWord, tailWord_3637481, baseEnd_3637481] using wordTrace_append hprefix tailTrace_3637481
  have hstable : (prefixWord ++ tailWord_3637481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637481).length < 2 ^ (prefixWord ++ tailWord_3637481).sum := by decide
  have hdescent : baseEnd_3637481 < baseStart_3637481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637512 : List Nat := [2, 1, 3, 2, 3, 1, 1, 4, 2, 1, 3]
def baseStart_3637512 : Nat := 118140960795 + 3637512 * 2 ^ 59
def prefixEnd_3637512 : Nat := 4983230072969 + 3 ^ 40 * 3637512 * 2
def baseEnd_3637512 : Nat := 1867792042497477451271393

theorem tailTrace_3637512 : CollatzResearch.WordTrace tailWord_3637512 prefixEnd_3637512 1867792042497477451271393 := by
  unfold tailWord_3637512
  simp only [CollatzResearch.WordTrace]
  refine ⟨66335480998961368217729395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88447307998615157623639193 66335480998961368217729395)
  ·
    refine ⟨99503221498442052326594093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66335480998961368217729395 99503221498442052326594093)
    ·
      refine ⟨37313708061915769622472785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99503221498442052326594093 37313708061915769622472785)
      ·
        refine ⟨27985281046436827216854589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37313708061915769622472785 27985281046436827216854589)
        ·
          refine ⟨10494480392413810206320471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27985281046436827216854589 10494480392413810206320471)
          ·
            refine ⟨15741720588620715309480707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10494480392413810206320471 15741720588620715309480707)
            ·
              refine ⟨23612580882931072964221061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15741720588620715309480707 23612580882931072964221061)
              ·
                refine ⟨4427358915549576180791449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23612580882931072964221061 4427358915549576180791449)
                ·
                  refine ⟨3320519186662182135593587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4427358915549576180791449 3320519186662182135593587)
                  ·
                    refine ⟨4980778779993273203390381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3320519186662182135593587 4980778779993273203390381)
                    ·
                      refine ⟨1867792042497477451271393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4980778779993273203390381 1867792042497477451271393)
                      ·
                        rfl

theorem cell23_3637512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_3637512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637512 prefixEnd_3637512 := by exact prefixLift 3637512
  have htrace : WordTrace (prefixWord ++ tailWord_3637512) baseStart_3637512 baseEnd_3637512 := by
    simpa [prefixWord, tailWord_3637512, baseEnd_3637512] using wordTrace_append hprefix tailTrace_3637512
  have hstable : (prefixWord ++ tailWord_3637512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637512).length < 2 ^ (prefixWord ++ tailWord_3637512).sum := by decide
  have hdescent : baseEnd_3637512 < baseStart_3637512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637518 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3637518 : Nat := 118140960795 + 3637518 * 2 ^ 59
def prefixEnd_3637518 : Nat := 4983230072969 + 3 ^ 40 * 3637518 * 2
def baseEnd_3637518 : Nat := 1867795123381404427796365

theorem tailTrace_3637518 : CollatzResearch.WordTrace tailWord_3637518 prefixEnd_3637518 1867795123381404427796365 := by
  unfold tailWord_3637518
  simp only [CollatzResearch.WordTrace]
  refine ⟨16583897604487624932522151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88447453890600666306784805 16583897604487624932522151)
  ·
    refine ⟨24875846406731437398783227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16583897604487624932522151 24875846406731437398783227)
    ·
      refine ⟨37313769610097156098174841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24875846406731437398783227 37313769610097156098174841)
      ·
        refine ⟨27985327207572867073631131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37313769610097156098174841 27985327207572867073631131)
        ·
          refine ⟨41977990811359300610446697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27985327207572867073631131 41977990811359300610446697)
          ·
            refine ⟨31483493108519475457835023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41977990811359300610446697 31483493108519475457835023)
            ·
              refine ⟨47225239662779213186752535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31483493108519475457835023 47225239662779213186752535)
              ·
                refine ⟨70837859494168819780128803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47225239662779213186752535 70837859494168819780128803)
                ·
                  refine ⟨106256789241253229670193205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70837859494168819780128803 106256789241253229670193205)
                  ·
                    refine ⟨9961573991367490281580613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106256789241253229670193205 9961573991367490281580613)
                    ·
                      refine ⟨1867795123381404427796365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9961573991367490281580613 1867795123381404427796365)
                      ·
                        rfl

theorem cell23_3637518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3637518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637518 prefixEnd_3637518 := by exact prefixLift 3637518
  have htrace : WordTrace (prefixWord ++ tailWord_3637518) baseStart_3637518 baseEnd_3637518 := by
    simpa [prefixWord, tailWord_3637518, baseEnd_3637518] using wordTrace_append hprefix tailTrace_3637518
  have hstable : (prefixWord ++ tailWord_3637518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637518).length < 2 ^ (prefixWord ++ tailWord_3637518).sum := by decide
  have hdescent : baseEnd_3637518 < baseStart_3637518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637528 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 2, 6]
def baseStart_3637528 : Nat := 118140960795 + 3637528 * 2 ^ 59
def prefixEnd_3637528 : Nat := 4983230072969 + 3 ^ 40 * 3637528 * 2
def baseEnd_3637528 : Nat := 622600086062649796223773

theorem tailTrace_3637528 : CollatzResearch.WordTrace tailWord_3637528 prefixEnd_3637528 622600086062649796223773 := by
  unfold tailWord_3637528
  simp only [CollatzResearch.WordTrace]
  refine ⟨66335772782932385584020619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88447697043909847445360825 66335772782932385584020619)
  ·
    refine ⟨99503659174398578376030929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66335772782932385584020619 99503659174398578376030929)
    ·
      refine ⟨74627744380798933782023197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99503659174398578376030929 74627744380798933782023197)
      ·
        refine ⟨27985404142799600168258699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74627744380798933782023197 27985404142799600168258699)
        ·
          refine ⟨41978106214199400252388049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27985404142799600168258699 41978106214199400252388049)
          ·
            refine ⟨31483579660649550189291037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41978106214199400252388049 31483579660649550189291037)
            ·
              refine ⟨11806342372743581320984139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31483579660649550189291037 11806342372743581320984139)
              ·
                refine ⟨17709513559115371981476209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11806342372743581320984139 17709513559115371981476209)
                ·
                  refine ⟨13282135169336528986107157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17709513559115371981476209 13282135169336528986107157)
                  ·
                    refine ⟨622600086062649796223773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13282135169336528986107157 622600086062649796223773)
                    ·
                      rfl

theorem cell23_3637528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_3637528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637528 prefixEnd_3637528 := by exact prefixLift 3637528
  have htrace : WordTrace (prefixWord ++ tailWord_3637528) baseStart_3637528 baseEnd_3637528 := by
    simpa [prefixWord, tailWord_3637528, baseEnd_3637528] using wordTrace_append hprefix tailTrace_3637528
  have hstable : (prefixWord ++ tailWord_3637528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637528).length < 2 ^ (prefixWord ++ tailWord_3637528).sum := by decide
  have hdescent : baseEnd_3637528 < baseStart_3637528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637556 : List Nat := [2, 5, 1, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_3637556 : Nat := 118140960795 + 3637556 * 2 ^ 59
def prefixEnd_3637556 : Nat := 4983230072969 + 3 ^ 40 * 3637556 * 2
def baseEnd_3637556 : Nat := 1867814635646275279121191

theorem tailTrace_3637556 : CollatzResearch.WordTrace tailWord_3637556 prefixEnd_3637556 1867814635646275279121191 := by
  unfold tailWord_3637556
  simp only [CollatzResearch.WordTrace]
  refine ⟨66336283404881665975030261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88448377873175554633373681 66336283404881665975030261)
  ·
    refine ⟨6219026569207656185159087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66336283404881665975030261 6219026569207656185159087)
    ·
      refine ⟨9328539853811484277738631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6219026569207656185159087 9328539853811484277738631)
      ·
        refine ⟨13992809780717226416607947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9328539853811484277738631 13992809780717226416607947)
        ·
          refine ⟨20989214671075839624911921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13992809780717226416607947 20989214671075839624911921)
          ·
            refine ⟨15741911003306879718683941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20989214671075839624911921 15741911003306879718683941)
            ·
              refine ⟨2951608313120039947253239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15741911003306879718683941 2951608313120039947253239)
              ·
                refine ⟨4427412469680059920879859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2951608313120039947253239 4427412469680059920879859)
                ·
                  refine ⟨6641118704520089881319789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4427412469680059920879859 6641118704520089881319789)
                  ·
                    refine ⟨2490419514195033705494921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6641118704520089881319789 2490419514195033705494921)
                    ·
                      refine ⟨1867814635646275279121191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2490419514195033705494921 1867814635646275279121191)
                      ·
                        rfl

theorem cell23_3637556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_3637556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637556 prefixEnd_3637556 := by exact prefixLift 3637556
  have htrace : WordTrace (prefixWord ++ tailWord_3637556) baseStart_3637556 baseEnd_3637556 := by
    simpa [prefixWord, tailWord_3637556, baseEnd_3637556] using wordTrace_append hprefix tailTrace_3637556
  have hstable : (prefixWord ++ tailWord_3637556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637556).length < 2 ^ (prefixWord ++ tailWord_3637556).sum := by decide
  have hdescent : baseEnd_3637556 < baseStart_3637556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637575 : List Nat := [1, 1, 4, 1, 2, 2, 1, 6, 5]
def baseStart_3637575 : Nat := 118140960795 + 3637575 * 2 ^ 59
def prefixEnd_3637575 : Nat := 4983230072969 + 3 ^ 40 * 3637575 * 2
def baseEnd_3637575 : Nat := 207536043530967856087067

theorem tailTrace_3637575 : CollatzResearch.WordTrace tailWord_3637575 prefixEnd_3637575 207536043530967856087067 := by
  unfold tailWord_3637575
  simp only [CollatzResearch.WordTrace]
  refine ⟨132673259796694498195002179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88448839864462998796668119 132673259796694498195002179)
  ·
    refine ⟨199009889695041747292503269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132673259796694498195002179 199009889695041747292503269)
    ·
      refine ⟨37314354317820327617344363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199009889695041747292503269 37314354317820327617344363)
      ·
        refine ⟨55971531476730491426016545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37314354317820327617344363 55971531476730491426016545)
        ·
          refine ⟨41978648607547868569512409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55971531476730491426016545 41978648607547868569512409)
          ·
            refine ⟨31483986455660901427134307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41978648607547868569512409 31483986455660901427134307)
            ·
              refine ⟨47225979683491352140701461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31483986455660901427134307 47225979683491352140701461)
              ·
                refine ⟨2213717797663657131595381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47225979683491352140701461 2213717797663657131595381)
                ·
                  refine ⟨207536043530967856087067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2213717797663657131595381 207536043530967856087067)
                  ·
                    rfl

theorem cell23_3637575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 5].length) (baseStart_3637575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637575 prefixEnd_3637575 := by exact prefixLift 3637575
  have htrace : WordTrace (prefixWord ++ tailWord_3637575) baseStart_3637575 baseEnd_3637575 := by
    simpa [prefixWord, tailWord_3637575, baseEnd_3637575] using wordTrace_append hprefix tailTrace_3637575
  have hstable : (prefixWord ++ tailWord_3637575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637575).length < 2 ^ (prefixWord ++ tailWord_3637575).sum := by decide
  have hdescent : baseEnd_3637575 < baseStart_3637575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637585 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 2, 3, 3]
def baseStart_3637585 : Nat := 118140960795 + 3637585 * 2 ^ 59
def prefixEnd_3637585 : Nat := 4983230072969 + 3 ^ 40 * 3637585 * 2
def baseEnd_3637585 : Nat := 1867829526585255665658557

theorem tailTrace_3637585 : CollatzResearch.WordTrace tailWord_3637585 prefixEnd_3637585 1867829526585255665658557 := by
  unfold tailWord_3637585
  simp only [CollatzResearch.WordTrace]
  refine ⟨132673624526658269902866209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88449083017772179935244139 132673624526658269902866209)
  ·
    refine ⟨99505218394993702427149657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132673624526658269902866209 99505218394993702427149657)
    ·
      refine ⟨74628913796245276820362243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99505218394993702427149657 74628913796245276820362243)
      ·
        refine ⟨111943370694367915230543365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74628913796245276820362243 111943370694367915230543365)
        ·
          refine ⟨20989382005193984105726881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111943370694367915230543365 20989382005193984105726881)
          ·
            refine ⟨15742036503895488079295161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20989382005193984105726881 15742036503895488079295161)
            ·
              refine ⟨11806527377921616059471371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15742036503895488079295161 11806527377921616059471371)
              ·
                refine ⟨17709791066882424089207057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11806527377921616059471371 17709791066882424089207057)
                ·
                  refine ⟨13282343300161818066905293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17709791066882424089207057 13282343300161818066905293)
                  ·
                    refine ⟨4980878737560681775089485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13282343300161818066905293 4980878737560681775089485)
                    ·
                      refine ⟨1867829526585255665658557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4980878737560681775089485 1867829526585255665658557)
                      ·
                        rfl

theorem cell23_3637585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_3637585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637585 prefixEnd_3637585 := by exact prefixLift 3637585
  have htrace : WordTrace (prefixWord ++ tailWord_3637585) baseStart_3637585 baseEnd_3637585 := by
    simpa [prefixWord, tailWord_3637585, baseEnd_3637585] using wordTrace_append hprefix tailTrace_3637585
  have hstable : (prefixWord ++ tailWord_3637585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637585).length < 2 ^ (prefixWord ++ tailWord_3637585).sum := by decide
  have hdescent : baseEnd_3637585 < baseStart_3637585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637628 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_3637628 : Nat := 118140960795 + 3637628 * 2 ^ 59
def prefixEnd_3637628 : Nat := 4983230072969 + 3 ^ 40 * 3637628 * 2
def baseEnd_3637628 : Nat := 1867851606253398997420859

theorem tailTrace_3637628 : CollatzResearch.WordTrace tailWord_3637628 prefixEnd_3637628 1867851606253398997420859 := by
  unfold tailWord_3637628
  simp only [CollatzResearch.WordTrace]
  refine ⟨66337596432751244123340769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88450128577001658831121025 66337596432751244123340769)
  ·
    refine ⟨49753197324563433092505577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66337596432751244123340769 49753197324563433092505577)
    ·
      refine ⟨37314897993422574819379183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49753197324563433092505577 37314897993422574819379183)
      ·
        refine ⟨55972346990133862229068775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37314897993422574819379183 55972346990133862229068775)
        ·
          refine ⟨83958520485200793343603163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55972346990133862229068775 83958520485200793343603163)
          ·
            refine ⟨125937780727801190015404745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83958520485200793343603163 125937780727801190015404745)
            ·
              refine ⟨94453335545850892511553559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125937780727801190015404745 94453335545850892511553559)
              ·
                refine ⟨141680003318776338767330339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94453335545850892511553559 141680003318776338767330339)
                ·
                  refine ⟨212520004978164508150995509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141680003318776338767330339 212520004978164508150995509)
                  ·
                    refine ⟨19923750466702922639155829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 212520004978164508150995509 19923750466702922639155829)
                    ·
                      refine ⟨1867851606253398997420859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19923750466702922639155829 1867851606253398997420859)
                      ·
                        rfl

theorem cell23_3637628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_3637628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637628 prefixEnd_3637628 := by exact prefixLift 3637628
  have htrace : WordTrace (prefixWord ++ tailWord_3637628) baseStart_3637628 baseEnd_3637628 := by
    simpa [prefixWord, tailWord_3637628, baseEnd_3637628] using wordTrace_append hprefix tailTrace_3637628
  have hstable : (prefixWord ++ tailWord_3637628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637628).length < 2 ^ (prefixWord ++ tailWord_3637628).sum := by decide
  have hdescent : baseEnd_3637628 < baseStart_3637628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637745 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_3637745 : Nat := 118140960795 + 3637745 * 2 ^ 59
def prefixEnd_3637745 : Nat := 4983230072969 + 3 ^ 40 * 3637745 * 2
def baseEnd_3637745 : Nat := 1867911683489975039657821

theorem tailTrace_3637745 : CollatzResearch.WordTrace tailWord_3637745 prefixEnd_3637745 1867911683489975039657821 := by
  unfold tailWord_3637745
  simp only [CollatzResearch.WordTrace]
  refine ⟨132679460206078617228690689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88452973470719078152460459 132679460206078617228690689)
  ·
    refine ⟨99509595154558962921518017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132679460206078617228690689 99509595154558962921518017)
    ·
      refine ⟨74632196365919222191138513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99509595154558962921518017 74632196365919222191138513)
      ·
        refine ⟨55974147274439416643353885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74632196365919222191138513 55974147274439416643353885)
        ·
          refine ⟨20990305227914781241257707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55974147274439416643353885 20990305227914781241257707)
          ·
            refine ⟨31485457841872171861886561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20990305227914781241257707 31485457841872171861886561)
            ·
              refine ⟨23614093381404128896414921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31485457841872171861886561 23614093381404128896414921)
              ·
                refine ⟨17710570036053096672311191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23614093381404128896414921 17710570036053096672311191)
                ·
                  refine ⟨26565855054079645008466787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17710570036053096672311191 26565855054079645008466787)
                  ·
                    refine ⟨39848782581119467512700181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26565855054079645008466787 39848782581119467512700181)
                    ·
                      refine ⟨1867911683489975039657821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39848782581119467512700181 1867911683489975039657821)
                      ·
                        rfl

theorem cell23_3637745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_3637745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637745 prefixEnd_3637745 := by exact prefixLift 3637745
  have htrace : WordTrace (prefixWord ++ tailWord_3637745) baseStart_3637745 baseEnd_3637745 := by
    simpa [prefixWord, tailWord_3637745, baseEnd_3637745] using wordTrace_append hprefix tailTrace_3637745
  have hstable : (prefixWord ++ tailWord_3637745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637745).length < 2 ^ (prefixWord ++ tailWord_3637745).sum := by decide
  have hdescent : baseEnd_3637745 < baseStart_3637745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637759 : List Nat := [1, 1, 2, 2, 1, 2, 7, 1, 2, 4]
def baseStart_3637759 : Nat := 118140960795 + 3637759 * 2 ^ 59
def prefixEnd_3637759 : Nat := 4983230072969 + 3 ^ 40 * 3637759 * 2
def baseEnd_3637759 : Nat := 622639624073045994960919

theorem tailTrace_3637759 : CollatzResearch.WordTrace tailWord_3637759 prefixEnd_3637759 622639624073045994960919 := by
  unfold tailWord_3637759
  simp only [CollatzResearch.WordTrace]
  refine ⟨132679970828027897619700331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88453313885351931746466887 132679970828027897619700331)
  ·
    refine ⟨199019956242041846429550497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132679970828027897619700331 199019956242041846429550497)
    ·
      refine ⟨149264967181531384822162873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199019956242041846429550497 149264967181531384822162873)
      ·
        refine ⟨111948725386148538616622155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149264967181531384822162873 111948725386148538616622155)
        ·
          refine ⟨167923088079222807924933233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111948725386148538616622155 167923088079222807924933233)
          ·
            refine ⟨125942316059417105943699925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167923088079222807924933233 125942316059417105943699925)
            ·
              refine ⟨2951773032642588420555467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 125942316059417105943699925 2951773032642588420555467)
              ·
                refine ⟨4427659548963882630833201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2951773032642588420555467 4427659548963882630833201)
                ·
                  refine ⟨3320744661722911973124901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4427659548963882630833201 3320744661722911973124901)
                  ·
                    refine ⟨622639624073045994960919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3320744661722911973124901 622639624073045994960919)
                    ·
                      rfl

theorem cell23_3637759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 2, 4].length) (baseStart_3637759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637759 prefixEnd_3637759 := by exact prefixLift 3637759
  have htrace : WordTrace (prefixWord ++ tailWord_3637759) baseStart_3637759 baseEnd_3637759 := by
    simpa [prefixWord, tailWord_3637759, baseEnd_3637759] using wordTrace_append hprefix tailTrace_3637759
  have hstable : (prefixWord ++ tailWord_3637759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637759).length < 2 ^ (prefixWord ++ tailWord_3637759).sum := by decide
  have hdescent : baseEnd_3637759 < baseStart_3637759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637772 : List Nat := [2, 2, 1, 2, 4, 1, 4, 7]
def baseStart_3637772 : Nat := 118140960795 + 3637772 * 2 ^ 59
def prefixEnd_3637772 : Nat := 4983230072969 + 3 ^ 40 * 3637772 * 2
def baseEnd_3637772 : Nat := 69182427683986904963711

theorem tailTrace_3637772 : CollatzResearch.WordTrace tailWord_3637772 prefixEnd_3637772 69182427683986904963711 := by
  unfold tailWord_3637772
  simp only [CollatzResearch.WordTrace]
  refine ⟨66340222488490400419961785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88453629984653867226615713 66340222488490400419961785)
  ·
    refine ⟨49755166866367800314971339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66340222488490400419961785 49755166866367800314971339)
    ·
      refine ⟨74632750299551700472457009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49755166866367800314971339 74632750299551700472457009)
      ·
        refine ⟨55974562724663775354342757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74632750299551700472457009 55974562724663775354342757)
        ·
          refine ⟨10495230510874457878939267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55974562724663775354342757 10495230510874457878939267)
          ·
            refine ⟨15742845766311686818408901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10495230510874457878939267 15742845766311686818408901)
            ·
              refine ⟨2951783581183441278451669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15742845766311686818408901 2951783581183441278451669)
              ·
                refine ⟨69182427683986904963711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2951783581183441278451669 69182427683986904963711)
                ·
                  rfl

theorem cell23_3637772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 7].length) (baseStart_3637772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637772 prefixEnd_3637772 := by exact prefixLift 3637772
  have htrace : WordTrace (prefixWord ++ tailWord_3637772) baseStart_3637772 baseEnd_3637772 := by
    simpa [prefixWord, tailWord_3637772, baseEnd_3637772] using wordTrace_append hprefix tailTrace_3637772
  have hstable : (prefixWord ++ tailWord_3637772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637772).length < 2 ^ (prefixWord ++ tailWord_3637772).sum := by decide
  have hdescent : baseEnd_3637772 < baseStart_3637772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637815 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 1, 8]
def baseStart_3637815 : Nat := 118140960795 + 3637815 * 2 ^ 59
def prefixEnd_3637815 : Nat := 4983230072969 + 3 ^ 40 * 3637815 * 2
def baseEnd_3637815 : Nat := 622649209045263255260833

theorem tailTrace_3637815 : CollatzResearch.WordTrace tailWord_3637815 prefixEnd_3637815 622649209045263255260833 := by
  unfold tailWord_3637815
  simp only [CollatzResearch.WordTrace]
  refine ⟨132682013315825019183738899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88454675543883346122492599 132682013315825019183738899)
  ·
    refine ⟨199023019973737528775608349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132682013315825019183738899 199023019973737528775608349)
    ·
      refine ⟨74633632490151573290853131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199023019973737528775608349 74633632490151573290853131)
      ·
        refine ⟨111950448735227359936279697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74633632490151573290853131 111950448735227359936279697)
        ·
          refine ⟨83962836551420519952209773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111950448735227359936279697 83962836551420519952209773)
          ·
            refine ⟨31486063706782694982078665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83962836551420519952209773 31486063706782694982078665)
            ·
              refine ⟨23614547780087021236558999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31486063706782694982078665 23614547780087021236558999)
              ·
                refine ⟨35421821670130531854838499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23614547780087021236558999 35421821670130531854838499)
                ·
                  refine ⟨53132732505195797782257749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35421821670130531854838499 53132732505195797782257749)
                  ·
                    refine ⟨622649209045263255260833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53132732505195797782257749 622649209045263255260833)
                    ·
                      rfl

theorem cell23_3637815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_3637815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637815 prefixEnd_3637815 := by exact prefixLift 3637815
  have htrace : WordTrace (prefixWord ++ tailWord_3637815) baseStart_3637815 baseEnd_3637815 := by
    simpa [prefixWord, tailWord_3637815, baseEnd_3637815] using wordTrace_append hprefix tailTrace_3637815
  have hstable : (prefixWord ++ tailWord_3637815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637815).length < 2 ^ (prefixWord ++ tailWord_3637815).sum := by decide
  have hdescent : baseEnd_3637815 < baseStart_3637815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637839 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 6, 2, 2]
def baseStart_3637839 : Nat := 118140960795 + 3637839 * 2 ^ 59
def prefixEnd_3637839 : Nat := 4983230072969 + 3 ^ 40 * 3637839 * 2
def baseEnd_3637839 : Nat := 1867959950671497671882389

theorem tailTrace_3637839 : CollatzResearch.WordTrace tailWord_3637839 prefixEnd_3637839 1867959950671497671882389 := by
  unfold tailWord_3637839
  simp only [CollatzResearch.WordTrace]
  refine ⟨132682888667738071282612571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88455259111825380855075047 132682888667738071282612571)
  ·
    refine ⟨199024333001607106923918857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132682888667738071282612571 199024333001607106923918857)
    ·
      refine ⟨149268249751205330192939143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199024333001607106923918857 149268249751205330192939143)
      ·
        refine ⟨223902374626807995289408715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149268249751205330192939143 223902374626807995289408715)
        ·
          refine ⟨335853561940211992934113073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223902374626807995289408715 335853561940211992934113073)
          ·
            refine ⟨251890171455158994700584805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335853561940211992934113073 251890171455158994700584805)
            ·
              refine ⟨47229407147842311506359651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251890171455158994700584805 47229407147842311506359651)
              ·
                refine ⟨70844110721763467259539477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47229407147842311506359651 70844110721763467259539477)
                ·
                  refine ⟨3320817690082662527790913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70844110721763467259539477 3320817690082662527790913)
                  ·
                    refine ⟨2490613267561996895843185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3320817690082662527790913 2490613267561996895843185)
                    ·
                      refine ⟨1867959950671497671882389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2490613267561996895843185 1867959950671497671882389)
                      ·
                        rfl

theorem cell23_3637839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 2, 2].length) (baseStart_3637839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637839 prefixEnd_3637839 := by exact prefixLift 3637839
  have htrace : WordTrace (prefixWord ++ tailWord_3637839) baseStart_3637839 baseEnd_3637839 := by
    simpa [prefixWord, tailWord_3637839, baseEnd_3637839] using wordTrace_append hprefix tailTrace_3637839
  have hstable : (prefixWord ++ tailWord_3637839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637839).length < 2 ^ (prefixWord ++ tailWord_3637839).sum := by decide
  have hdescent : baseEnd_3637839 < baseStart_3637839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637842 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_3637842 : Nat := 118140960795 + 3637842 * 2 ^ 59
def prefixEnd_3637842 : Nat := 4983230072969 + 3 ^ 40 * 3637842 * 2
def baseEnd_3637842 : Nat := 1867961491113461160144875

theorem tailTrace_3637842 : CollatzResearch.WordTrace tailWord_3637842 prefixEnd_3637842 1867961491113461160144875 := by
  unfold tailWord_3637842
  simp only [CollatzResearch.WordTrace]
  refine ⟨33170749521681800698742945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88455332057818135196647853 33170749521681800698742945)
  ·
    refine ⟨24878062141261350524057209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33170749521681800698742945 24878062141261350524057209)
    ·
      refine ⟨18658546605946012893042907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24878062141261350524057209 18658546605946012893042907)
      ·
        refine ⟨27987819908919019339564361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18658546605946012893042907 27987819908919019339564361)
        ·
          refine ⟨20990864931689264504673271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27987819908919019339564361 20990864931689264504673271)
          ·
            refine ⟨31486297397533896757009907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20990864931689264504673271 31486297397533896757009907)
            ·
              refine ⟨47229446096300845135514861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31486297397533896757009907 47229446096300845135514861)
              ·
                refine ⟨17711042286112816925818073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47229446096300845135514861 17711042286112816925818073)
                ·
                  refine ⟨13283281714584612694363555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17711042286112816925818073 13283281714584612694363555)
                  ·
                    refine ⟨19924922571876919041545333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13283281714584612694363555 19924922571876919041545333)
                    ·
                      refine ⟨1867961491113461160144875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19924922571876919041545333 1867961491113461160144875)
                      ·
                        rfl

theorem cell23_3637842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_3637842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637842 prefixEnd_3637842 := by exact prefixLift 3637842
  have htrace : WordTrace (prefixWord ++ tailWord_3637842) baseStart_3637842 baseEnd_3637842 := by
    simpa [prefixWord, tailWord_3637842, baseEnd_3637842] using wordTrace_append hprefix tailTrace_3637842
  have hstable : (prefixWord ++ tailWord_3637842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637842).length < 2 ^ (prefixWord ++ tailWord_3637842).sum := by decide
  have hdescent : baseEnd_3637842 < baseStart_3637842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637855 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 7]
def baseStart_3637855 : Nat := 118140960795 + 3637855 * 2 ^ 59
def prefixEnd_3637855 : Nat := 4983230072969 + 3 ^ 40 * 3637855 * 2
def baseEnd_3637855 : Nat := 1867968166361969609282315

theorem tailTrace_3637855 : CollatzResearch.WordTrace tailWord_3637855 prefixEnd_3637855 1867968166361969609282315 := by
  unfold tailWord_3637855
  simp only [CollatzResearch.WordTrace]
  refine ⟨132683472235680106015195019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88455648157120070676796679 132683472235680106015195019)
  ·
    refine ⟨199025208353520159022792529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132683472235680106015195019 199025208353520159022792529)
    ·
      refine ⟨149268906265140119267094397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199025208353520159022792529 149268906265140119267094397)
      ·
        refine ⟨55975839849427544725160399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149268906265140119267094397 55975839849427544725160399)
        ·
          refine ⟨83963759774141317087740599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55975839849427544725160399 83963759774141317087740599)
          ·
            refine ⟨125945639661211975631610899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83963759774141317087740599 125945639661211975631610899)
            ·
              refine ⟨188918459491817963447416349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125945639661211975631610899 188918459491817963447416349)
              ·
                refine ⟨70844422309431736292781131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188918459491817963447416349 70844422309431736292781131)
                ·
                  refine ⟨106266633464147604439171697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70844422309431736292781131 106266633464147604439171697)
                  ·
                    refine ⟨79699975098110703329378773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106266633464147604439171697 79699975098110703329378773)
                    ·
                      refine ⟨1867968166361969609282315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79699975098110703329378773 1867968166361969609282315)
                      ·
                        rfl

theorem cell23_3637855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_3637855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637855 prefixEnd_3637855 := by exact prefixLift 3637855
  have htrace : WordTrace (prefixWord ++ tailWord_3637855) baseStart_3637855 baseEnd_3637855 := by
    simpa [prefixWord, tailWord_3637855, baseEnd_3637855] using wordTrace_append hprefix tailTrace_3637855
  have hstable : (prefixWord ++ tailWord_3637855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637855).length < 2 ^ (prefixWord ++ tailWord_3637855).sum := by decide
  have hdescent : baseEnd_3637855 < baseStart_3637855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637856 : List Nat := [2, 1, 1, 3, 2, 1, 3, 4, 2, 2, 2]
def baseStart_3637856 : Nat := 118140960795 + 3637856 * 2 ^ 59
def prefixEnd_3637856 : Nat := 4983230072969 + 3 ^ 40 * 3637856 * 2
def baseEnd_3637856 : Nat := 1867968679842624105369811

theorem tailTrace_3637856 : CollatzResearch.WordTrace tailWord_3637856 prefixEnd_3637856 1867968679842624105369811 := by
  unfold tailWord_3637856
  simp only [CollatzResearch.WordTrace]
  refine ⟨66341754354338241592990711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88455672472450988790654281 66341754354338241592990711)
  ·
    refine ⟨99512631531507362389486067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66341754354338241592990711 99512631531507362389486067)
    ·
      refine ⟨149268947297261043584229101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99512631531507362389486067 149268947297261043584229101)
      ·
        refine ⟨55975855236472891344085913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149268947297261043584229101 55975855236472891344085913)
        ·
          refine ⟨41981891427354668508064435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55975855236472891344085913 41981891427354668508064435)
          ·
            refine ⟨62972837141032002762096653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41981891427354668508064435 62972837141032002762096653)
            ·
              refine ⟨23614813927887001035786245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62972837141032002762096653 23614813927887001035786245)
              ·
                refine ⟨4427777611478812694209921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23614813927887001035786245 4427777611478812694209921)
                ·
                  refine ⟨3320833208609109520657441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4427777611478812694209921 3320833208609109520657441)
                  ·
                    refine ⟨2490624906456832140493081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3320833208609109520657441 2490624906456832140493081)
                    ·
                      refine ⟨1867968679842624105369811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2490624906456832140493081 1867968679842624105369811)
                      ·
                        rfl

theorem cell23_3637856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_3637856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637856 prefixEnd_3637856 := by exact prefixLift 3637856
  have htrace : WordTrace (prefixWord ++ tailWord_3637856) baseStart_3637856 baseEnd_3637856 := by
    simpa [prefixWord, tailWord_3637856, baseEnd_3637856] using wordTrace_append hprefix tailTrace_3637856
  have hstable : (prefixWord ++ tailWord_3637856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637856).length < 2 ^ (prefixWord ++ tailWord_3637856).sum := by decide
  have hdescent : baseEnd_3637856 < baseStart_3637856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637865 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 8]
def baseStart_3637865 : Nat := 118140960795 + 3637865 * 2 ^ 59
def prefixEnd_3637865 : Nat := 4983230072969 + 3 ^ 40 * 3637865 * 2
def baseEnd_3637865 : Nat := 1867973301168514570157269

theorem tailTrace_3637865 : CollatzResearch.WordTrace tailWord_3637865 prefixEnd_3637865 1867973301168514570157269 := by
  unfold tailWord_3637865
  simp only [CollatzResearch.WordTrace]
  refine ⟨132683836965643877723059049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88455891310429251815372699 132683836965643877723059049)
  ·
    refine ⟨99512877724232908292294287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132683836965643877723059049 99512877724232908292294287)
    ·
      refine ⟨149269316586349362438441431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99512877724232908292294287 149269316586349362438441431)
      ·
        refine ⟨223903974879524043657662147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149269316586349362438441431 223903974879524043657662147)
        ·
          refine ⟨335855962319286065486493221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223903974879524043657662147 335855962319286065486493221)
          ·
            refine ⟨62972992934866137278717479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 335855962319286065486493221 62972992934866137278717479)
            ·
              refine ⟨94459489402299205918076219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62972992934866137278717479 94459489402299205918076219)
              ·
                refine ⟨141689234103448808877114329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94459489402299205918076219 141689234103448808877114329)
                ·
                  refine ⟨106266925577586606657835747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141689234103448808877114329 106266925577586606657835747)
                  ·
                    refine ⟨159400388366379909986753621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106266925577586606657835747 159400388366379909986753621)
                    ·
                      refine ⟨1867973301168514570157269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 159400388366379909986753621 1867973301168514570157269)
                      ·
                        rfl

theorem cell23_3637865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_3637865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637865 prefixEnd_3637865 := by exact prefixLift 3637865
  have htrace : WordTrace (prefixWord ++ tailWord_3637865) baseStart_3637865 baseEnd_3637865 := by
    simpa [prefixWord, tailWord_3637865, baseEnd_3637865] using wordTrace_append hprefix tailTrace_3637865
  have hstable : (prefixWord ++ tailWord_3637865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637865).length < 2 ^ (prefixWord ++ tailWord_3637865).sum := by decide
  have hdescent : baseEnd_3637865 < baseStart_3637865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637869 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_3637869 : Nat := 118140960795 + 3637869 * 2 ^ 59
def prefixEnd_3637869 : Nat := 4983230072969 + 3 ^ 40 * 3637869 * 2
def baseEnd_3637869 : Nat := 1867975355091132554507251

theorem tailTrace_3637869 : CollatzResearch.WordTrace tailWord_3637869 prefixEnd_3637869 1867975355091132554507251 := by
  unfold tailWord_3637869
  simp only [CollatzResearch.WordTrace]
  refine ⟨132683982857629386406204661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88455988571752924270803107 132683982857629386406204661)
  ·
    refine ⟨12439123392902754975581687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132683982857629386406204661 12439123392902754975581687)
    ·
      refine ⟨18658685089354132463372531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12439123392902754975581687 18658685089354132463372531)
      ·
        refine ⟨27988027634031198695058797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18658685089354132463372531 27988027634031198695058797)
        ·
          refine ⟨10495510362761699510647049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27988027634031198695058797 10495510362761699510647049)
          ·
            refine ⟨7871632772071274632985287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10495510362761699510647049 7871632772071274632985287)
            ·
              refine ⟨11807449158106911949477931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7871632772071274632985287 11807449158106911949477931)
              ·
                refine ⟨17711173737160367924216897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11807449158106911949477931 17711173737160367924216897)
                ·
                  refine ⟨13283380302870275943162673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17711173737160367924216897 13283380302870275943162673)
                  ·
                    refine ⟨9962535227152706957372005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13283380302870275943162673 9962535227152706957372005)
                    ·
                      refine ⟨1867975355091132554507251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9962535227152706957372005 1867975355091132554507251)
                      ·
                        rfl

theorem cell23_3637869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_3637869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637869 prefixEnd_3637869 := by exact prefixLift 3637869
  have htrace : WordTrace (prefixWord ++ tailWord_3637869) baseStart_3637869 baseEnd_3637869 := by
    simpa [prefixWord, tailWord_3637869, baseEnd_3637869] using wordTrace_append hprefix tailTrace_3637869
  have hstable : (prefixWord ++ tailWord_3637869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637869).length < 2 ^ (prefixWord ++ tailWord_3637869).sum := by decide
  have hdescent : baseEnd_3637869 < baseStart_3637869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637939 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 3, 4]
def baseStart_3637939 : Nat := 118140960795 + 3637939 * 2 ^ 59
def prefixEnd_3637939 : Nat := 4983230072969 + 3 ^ 40 * 3637939 * 2
def baseEnd_3637939 : Nat := 622670432912315760210643

theorem tailTrace_3637939 : CollatzResearch.WordTrace tailWord_3637939 prefixEnd_3637939 622670432912315760210643 := by
  unfold tailWord_3637939
  simp only [CollatzResearch.WordTrace]
  refine ⟨132686535967375788361252871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88457690644917192240835247 132686535967375788361252871)
  ·
    refine ⟨199029803951063682541879307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132686535967375788361252871 199029803951063682541879307)
    ·
      refine ⟨298544705926595523812818961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199029803951063682541879307 298544705926595523812818961)
      ·
        refine ⟨223908529444946642859614221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298544705926595523812818961 223908529444946642859614221)
        ·
          refine ⟨83965698541854991072355333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223908529444946642859614221 83965698541854991072355333)
          ·
            refine ⟨15743568476597810826066625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83965698541854991072355333 15743568476597810826066625)
            ·
              refine ⟨11807676357448358119549969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15743568476597810826066625 11807676357448358119549969)
              ·
                refine ⟨8855757268086268589662477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11807676357448358119549969 8855757268086268589662477)
                ·
                  refine ⟨3320908975532350721123429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8855757268086268589662477 3320908975532350721123429)
                  ·
                    refine ⟨622670432912315760210643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3320908975532350721123429 622670432912315760210643)
                    ·
                      rfl

theorem cell23_3637939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 4].length) (baseStart_3637939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637939 prefixEnd_3637939 := by exact prefixLift 3637939
  have htrace : WordTrace (prefixWord ++ tailWord_3637939) baseStart_3637939 baseEnd_3637939 := by
    simpa [prefixWord, tailWord_3637939, baseEnd_3637939] using wordTrace_append hprefix tailTrace_3637939
  have hstable : (prefixWord ++ tailWord_3637939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637939).length < 2 ^ (prefixWord ++ tailWord_3637939).sum := by decide
  have hdescent : baseEnd_3637939 < baseStart_3637939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637949 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_3637949 : Nat := 118140960795 + 3637949 * 2 ^ 59
def prefixEnd_3637949 : Nat := 4983230072969 + 3 ^ 40 * 3637949 * 2
def baseEnd_3637949 : Nat := 1868016433543492241506883

theorem tailTrace_3637949 : CollatzResearch.WordTrace tailWord_3637949 prefixEnd_3637949 1868016433543492241506883 := by
  unfold tailWord_3637949
  simp only [CollatzResearch.WordTrace]
  refine ⟨132686900697339560069116901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88457933798226373379411267 132686900697339560069116901)
  ·
    refine ⟨24878793880751167512959419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132686900697339560069116901 24878793880751167512959419)
    ·
      refine ⟨37318190821126751269439129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24878793880751167512959419 37318190821126751269439129)
      ·
        refine ⟨27988643115845063452079347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37318190821126751269439129 27988643115845063452079347)
        ·
          refine ⟨41982964673767595178119021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27988643115845063452079347 41982964673767595178119021)
          ·
            refine ⟨15743611752662848191794633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41982964673767595178119021 15743611752662848191794633)
            ·
              refine ⟨11807708814497136143845975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15743611752662848191794633 11807708814497136143845975)
              ·
                refine ⟨17711563221745704215768963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11807708814497136143845975 17711563221745704215768963)
                ·
                  refine ⟨26567344832618556323653445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17711563221745704215768963 26567344832618556323653445)
                  ·
                    refine ⟨4981377156115979310685021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26567344832618556323653445 4981377156115979310685021)
                    ·
                      refine ⟨1868016433543492241506883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4981377156115979310685021 1868016433543492241506883)
                      ·
                        rfl

theorem cell23_3637949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_3637949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637949 prefixEnd_3637949 := by exact prefixLift 3637949
  have htrace : WordTrace (prefixWord ++ tailWord_3637949) baseStart_3637949 baseEnd_3637949 := by
    simpa [prefixWord, tailWord_3637949, baseEnd_3637949] using wordTrace_append hprefix tailTrace_3637949
  have hstable : (prefixWord ++ tailWord_3637949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637949).length < 2 ^ (prefixWord ++ tailWord_3637949).sum := by decide
  have hdescent : baseEnd_3637949 < baseStart_3637949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637952 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 8]
def baseStart_3637952 : Nat := 118140960795 + 3637952 * 2 ^ 59
def prefixEnd_3637952 : Nat := 4983230072969 + 3 ^ 40 * 3637952 * 2
def baseEnd_3637952 : Nat := 207557552665050636641041

theorem tailTrace_3637952 : CollatzResearch.WordTrace tailWord_3637952 prefixEnd_3637952 207557552665050636641041 := by
  unfold tailWord_3637952
  simp only [CollatzResearch.WordTrace]
  refine ⟨66343505058164345790738055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88458006744219127720984073 66343505058164345790738055)
  ·
    refine ⟨99515257587246518686107083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66343505058164345790738055 99515257587246518686107083)
    ·
      refine ⟨149272886380869778029160625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99515257587246518686107083 149272886380869778029160625)
      ·
        refine ⟨111954664785652333521870469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149272886380869778029160625 111954664785652333521870469)
        ·
          refine ⟨20991499647309812535350713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111954664785652333521870469 20991499647309812535350713)
          ·
            refine ⟨15743624735482359401513035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20991499647309812535350713 15743624735482359401513035)
            ·
              refine ⟨23615437103223539102269553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15743624735482359401513035 23615437103223539102269553)
              ·
                refine ⟨17711577827417654326702165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23615437103223539102269553 17711577827417654326702165)
                ·
                  refine ⟨207557552665050636641041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17711577827417654326702165 207557552665050636641041)
                  ·
                    rfl

theorem cell23_3637952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 8].length) (baseStart_3637952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637952 prefixEnd_3637952 := by exact prefixLift 3637952
  have htrace : WordTrace (prefixWord ++ tailWord_3637952) baseStart_3637952 baseEnd_3637952 := by
    simpa [prefixWord, tailWord_3637952, baseEnd_3637952] using wordTrace_append hprefix tailTrace_3637952
  have hstable : (prefixWord ++ tailWord_3637952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637952).length < 2 ^ (prefixWord ++ tailWord_3637952).sum := by decide
  have hdescent : baseEnd_3637952 < baseStart_3637952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637966 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_3637966 : Nat := 118140960795 + 3637966 * 2 ^ 59
def prefixEnd_3637966 : Nat := 4983230072969 + 3 ^ 40 * 3637966 * 2
def baseEnd_3637966 : Nat := 1868025162714618674994305

theorem tailTrace_3637966 : CollatzResearch.WordTrace tailWord_3637966 prefixEnd_3637966 1868025162714618674994305 := by
  unfold tailWord_3637966
  simp only [CollatzResearch.WordTrace]
  refine ⟨16585940092284746496560719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88458347158851981314990501 16585940092284746496560719)
  ·
    refine ⟨24878910138427119744841079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16585940092284746496560719 24878910138427119744841079)
    ·
      refine ⟨37318365207640679617261619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24878910138427119744841079 37318365207640679617261619)
      ·
        refine ⟨55977547811461019425892429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37318365207640679617261619 55977547811461019425892429)
        ·
          refine ⟨20991580429297882284709661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55977547811461019425892429 20991580429297882284709661)
          ·
            refine ⟨7871842660986705856766123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20991580429297882284709661 7871842660986705856766123)
            ·
              refine ⟨11807763991480058785149185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7871842660986705856766123 11807763991480058785149185)
              ·
                refine ⟨8855822993610044088861889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11807763991480058785149185 8855822993610044088861889)
                ·
                  refine ⟨6641867245207533066646417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8855822993610044088861889 6641867245207533066646417)
                  ·
                    refine ⟨4981400433905649799984813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6641867245207533066646417 4981400433905649799984813)
                    ·
                      refine ⟨1868025162714618674994305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4981400433905649799984813 1868025162714618674994305)
                      ·
                        rfl

theorem cell23_3637966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_3637966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637966 prefixEnd_3637966 := by exact prefixLift 3637966
  have htrace : WordTrace (prefixWord ++ tailWord_3637966) baseStart_3637966 baseEnd_3637966 := by
    simpa [prefixWord, tailWord_3637966, baseEnd_3637966] using wordTrace_append hprefix tailTrace_3637966
  have hstable : (prefixWord ++ tailWord_3637966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637966).length < 2 ^ (prefixWord ++ tailWord_3637966).sum := by decide
  have hdescent : baseEnd_3637966 < baseStart_3637966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637979 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 9, 1, 3]
def baseStart_3637979 : Nat := 118140960795 + 3637979 * 2 ^ 59
def prefixEnd_3637979 : Nat := 4983230072969 + 3 ^ 40 * 3637979 * 2
def baseEnd_3637979 : Nat := 1868031837963127124131745

theorem tailTrace_3637979 : CollatzResearch.WordTrace tailWord_3637979 prefixEnd_3637979 1868031837963127124131745 := by
  unfold tailWord_3637979
  simp only [CollatzResearch.WordTrace]
  refine ⟨132687994887230875192708991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88458663258153916795139327 132687994887230875192708991)
  ·
    refine ⟨199031992330846312789063487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132687994887230875192708991 199031992330846312789063487)
    ·
      refine ⟨298547988496269469183595231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199031992330846312789063487 298547988496269469183595231)
      ·
        refine ⟨447821982744404203775392847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298547988496269469183595231 447821982744404203775392847)
        ·
          refine ⟨671732974116606305663089271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447821982744404203775392847 671732974116606305663089271)
          ·
            refine ⟨1007599461174909458494633907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671732974116606305663089271 1007599461174909458494633907)
            ·
              refine ⟨1511399191762364187741950861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007599461174909458494633907 1511399191762364187741950861)
              ·
                refine ⟨566774696910886570403231573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1511399191762364187741950861 566774696910886570403231573)
                ·
                  refine ⟨3320945489712225998456435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 566774696910886570403231573 3320945489712225998456435)
                  ·
                    refine ⟨4981418234568338997684653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3320945489712225998456435 4981418234568338997684653)
                    ·
                      refine ⟨1868031837963127124131745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4981418234568338997684653 1868031837963127124131745)
                      ·
                        rfl

theorem cell23_3637979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 1, 3].length) (baseStart_3637979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637979 prefixEnd_3637979 := by exact prefixLift 3637979
  have htrace : WordTrace (prefixWord ++ tailWord_3637979) baseStart_3637979 baseEnd_3637979 := by
    simpa [prefixWord, tailWord_3637979, baseEnd_3637979] using wordTrace_append hprefix tailTrace_3637979
  have hstable : (prefixWord ++ tailWord_3637979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637979).length < 2 ^ (prefixWord ++ tailWord_3637979).sum := by decide
  have hdescent : baseEnd_3637979 < baseStart_3637979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3637999 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 3, 5]
def baseStart_3637999 : Nat := 118140960795 + 3637999 * 2 ^ 59
def prefixEnd_3637999 : Nat := 4983230072969 + 3 ^ 40 * 3637999 * 2
def baseEnd_3637999 : Nat := 622680702525405681960551

theorem tailTrace_3637999 : CollatzResearch.WordTrace tailWord_3637999 prefixEnd_3637999 622680702525405681960551 := by
  unfold tailWord_3637999
  simp only [CollatzResearch.WordTrace]
  refine ⟨132688724347158418608437051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88459149564772279072291367 132688724347158418608437051)
  ·
    refine ⟨199033086520737627912655577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132688724347158418608437051 199033086520737627912655577)
    ·
      refine ⟨149274814890553220934491683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199033086520737627912655577 149274814890553220934491683)
      ·
        refine ⟨223912222335829831401737525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149274814890553220934491683 223912222335829831401737525)
        ·
          refine ⟨20991770843984046693912893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223912222335829831401737525 20991770843984046693912893)
          ·
            refine ⟨7871914066494017510217335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20991770843984046693912893 7871914066494017510217335)
            ·
              refine ⟨11807871099741026265326003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7871914066494017510217335 11807871099741026265326003)
              ·
                refine ⟨17711806649611539397989005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11807871099741026265326003 17711806649611539397989005)
                ·
                  refine ⟨6641927493604327274245877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17711806649611539397989005 6641927493604327274245877)
                  ·
                    refine ⟨622680702525405681960551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6641927493604327274245877 622680702525405681960551)
                    ·
                      rfl

theorem cell23_3637999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 5].length) (baseStart_3637999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3637999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3637999 prefixEnd_3637999 := by exact prefixLift 3637999
  have htrace : WordTrace (prefixWord ++ tailWord_3637999) baseStart_3637999 baseEnd_3637999 := by
    simpa [prefixWord, tailWord_3637999, baseEnd_3637999] using wordTrace_append hprefix tailTrace_3637999
  have hstable : (prefixWord ++ tailWord_3637999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3637999).length < 2 ^ (prefixWord ++ tailWord_3637999).sum := by decide
  have hdescent : baseEnd_3637999 < baseStart_3637999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3637999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638013 : List Nat := [1, 4, 1, 1, 1, 1, 4, 5, 1, 1, 3]
def baseStart_3638013 : Nat := 118140960795 + 3638013 * 2 ^ 59
def prefixEnd_3638013 : Nat := 4983230072969 + 3 ^ 40 * 3638013 * 2
def baseEnd_3638013 : Nat := 1868049296305379991106589

theorem tailTrace_3638013 : CollatzResearch.WordTrace tailWord_3638013 prefixEnd_3638013 1868049296305379991106589 := by
  unfold tailWord_3638013
  simp only [CollatzResearch.WordTrace]
  refine ⟨132689234969107698999446693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88459489979405132666297795 132689234969107698999446693)
  ·
    refine ⟨24879231556707693562396255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132689234969107698999446693 24879231556707693562396255)
    ·
      refine ⟨37318847335061540343594383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24879231556707693562396255 37318847335061540343594383)
      ·
        refine ⟨55978271002592310515391575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37318847335061540343594383 55978271002592310515391575)
        ·
          refine ⟨83967406503888465773087363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55978271002592310515391575 83967406503888465773087363)
          ·
            refine ⟨125951109755832698659631045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83967406503888465773087363 125951109755832698659631045)
            ·
              refine ⟨23615833079218630998680821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125951109755832698659631045 23615833079218630998680821)
              ·
                refine ⟨2213984351176746656126327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23615833079218630998680821 2213984351176746656126327)
                ·
                  refine ⟨3320976526765119984189491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2213984351176746656126327 3320976526765119984189491)
                  ·
                    refine ⟨4981464790147679976284237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3320976526765119984189491 4981464790147679976284237)
                    ·
                      refine ⟨1868049296305379991106589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4981464790147679976284237 1868049296305379991106589)
                      ·
                        rfl

theorem cell23_3638013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_3638013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638013 prefixEnd_3638013 := by exact prefixLift 3638013
  have htrace : WordTrace (prefixWord ++ tailWord_3638013) baseStart_3638013 baseEnd_3638013 := by
    simpa [prefixWord, tailWord_3638013, baseEnd_3638013] using wordTrace_append hprefix tailTrace_3638013
  have hstable : (prefixWord ++ tailWord_3638013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638013).length < 2 ^ (prefixWord ++ tailWord_3638013).sum := by decide
  have hdescent : baseEnd_3638013 < baseStart_3638013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638023 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 2, 3, 2]
def baseStart_3638023 : Nat := 118140960795 + 3638023 * 2 ^ 59
def prefixEnd_3638023 : Nat := 4983230072969 + 3 ^ 40 * 3638023 * 2
def baseEnd_3638023 : Nat := 1868054431111924951981543

theorem tailTrace_3638023 : CollatzResearch.WordTrace tailWord_3638023 prefixEnd_3638023 1868054431111924951981543 := by
  unfold tailWord_3638023
  simp only [CollatzResearch.WordTrace]
  refine ⟨132689599699071470707310723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88459733132714313804873815 132689599699071470707310723)
  ·
    refine ⟨199034399548607206060966085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132689599699071470707310723 199034399548607206060966085)
    ·
      refine ⟨37318949915363851136431141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199034399548607206060966085 37318949915363851136431141)
      ·
        refine ⟨6997303109130722088080839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37318949915363851136431141 6997303109130722088080839)
        ·
          refine ⟨10495954663696083132121259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6997303109130722088080839 10495954663696083132121259)
          ·
            refine ⟨15743931995544124698181889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10495954663696083132121259 15743931995544124698181889)
            ·
              refine ⟨11807948996658093523636417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15743931995544124698181889 11807948996658093523636417)
              ·
                refine ⟨8855961747493570142727313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11807948996658093523636417 8855961747493570142727313)
                ·
                  refine ⟨6641971310620177607045485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8855961747493570142727313 6641971310620177607045485)
                  ·
                    refine ⟨2490739241482566602642057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6641971310620177607045485 2490739241482566602642057)
                    ·
                      refine ⟨1868054431111924951981543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2490739241482566602642057 1868054431111924951981543)
                      ·
                        rfl

theorem cell23_3638023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_3638023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638023 prefixEnd_3638023 := by exact prefixLift 3638023
  have htrace : WordTrace (prefixWord ++ tailWord_3638023) baseStart_3638023 baseEnd_3638023 := by
    simpa [prefixWord, tailWord_3638023, baseEnd_3638023] using wordTrace_append hprefix tailTrace_3638023
  have hstable : (prefixWord ++ tailWord_3638023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638023).length < 2 ^ (prefixWord ++ tailWord_3638023).sum := by decide
  have hdescent : baseEnd_3638023 < baseStart_3638023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638053 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 3, 2, 2]
def baseStart_3638053 : Nat := 118140960795 + 3638053 * 2 ^ 59
def prefixEnd_3638053 : Nat := 4983230072969 + 3 ^ 40 * 3638053 * 2
def baseEnd_3638053 : Nat := 1868069835531559834606405

theorem tailTrace_3638053 : CollatzResearch.WordTrace tailWord_3638053 prefixEnd_3638053 1868069835531559834606405 := by
  unfold tailWord_3638053
  simp only [CollatzResearch.WordTrace]
  refine ⟨132690693888962785830902813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88460462592641857220601875 132690693888962785830902813)
  ·
    refine ⟨49759010208361044686588555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132690693888962785830902813 49759010208361044686588555)
    ·
      refine ⟨74638515312541567029882833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49759010208361044686588555 74638515312541567029882833)
      ·
        refine ⟨55978886484406175272412125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74638515312541567029882833 55978886484406175272412125)
        ·
          refine ⟨20992082431652315727154547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55978886484406175272412125 20992082431652315727154547)
          ·
            refine ⟨31488123647478473590731821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20992082431652315727154547 31488123647478473590731821)
            ·
              refine ⟨11808046367804427596524433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31488123647478473590731821 11808046367804427596524433)
              ·
                refine ⟨8856034775853320697393325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11808046367804427596524433 8856034775853320697393325)
                ·
                  refine ⟨3321013040944995261522497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8856034775853320697393325 3321013040944995261522497)
                  ·
                    refine ⟨2490759780708746446141873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3321013040944995261522497 2490759780708746446141873)
                    ·
                      refine ⟨1868069835531559834606405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2490759780708746446141873 1868069835531559834606405)
                      ·
                        rfl

theorem cell23_3638053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_3638053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638053 prefixEnd_3638053 := by exact prefixLift 3638053
  have htrace : WordTrace (prefixWord ++ tailWord_3638053) baseStart_3638053 baseEnd_3638053 := by
    simpa [prefixWord, tailWord_3638053, baseEnd_3638053] using wordTrace_append hprefix tailTrace_3638053
  have hstable : (prefixWord ++ tailWord_3638053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638053).length < 2 ^ (prefixWord ++ tailWord_3638053).sum := by decide
  have hdescent : baseEnd_3638053 < baseStart_3638053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638056 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_3638056 : Nat := 118140960795 + 3638056 * 2 ^ 59
def prefixEnd_3638056 : Nat := 4983230072969 + 3 ^ 40 * 3638056 * 2
def baseEnd_3638056 : Nat := 1868071375973523322868891

theorem tailTrace_3638056 : CollatzResearch.WordTrace tailWord_3638056 prefixEnd_3638056 1868071375973523322868891 := by
  unfold tailWord_3638056
  simp only [CollatzResearch.WordTrace]
  refine ⟨66345401653975958671631011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88460535538634611562174681 66345401653975958671631011)
  ·
    refine ⟨99518102480963938007446517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66345401653975958671631011 99518102480963938007446517)
    ·
      refine ⟨9329822107590369188198111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99518102480963938007446517 9329822107590369188198111)
      ·
        refine ⟨13994733161385553782297167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9329822107590369188198111 13994733161385553782297167)
        ·
          refine ⟨20992099742078330673445751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13994733161385553782297167 20992099742078330673445751)
          ·
            refine ⟨31488149613117496010168627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20992099742078330673445751 31488149613117496010168627)
            ·
              refine ⟨47232224419676244015252941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31488149613117496010168627 47232224419676244015252941)
              ·
                refine ⟨17712084157378591505719853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47232224419676244015252941 17712084157378591505719853)
                ·
                  refine ⟨6642031559016971814644945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17712084157378591505719853 6642031559016971814644945)
                  ·
                    refine ⟨4981523669262728860983709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6642031559016971814644945 4981523669262728860983709)
                    ·
                      refine ⟨1868071375973523322868891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4981523669262728860983709 1868071375973523322868891)
                      ·
                        rfl

theorem cell23_3638056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_3638056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638056 prefixEnd_3638056 := by exact prefixLift 3638056
  have htrace : WordTrace (prefixWord ++ tailWord_3638056) baseStart_3638056 baseEnd_3638056 := by
    simpa [prefixWord, tailWord_3638056, baseEnd_3638056] using wordTrace_append hprefix tailTrace_3638056
  have hstable : (prefixWord ++ tailWord_3638056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638056).length < 2 ^ (prefixWord ++ tailWord_3638056).sum := by decide
  have hdescent : baseEnd_3638056 < baseStart_3638056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638070 : List Nat := [5, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3638070 : Nat := 118140960795 + 3638070 * 2 ^ 59
def prefixEnd_3638070 : Nat := 4983230072969 + 3 ^ 40 * 3638070 * 2
def baseEnd_3638070 : Nat := 1868078564702686268093827

theorem tailTrace_3638070 : CollatzResearch.WordTrace tailWord_3638070 prefixEnd_3638070 1868078564702686268093827 := by
  unfold tailWord_3638070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8293207120618824858391979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88460875953267465156181109 8293207120618824858391979)
  ·
    refine ⟨12439810680928237287587969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8293207120618824858391979 12439810680928237287587969)
    ·
      refine ⟨9329858010696177965690977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12439810680928237287587969 9329858010696177965690977)
      ·
        refine ⟨6997393508022133474268233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9329858010696177965690977 6997393508022133474268233)
        ·
          refine ⟨5248045131016600105701175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6997393508022133474268233 5248045131016600105701175)
          ·
            refine ⟨7872067696524900158551763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5248045131016600105701175 7872067696524900158551763)
            ·
              refine ⟨11808101544787350237827645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7872067696524900158551763 11808101544787350237827645)
              ·
                refine ⟨4428038079295256339185367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11808101544787350237827645 4428038079295256339185367)
                ·
                  refine ⟨6642057118942884508778051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4428038079295256339185367 6642057118942884508778051)
                  ·
                    refine ⟨9963085678414326763167077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6642057118942884508778051 9963085678414326763167077)
                    ·
                      refine ⟨1868078564702686268093827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9963085678414326763167077 1868078564702686268093827)
                      ·
                        rfl

theorem cell23_3638070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3638070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638070 prefixEnd_3638070 := by exact prefixLift 3638070
  have htrace : WordTrace (prefixWord ++ tailWord_3638070) baseStart_3638070 baseEnd_3638070 := by
    simpa [prefixWord, tailWord_3638070, baseEnd_3638070] using wordTrace_append hprefix tailTrace_3638070
  have hstable : (prefixWord ++ tailWord_3638070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638070).length < 2 ^ (prefixWord ++ tailWord_3638070).sum := by decide
  have hdescent : baseEnd_3638070 < baseStart_3638070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638096 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 5, 3, 2]
def baseStart_3638096 : Nat := 118140960795 + 3638096 * 2 ^ 59
def prefixEnd_3638096 : Nat := 4983230072969 + 3 ^ 40 * 3638096 * 2
def baseEnd_3638096 : Nat := 1868091915199703166368707

theorem tailTrace_3638096 : CollatzResearch.WordTrace tailWord_3638096 prefixEnd_3638096 1868091915199703166368707 := by
  unfold tailWord_3638096
  simp only [CollatzResearch.WordTrace]
  refine ⟨66346131113903502087359071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88461508151871336116478761 66346131113903502087359071)
  ·
    refine ⟨99519196670855253131038607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66346131113903502087359071 99519196670855253131038607)
    ·
      refine ⟨149278795006282879696557911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99519196670855253131038607 149278795006282879696557911)
      ·
        refine ⟨223918192509424319544836867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149278795006282879696557911 223918192509424319544836867)
        ·
          refine ⟨335877288764136479317255301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223918192509424319544836867 335877288764136479317255301)
          ·
            refine ⟨62976991643275589871985369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 335877288764136479317255301 62976991643275589871985369)
            ·
              refine ⟨47232743732456692403989027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62976991643275589871985369 47232743732456692403989027)
              ·
                refine ⟨70849115598685038605983541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47232743732456692403989027 70849115598685038605983541)
                ·
                  refine ⟨6642104587376722369310957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70849115598685038605983541 6642104587376722369310957)
                  ·
                    refine ⟨2490789220266270888491609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6642104587376722369310957 2490789220266270888491609)
                    ·
                      refine ⟨1868091915199703166368707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2490789220266270888491609 1868091915199703166368707)
                      ·
                        rfl

theorem cell23_3638096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 5, 3, 2].length) (baseStart_3638096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638096 prefixEnd_3638096 := by exact prefixLift 3638096
  have htrace : WordTrace (prefixWord ++ tailWord_3638096) baseStart_3638096 baseEnd_3638096 := by
    simpa [prefixWord, tailWord_3638096, baseEnd_3638096] using wordTrace_append hprefix tailTrace_3638096
  have hstable : (prefixWord ++ tailWord_3638096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638096).length < 2 ^ (prefixWord ++ tailWord_3638096).sum := by decide
  have hdescent : baseEnd_3638096 < baseStart_3638096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638100 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_3638100 : Nat := 118140960795 + 3638100 * 2 ^ 59
def prefixEnd_3638100 : Nat := 4983230072969 + 3 ^ 40 * 3638100 * 2
def baseEnd_3638100 : Nat := 1868093969122321150718689

theorem tailTrace_3638100 : CollatzResearch.WordTrace tailWord_3638100 prefixEnd_3638100 1868093969122321150718689 := by
  unfold tailWord_3638100
  simp only [CollatzResearch.WordTrace]
  refine ⟨66346204059896256428931877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88461605413195008571909169 66346204059896256428931877)
  ·
    refine ⟨12439913261230548080424727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66346204059896256428931877 12439913261230548080424727)
    ·
      refine ⟨18659869891845822120637091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12439913261230548080424727 18659869891845822120637091)
      ·
        refine ⟨27989804837768733180955637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18659869891845822120637091 27989804837768733180955637)
        ·
          refine ⟨2624044203540818735714591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27989804837768733180955637 2624044203540818735714591)
          ·
            refine ⟨3936066305311228103571887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2624044203540818735714591 3936066305311228103571887)
            ·
              refine ⟨5904099457966842155357831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936066305311228103571887 5904099457966842155357831)
              ·
                refine ⟨8856149186950263233036747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904099457966842155357831 8856149186950263233036747)
                ·
                  refine ⟨13284223780425394849555121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8856149186950263233036747 13284223780425394849555121)
                  ·
                    refine ⟨9963167835319046137166341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13284223780425394849555121 9963167835319046137166341)
                    ·
                      refine ⟨1868093969122321150718689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9963167835319046137166341 1868093969122321150718689)
                      ·
                        rfl

theorem cell23_3638100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_3638100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638100 prefixEnd_3638100 := by exact prefixLift 3638100
  have htrace : WordTrace (prefixWord ++ tailWord_3638100) baseStart_3638100 baseEnd_3638100 := by
    simpa [prefixWord, tailWord_3638100, baseEnd_3638100] using wordTrace_append hprefix tailTrace_3638100
  have hstable : (prefixWord ++ tailWord_3638100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638100).length < 2 ^ (prefixWord ++ tailWord_3638100).sum := by decide
  have hdescent : baseEnd_3638100 < baseStart_3638100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638103 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 1, 3, 3]
def baseStart_3638103 : Nat := 118140960795 + 3638103 * 2 ^ 59
def prefixEnd_3638103 : Nat := 4983230072969 + 3 ^ 40 * 3638103 * 2
def baseEnd_3638103 : Nat := 1868095509564284638981175

theorem tailTrace_3638103 : CollatzResearch.WordTrace tailWord_3638103 prefixEnd_3638103 1868095509564284638981175 := by
  unfold tailWord_3638103
  simp only [CollatzResearch.WordTrace]
  refine ⟨132692517538781644370222963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88461678359187762913481975 132692517538781644370222963)
  ·
    refine ⟨199038776308172466555334445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132692517538781644370222963 199038776308172466555334445)
    ·
      refine ⟨74639541115564674958250417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199038776308172466555334445 74639541115564674958250417)
      ·
        refine ⟨55979655836673506218687813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74639541115564674958250417 55979655836673506218687813)
        ·
          refine ⟨10496185469376282416003965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55979655836673506218687813 10496185469376282416003965)
          ·
            refine ⟨3936069551016105906001487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10496185469376282416003965 3936069551016105906001487)
            ·
              refine ⟨5904104326524158859002231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936069551016105906001487 5904104326524158859002231)
              ·
                refine ⟨8856156489786238288503347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904104326524158859002231 8856156489786238288503347)
                ·
                  refine ⟨13284234734679357432755021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8856156489786238288503347 13284234734679357432755021)
                  ·
                    refine ⟨4981588025504759037283133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13284234734679357432755021 4981588025504759037283133)
                    ·
                      refine ⟨1868095509564284638981175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4981588025504759037283133 1868095509564284638981175)
                      ·
                        rfl

theorem cell23_3638103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_3638103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638103 prefixEnd_3638103 := by exact prefixLift 3638103
  have htrace : WordTrace (prefixWord ++ tailWord_3638103) baseStart_3638103 baseEnd_3638103 := by
    simpa [prefixWord, tailWord_3638103, baseEnd_3638103] using wordTrace_append hprefix tailTrace_3638103
  have hstable : (prefixWord ++ tailWord_3638103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638103).length < 2 ^ (prefixWord ++ tailWord_3638103).sum := by decide
  have hdescent : baseEnd_3638103 < baseStart_3638103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638129 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_3638129 : Nat := 118140960795 + 3638129 * 2 ^ 59
def prefixEnd_3638129 : Nat := 4983230072969 + 3 ^ 40 * 3638129 * 2
def baseEnd_3638129 : Nat := 1868108860061301537256055

theorem tailTrace_3638129 : CollatzResearch.WordTrace tailWord_3638129 prefixEnd_3638129 1868108860061301537256055 := by
  unfold tailWord_3638129
  simp only [CollatzResearch.WordTrace]
  refine ⟨132693465836687450810669441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88462310557791633873779627 132693465836687450810669441)
  ·
    refine ⟨99520099377515588108002081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132693465836687450810669441 99520099377515588108002081)
    ·
      refine ⟨74640074533136691081001561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99520099377515588108002081 74640074533136691081001561)
      ·
        refine ⟨55980055899852518310751171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74640074533136691081001561 55980055899852518310751171)
        ·
          refine ⟨83970083849778777466126757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55980055899852518310751171 83970083849778777466126757)
          ·
            refine ⟨15744390721833520774898767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83970083849778777466126757 15744390721833520774898767)
            ·
              refine ⟨23616586082750281162348151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15744390721833520774898767 23616586082750281162348151)
              ·
                refine ⟨35424879124125421743522227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23616586082750281162348151 35424879124125421743522227)
                ·
                  refine ⟨53137318686188132615283341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35424879124125421743522227 53137318686188132615283341)
                  ·
                    refine ⟨19926494507320549730731253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53137318686188132615283341 19926494507320549730731253)
                    ·
                      refine ⟨1868108860061301537256055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19926494507320549730731253 1868108860061301537256055)
                      ·
                        rfl

theorem cell23_3638129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_3638129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638129 prefixEnd_3638129 := by exact prefixLift 3638129
  have htrace : WordTrace (prefixWord ++ tailWord_3638129) baseStart_3638129 baseEnd_3638129 := by
    simpa [prefixWord, tailWord_3638129, baseEnd_3638129] using wordTrace_append hprefix tailTrace_3638129
  have hstable : (prefixWord ++ tailWord_3638129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638129).length < 2 ^ (prefixWord ++ tailWord_3638129).sum := by decide
  have hdescent : baseEnd_3638129 < baseStart_3638129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638139 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 4]
def baseStart_3638139 : Nat := 118140960795 + 3638139 * 2 ^ 59
def prefixEnd_3638139 : Nat := 4983230072969 + 3 ^ 40 * 3638139 * 2
def baseEnd_3638139 : Nat := 1868113994867846498131009

theorem tailTrace_3638139 : CollatzResearch.WordTrace tailWord_3638139 prefixEnd_3638139 1868113994867846498131009 := by
  unfold tailWord_3638139
  simp only [CollatzResearch.WordTrace]
  refine ⟨132693830566651222518533471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88462553711100815012355647 132693830566651222518533471)
  ·
    refine ⟨199040745849976833777800207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132693830566651222518533471 199040745849976833777800207)
    ·
      refine ⟨298561118774965250666700311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199040745849976833777800207 298561118774965250666700311)
      ·
        refine ⟨447841678162447876000050467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298561118774965250666700311 447841678162447876000050467)
        ·
          refine ⟨671762517243671814000075701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447841678162447876000050467 671762517243671814000075701)
          ·
            refine ⟨62977735991594232562507097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 671762517243671814000075701 62977735991594232562507097)
            ·
              refine ⟨47233301993695674421880323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62977735991594232562507097 47233301993695674421880323)
              ·
                refine ⟨70849952990543511632820485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47233301993695674421880323 70849952990543511632820485)
                ·
                  refine ⟨13284366185726908431153841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70849952990543511632820485 13284366185726908431153841)
                  ·
                    refine ⟨9963274639295181323365381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13284366185726908431153841 9963274639295181323365381)
                    ·
                      refine ⟨1868113994867846498131009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9963274639295181323365381 1868113994867846498131009)
                      ·
                        rfl

theorem cell23_3638139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 4].length) (baseStart_3638139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638139 prefixEnd_3638139 := by exact prefixLift 3638139
  have htrace : WordTrace (prefixWord ++ tailWord_3638139) baseStart_3638139 baseEnd_3638139 := by
    simpa [prefixWord, tailWord_3638139, baseEnd_3638139] using wordTrace_append hprefix tailTrace_3638139
  have hstable : (prefixWord ++ tailWord_3638139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638139).length < 2 ^ (prefixWord ++ tailWord_3638139).sum := by decide
  have hdescent : baseEnd_3638139 < baseStart_3638139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638143 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 4, 2, 2]
def baseStart_3638143 : Nat := 118140960795 + 3638143 * 2 ^ 59
def prefixEnd_3638143 : Nat := 4983230072969 + 3 ^ 40 * 3638143 * 2
def baseEnd_3638143 : Nat := 1868116048790464482480991

theorem tailTrace_3638143 : CollatzResearch.WordTrace tailWord_3638143 prefixEnd_3638143 1868116048790464482480991 := by
  unfold tailWord_3638143
  simp only [CollatzResearch.WordTrace]
  refine ⟨132693976458636731201679083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88462650972424487467786055 132693976458636731201679083)
  ·
    refine ⟨199040964687955096802518625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132693976458636731201679083 199040964687955096802518625)
    ·
      refine ⟨149280723515966322601888969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199040964687955096802518625 149280723515966322601888969)
      ·
        refine ⟨111960542636974741951416727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149280723515966322601888969 111960542636974741951416727)
        ·
          refine ⟨167940813955462112927125091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111960542636974741951416727 167940813955462112927125091)
          ·
            refine ⟨251911220933193169390687637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167940813955462112927125091 251911220933193169390687637)
            ·
              refine ⟨11808338481243429815188483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 251911220933193169390687637 11808338481243429815188483)
              ·
                refine ⟨17712507721865144722782725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11808338481243429815188483 17712507721865144722782725)
                ·
                  refine ⟨3321095197849714635521761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17712507721865144722782725 3321095197849714635521761)
                  ·
                    refine ⟨2490821398387285976641321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3321095197849714635521761 2490821398387285976641321)
                    ·
                      refine ⟨1868116048790464482480991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2490821398387285976641321 1868116048790464482480991)
                      ·
                        rfl

theorem cell23_3638143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 2, 2].length) (baseStart_3638143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638143 prefixEnd_3638143 := by exact prefixLift 3638143
  have htrace : WordTrace (prefixWord ++ tailWord_3638143) baseStart_3638143 baseEnd_3638143 := by
    simpa [prefixWord, tailWord_3638143, baseEnd_3638143] using wordTrace_append hprefix tailTrace_3638143
  have hstable : (prefixWord ++ tailWord_3638143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638143).length < 2 ^ (prefixWord ++ tailWord_3638143).sum := by decide
  have hdescent : baseEnd_3638143 < baseStart_3638143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638179 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 1, 7]
def baseStart_3638179 : Nat := 118140960795 + 3638179 * 2 ^ 59
def prefixEnd_3638179 : Nat := 4983230072969 + 3 ^ 40 * 3638179 * 2
def baseEnd_3638179 : Nat := 622711511364675447210275

theorem tailTrace_3638179 : CollatzResearch.WordTrace tailWord_3638179 prefixEnd_3638179 622711511364675447210275 := by
  unfold tailWord_3638179
  simp only [CollatzResearch.WordTrace]
  refine ⟨132695289486506309349989591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88463526324337539566659727 132695289486506309349989591)
  ·
    refine ⟨199042934229759464024984387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132695289486506309349989591 199042934229759464024984387)
    ·
      refine ⟨298564401344639196037476581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199042934229759464024984387 298564401344639196037476581)
      ·
        refine ⟨55980825252119849257026859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298564401344639196037476581 55980825252119849257026859)
        ·
          refine ⟨83971237878179773885540289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55980825252119849257026859 83971237878179773885540289)
          ·
            refine ⟨62978428408634830414155217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83971237878179773885540289 62978428408634830414155217)
            ·
              refine ⟨47233821306476122810616413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62978428408634830414155217 47233821306476122810616413)
              ·
                refine ⟨17712682989928546053981155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47233821306476122810616413 17712682989928546053981155)
                ·
                  refine ⟨26569024484892819080971733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17712682989928546053981155 26569024484892819080971733)
                  ·
                    refine ⟨622711511364675447210275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26569024484892819080971733 622711511364675447210275)
                    ·
                      rfl

theorem cell23_3638179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 7].length) (baseStart_3638179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638179 prefixEnd_3638179 := by exact prefixLift 3638179
  have htrace : WordTrace (prefixWord ++ tailWord_3638179) baseStart_3638179 baseEnd_3638179 := by
    simpa [prefixWord, tailWord_3638179, baseEnd_3638179] using wordTrace_append hprefix tailTrace_3638179
  have hstable : (prefixWord ++ tailWord_3638179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638179).length < 2 ^ (prefixWord ++ tailWord_3638179).sum := by decide
  have hdescent : baseEnd_3638179 < baseStart_3638179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638200 : List Nat := [2, 1, 2, 1, 2, 6, 2, 2, 5]
def baseStart_3638200 : Nat := 118140960795 + 3638200 * 2 ^ 59
def prefixEnd_3638200 : Nat := 4983230072969 + 3 ^ 40 * 3638200 * 2
def baseEnd_3638200 : Nat := 207571701909752306607581

theorem tailTrace_3638200 : CollatzResearch.WordTrace tailWord_3638200 prefixEnd_3638200 207571701909752306607581 := by
  unfold tailWord_3638200
  simp only [CollatzResearch.WordTrace]
  refine ⟨66348027709715114968252027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88464036946286819957669369 66348027709715114968252027)
  ·
    refine ⟨99522041564572672452378041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66348027709715114968252027 99522041564572672452378041)
    ·
      refine ⟨74641531173429504339283531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99522041564572672452378041 74641531173429504339283531)
      ·
        refine ⟨111962296760144256508925297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74641531173429504339283531 111962296760144256508925297)
        ·
          refine ⟨83971722570108192381693973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111962296760144256508925297 83971722570108192381693973)
          ·
            refine ⟨3936174495473821517891905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83971722570108192381693973 3936174495473821517891905)
            ·
              refine ⟨2952130871605366138418929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3936174495473821517891905 2952130871605366138418929)
              ·
                refine ⟨2214098153704024603814197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2952130871605366138418929 2214098153704024603814197)
                ·
                  refine ⟨207571701909752306607581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2214098153704024603814197 207571701909752306607581)
                  ·
                    rfl

theorem cell23_3638200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 5].length) (baseStart_3638200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638200 prefixEnd_3638200 := by exact prefixLift 3638200
  have htrace : WordTrace (prefixWord ++ tailWord_3638200) baseStart_3638200 baseEnd_3638200 := by
    simpa [prefixWord, tailWord_3638200, baseEnd_3638200] using wordTrace_append hprefix tailTrace_3638200
  have hstable : (prefixWord ++ tailWord_3638200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638200).length < 2 ^ (prefixWord ++ tailWord_3638200).sum := by decide
  have hdescent : baseEnd_3638200 < baseStart_3638200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638206 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_3638206 : Nat := 118140960795 + 3638206 * 2 ^ 59
def prefixEnd_3638206 : Nat := 4983230072969 + 3 ^ 40 * 3638206 * 2
def baseEnd_3638206 : Nat := 1868148398071697735993201

theorem tailTrace_3638206 : CollatzResearch.WordTrace tailWord_3638206 prefixEnd_3638206 1868148398071697735993201 := by
  unfold tailWord_3638206
  simp only [CollatzResearch.WordTrace]
  refine ⟨16587034282176061620152809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88464182838272328640814981 16587034282176061620152809)
  ·
    refine ⟨12440275711632046215114607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16587034282176061620152809 12440275711632046215114607)
    ·
      refine ⟨18660413567448069322671911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12440275711632046215114607 18660413567448069322671911)
      ·
        refine ⟨27990620351172103984007867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18660413567448069322671911 27990620351172103984007867)
        ·
          refine ⟨41985930526758155976011801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27990620351172103984007867 41985930526758155976011801)
          ·
            refine ⟨31489447895068616982008851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41985930526758155976011801 31489447895068616982008851)
            ·
              refine ⟨47234171842602925473013277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31489447895068616982008851 47234171842602925473013277)
              ·
                refine ⟨17712814440976097052379979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47234171842602925473013277 17712814440976097052379979)
                ·
                  refine ⟨26569221661464145578569969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17712814440976097052379979 26569221661464145578569969)
                  ·
                    refine ⟨19926916246098109183927477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26569221661464145578569969 19926916246098109183927477)
                    ·
                      refine ⟨1868148398071697735993201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19926916246098109183927477 1868148398071697735993201)
                      ·
                        rfl

theorem cell23_3638206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_3638206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638206 prefixEnd_3638206 := by exact prefixLift 3638206
  have htrace : WordTrace (prefixWord ++ tailWord_3638206) baseStart_3638206 baseEnd_3638206 := by
    simpa [prefixWord, tailWord_3638206, baseEnd_3638206] using wordTrace_append hprefix tailTrace_3638206
  have hstable : (prefixWord ++ tailWord_3638206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638206).length < 2 ^ (prefixWord ++ tailWord_3638206).sum := by decide
  have hdescent : baseEnd_3638206 < baseStart_3638206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638230 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_3638230 : Nat := 118140960795 + 3638230 * 2 ^ 59
def prefixEnd_3638230 : Nat := 4983230072969 + 3 ^ 40 * 3638230 * 2
def baseEnd_3638230 : Nat := 622720240535801880697697

theorem tailTrace_3638230 : CollatzResearch.WordTrace tailWord_3638230 prefixEnd_3638230 622720240535801880697697 := by
  unfold tailWord_3638230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8293571850582596566256009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88464766406214363373397429 8293571850582596566256009)
  ·
    refine ⟨6220178887936947424692007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8293571850582596566256009 6220178887936947424692007)
    ·
      refine ⟨9330268331905421137038011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6220178887936947424692007 9330268331905421137038011)
      ·
        refine ⟨13995402497858131705557017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9330268331905421137038011 13995402497858131705557017)
        ·
          refine ⟨10496551873393598779167763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13995402497858131705557017 10496551873393598779167763)
          ·
            refine ⟨15744827810090398168751645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10496551873393598779167763 15744827810090398168751645)
            ·
              refine ⟨5904310428783899313281867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15744827810090398168751645 5904310428783899313281867)
              ·
                refine ⟨8856465643175848969922801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904310428783899313281867 8856465643175848969922801)
                ·
                  refine ⟨6642349232381886727442101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8856465643175848969922801 6642349232381886727442101)
                  ·
                    refine ⟨622720240535801880697697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6642349232381886727442101 622720240535801880697697)
                    ·
                      rfl

theorem cell23_3638230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_3638230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638230 prefixEnd_3638230 := by exact prefixLift 3638230
  have htrace : WordTrace (prefixWord ++ tailWord_3638230) baseStart_3638230 baseEnd_3638230 := by
    simpa [prefixWord, tailWord_3638230, baseEnd_3638230] using wordTrace_append hprefix tailTrace_3638230
  have hstable : (prefixWord ++ tailWord_3638230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638230).length < 2 ^ (prefixWord ++ tailWord_3638230).sum := by decide
  have hdescent : baseEnd_3638230 < baseStart_3638230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638233 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 2, 1, 4]
def baseStart_3638233 : Nat := 118140960795 + 3638233 * 2 ^ 59
def prefixEnd_3638233 : Nat := 4983230072969 + 3 ^ 40 * 3638233 * 2
def baseEnd_3638233 : Nat := 1868162262049369130355577

theorem tailTrace_3638233 : CollatzResearch.WordTrace tailWord_3638233 prefixEnd_3638233 1868162262049369130355577 := by
  unfold tailWord_3638233
  simp only [CollatzResearch.WordTrace]
  refine ⟨132697259028310676572455353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88464839352207117714970235 132697259028310676572455353)
  ·
    refine ⟨99522944271233007429341515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132697259028310676572455353 99522944271233007429341515)
    ·
      refine ⟨149284416406849511144012273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99522944271233007429341515 149284416406849511144012273)
      ·
        refine ⟨111963312305137133358009205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149284416406849511144012273 111963312305137133358009205)
        ·
          refine ⟨10496560528606606252313363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111963312305137133358009205 10496560528606606252313363)
          ·
            refine ⟨15744840792909909378470045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10496560528606606252313363 15744840792909909378470045)
            ·
              refine ⟨5904315297341216016926267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15744840792909909378470045 5904315297341216016926267)
              ·
                refine ⟨8856472946011824025389401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904315297341216016926267 8856472946011824025389401)
                ·
                  refine ⟨6642354709508868019042051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8856472946011824025389401 6642354709508868019042051)
                  ·
                    refine ⟨9963532064263302028563077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6642354709508868019042051 9963532064263302028563077)
                    ·
                      refine ⟨1868162262049369130355577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9963532064263302028563077 1868162262049369130355577)
                      ·
                        rfl

theorem cell23_3638233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_3638233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638233 prefixEnd_3638233 := by exact prefixLift 3638233
  have htrace : WordTrace (prefixWord ++ tailWord_3638233) baseStart_3638233 baseEnd_3638233 := by
    simpa [prefixWord, tailWord_3638233, baseEnd_3638233] using wordTrace_append hprefix tailTrace_3638233
  have hstable : (prefixWord ++ tailWord_3638233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638233).length < 2 ^ (prefixWord ++ tailWord_3638233).sum := by decide
  have hdescent : baseEnd_3638233 < baseStart_3638233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638249 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 7]
def baseStart_3638249 : Nat := 118140960795 + 3638249 * 2 ^ 59
def prefixEnd_3638249 : Nat := 4983230072969 + 3 ^ 40 * 3638249 * 2
def baseEnd_3638249 : Nat := 1868170477739841067755503

theorem tailTrace_3638249 : CollatzResearch.WordTrace tailWord_3638249 prefixEnd_3638249 1868170477739841067755503 := by
  unfold tailWord_3638249
  simp only [CollatzResearch.WordTrace]
  refine ⟨132697842596252711305037801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88465228397501807536691867 132697842596252711305037801)
  ·
    refine ⟨99523381947189533478778351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132697842596252711305037801 99523381947189533478778351)
    ·
      refine ⟨149285072920784300218167527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99523381947189533478778351 149285072920784300218167527)
      ·
        refine ⟨223927609381176450327251291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149285072920784300218167527 223927609381176450327251291)
        ·
          refine ⟨335891414071764675490876937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223927609381176450327251291 335891414071764675490876937)
          ·
            refine ⟨251918560553823506618157703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335891414071764675490876937 251918560553823506618157703)
            ·
              refine ⟨377877840830735259927236555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251918560553823506618157703 377877840830735259927236555)
              ·
                refine ⟨566816761246102889890854833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377877840830735259927236555 566816761246102889890854833)
                ·
                  refine ⟨425112570934577167418141125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566816761246102889890854833 425112570934577167418141125)
                  ·
                    refine ⟨79708607050233218890901461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 425112570934577167418141125 79708607050233218890901461)
                    ·
                      refine ⟨1868170477739841067755503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79708607050233218890901461 1868170477739841067755503)
                      ·
                        rfl

theorem cell23_3638249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_3638249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638249 prefixEnd_3638249 := by exact prefixLift 3638249
  have htrace : WordTrace (prefixWord ++ tailWord_3638249) baseStart_3638249 baseEnd_3638249 := by
    simpa [prefixWord, tailWord_3638249, baseEnd_3638249] using wordTrace_append hprefix tailTrace_3638249
  have hstable : (prefixWord ++ tailWord_3638249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638249).length < 2 ^ (prefixWord ++ tailWord_3638249).sum := by decide
  have hdescent : baseEnd_3638249 < baseStart_3638249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638303 : List Nat := [1, 1, 2, 4, 1, 3, 2, 3, 1, 5]
def baseStart_3638303 : Nat := 118140960795 + 3638303 * 2 ^ 59
def prefixEnd_3638303 : Nat := 4983230072969 + 3 ^ 40 * 3638303 * 2
def baseEnd_3638303 : Nat := 622732735231727952160085

theorem tailTrace_3638303 : CollatzResearch.WordTrace tailWord_3638303 prefixEnd_3638303 622732735231727952160085 := by
  unfold tailWord_3638303
  simp only [CollatzResearch.WordTrace]
  refine ⟨132699812138057078527503563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88466541425371385685002375 132699812138057078527503563)
  ·
    refine ⟨199049718207085617791255345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132699812138057078527503563 199049718207085617791255345)
    ·
      refine ⟨149287288655314213343441509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199049718207085617791255345 149287288655314213343441509)
      ·
        refine ⟨27991366622871415001895283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149287288655314213343441509 27991366622871415001895283)
        ·
          refine ⟨41987049934307122502842925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27991366622871415001895283 41987049934307122502842925)
          ·
            refine ⟨15745143725365170938566097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41987049934307122502842925 15745143725365170938566097)
            ·
              refine ⟨11808857794023878203924573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15745143725365170938566097 11808857794023878203924573)
              ·
                refine ⟨4428321672758954326471715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11808857794023878203924573 4428321672758954326471715)
                ·
                  refine ⟨6642482509138431489707573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4428321672758954326471715 6642482509138431489707573)
                  ·
                    refine ⟨622732735231727952160085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6642482509138431489707573 622732735231727952160085)
                    ·
                      rfl

theorem cell23_3638303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 5].length) (baseStart_3638303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638303 prefixEnd_3638303 := by exact prefixLift 3638303
  have htrace : WordTrace (prefixWord ++ tailWord_3638303) baseStart_3638303 baseEnd_3638303 := by
    simpa [prefixWord, tailWord_3638303, baseEnd_3638303] using wordTrace_append hprefix tailTrace_3638303
  have hstable : (prefixWord ++ tailWord_3638303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638303).length < 2 ^ (prefixWord ++ tailWord_3638303).sum := by decide
  have hdescent : baseEnd_3638303 < baseStart_3638303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638336 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 6]
def baseStart_3638336 : Nat := 118140960795 + 3638336 * 2 ^ 59
def prefixEnd_3638336 : Nat := 4983230072969 + 3 ^ 40 * 3638336 * 2
def baseEnd_3638336 : Nat := 1868215150556782227367603

theorem tailTrace_3638336 : CollatzResearch.WordTrace tailWord_3638336 prefixEnd_3638336 1868215150556782227367603 := by
  unfold tailWord_3638336
  simp only [CollatzResearch.WordTrace]
  refine ⟨66350507873468762581727431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88467343831291683442303241 66350507873468762581727431)
  ·
    refine ⟨99525761810203143872591147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66350507873468762581727431 99525761810203143872591147)
    ·
      refine ⟨149288642715304715808886721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99525761810203143872591147 149288642715304715808886721)
      ·
        refine ⟨111966482036478536856665041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149288642715304715808886721 111966482036478536856665041)
        ·
          refine ⟨83974861527358902642498781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111966482036478536856665041 83974861527358902642498781)
          ·
            refine ⟨31490573072759588490937043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83974861527358902642498781 31490573072759588490937043)
            ·
              refine ⟨47235859609139382736405565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31490573072759588490937043 47235859609139382736405565)
              ·
                refine ⟨17713447353427268526152087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47235859609139382736405565 17713447353427268526152087)
                ·
                  refine ⟨26570171030140902789228131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17713447353427268526152087 26570171030140902789228131)
                  ·
                    refine ⟨39855256545211354183842197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26570171030140902789228131 39855256545211354183842197)
                    ·
                      refine ⟨1868215150556782227367603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39855256545211354183842197 1868215150556782227367603)
                      ·
                        rfl

theorem cell23_3638336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_3638336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638336 prefixEnd_3638336 := by exact prefixLift 3638336
  have htrace : WordTrace (prefixWord ++ tailWord_3638336) baseStart_3638336 baseEnd_3638336 := by
    simpa [prefixWord, tailWord_3638336, baseEnd_3638336] using wordTrace_append hprefix tailTrace_3638336
  have hstable : (prefixWord ++ tailWord_3638336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638336).length < 2 ^ (prefixWord ++ tailWord_3638336).sum := by decide
  have hdescent : baseEnd_3638336 < baseStart_3638336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638337 : List Nat := [1, 2, 5, 1, 3, 2, 1, 2, 1, 5]
def baseStart_3638337 : Nat := 118140960795 + 3638337 * 2 ^ 59
def prefixEnd_3638337 : Nat := 4983230072969 + 3 ^ 40 * 3638337 * 2
def baseEnd_3638337 : Nat := 622738554679145574485033

theorem tailTrace_3638337 : CollatzResearch.WordTrace tailWord_3638337 prefixEnd_3638337 622738554679145574485033 := by
  unfold tailWord_3638337
  simp only [CollatzResearch.WordTrace]
  refine ⟨132701052219933902334241265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88467368146622601556160843 132701052219933902334241265)
  ·
    refine ⟨99525789164950426750680949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132701052219933902334241265 99525789164950426750680949)
    ·
      refine ⟨9330542734214102507876339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99525789164950426750680949 9330542734214102507876339)
      ·
        refine ⟨13995814101321153761814509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9330542734214102507876339 13995814101321153761814509)
        ·
          refine ⟨5248430287995432660680441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13995814101321153761814509 5248430287995432660680441)
          ·
            refine ⟨3936322715996574495510331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5248430287995432660680441 3936322715996574495510331)
            ·
              refine ⟨5904484073994861743265497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936322715996574495510331 5904484073994861743265497)
              ·
                refine ⟨4428363055496146307449123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5904484073994861743265497 4428363055496146307449123)
                ·
                  refine ⟨6642544583244219461173685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4428363055496146307449123 6642544583244219461173685)
                  ·
                    refine ⟨622738554679145574485033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6642544583244219461173685 622738554679145574485033)
                    ·
                      rfl

theorem cell23_3638337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_3638337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638337 prefixEnd_3638337 := by exact prefixLift 3638337
  have htrace : WordTrace (prefixWord ++ tailWord_3638337) baseStart_3638337 baseEnd_3638337 := by
    simpa [prefixWord, tailWord_3638337, baseEnd_3638337] using wordTrace_append hprefix tailTrace_3638337
  have hstable : (prefixWord ++ tailWord_3638337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638337).length < 2 ^ (prefixWord ++ tailWord_3638337).sum := by decide
  have hdescent : baseEnd_3638337 < baseStart_3638337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638346 : List Nat := [3, 1, 2, 1, 1, 2, 4, 9]
def baseStart_3638346 : Nat := 118140960795 + 3638346 * 2 ^ 59
def prefixEnd_3638346 : Nat := 4983230072969 + 3 ^ 40 * 3638346 * 2
def baseEnd_3638346 : Nat := 69193343902345451416391

theorem tailTrace_3638346 : CollatzResearch.WordTrace tailWord_3638346 prefixEnd_3638346 69193343902345451416391 := by
  unfold tailWord_3638346
  simp only [CollatzResearch.WordTrace]
  refine ⟨33175345119225324217829723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88467586984600864580879261 33175345119225324217829723)
  ·
    refine ⟨49763017678837986326744585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33175345119225324217829723 49763017678837986326744585)
    ·
      refine ⟨37322263259128489745058439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49763017678837986326744585 37322263259128489745058439)
      ·
        refine ⟨55983394888692734617587659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37322263259128489745058439 55983394888692734617587659)
        ·
          refine ⟨83975092333039101926381489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55983394888692734617587659 83975092333039101926381489)
          ·
            refine ⟨62981319249779326444786117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83975092333039101926381489 62981319249779326444786117)
            ·
              refine ⟨11808997359333623708397397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62981319249779326444786117 11808997359333623708397397)
              ·
                refine ⟨69193343902345451416391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11808997359333623708397397 69193343902345451416391)
                ·
                  rfl

theorem cell23_3638346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 9].length) (baseStart_3638346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638346 prefixEnd_3638346 := by exact prefixLift 3638346
  have htrace : WordTrace (prefixWord ++ tailWord_3638346) baseStart_3638346 baseEnd_3638346 := by
    simpa [prefixWord, tailWord_3638346, baseEnd_3638346] using wordTrace_append hprefix tailTrace_3638346
  have hstable : (prefixWord ++ tailWord_3638346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638346).length < 2 ^ (prefixWord ++ tailWord_3638346).sum := by decide
  have hdescent : baseEnd_3638346 < baseStart_3638346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638373 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 3, 3, 3]
def baseStart_3638373 : Nat := 118140960795 + 3638373 * 2 ^ 59
def prefixEnd_3638373 : Nat := 4983230072969 + 3 ^ 40 * 3638373 * 2
def baseEnd_3638373 : Nat := 1868234149340998582604933

theorem tailTrace_3638373 : CollatzResearch.WordTrace tailWord_3638373 prefixEnd_3638373 1868234149340998582604933 := by
  unfold tailWord_3638373
  simp only [CollatzResearch.WordTrace]
  refine ⟨132702365247803480482551773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88468243498535653655034515 132702365247803480482551773)
  ·
    refine ⟨49763386967926305180956915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132702365247803480482551773 49763386967926305180956915)
    ·
      refine ⟨74645080451889457771435373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49763386967926305180956915 74645080451889457771435373)
      ·
        refine ⟨27991905169458546664288265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74645080451889457771435373 27991905169458546664288265)
        ·
          refine ⟨20993928877093909998216199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27991905169458546664288265 20993928877093909998216199)
          ·
            refine ⟨31490893315640864997324299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20993928877093909998216199 31490893315640864997324299)
            ·
              refine ⟨47236339973461297495986449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31490893315640864997324299 47236339973461297495986449)
              ·
                refine ⟨35427254980095973121989837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47236339973461297495986449 35427254980095973121989837)
                ·
                  refine ⟨13285220617535989920746189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35427254980095973121989837 13285220617535989920746189)
                  ·
                    refine ⟨4981957731575996220279821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13285220617535989920746189 4981957731575996220279821)
                    ·
                      refine ⟨1868234149340998582604933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4981957731575996220279821 1868234149340998582604933)
                      ·
                        rfl

theorem cell23_3638373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_3638373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638373 prefixEnd_3638373 := by exact prefixLift 3638373
  have htrace : WordTrace (prefixWord ++ tailWord_3638373) baseStart_3638373 baseEnd_3638373 := by
    simpa [prefixWord, tailWord_3638373, baseEnd_3638373] using wordTrace_append hprefix tailTrace_3638373
  have hstable : (prefixWord ++ tailWord_3638373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638373).length < 2 ^ (prefixWord ++ tailWord_3638373).sum := by decide
  have hdescent : baseEnd_3638373 < baseStart_3638373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638400 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 3, 3, 2]
def baseStart_3638400 : Nat := 118140960795 + 3638400 * 2 ^ 59
def prefixEnd_3638400 : Nat := 4983230072969 + 3 ^ 40 * 3638400 * 2
def baseEnd_3638400 : Nat := 1868248013318669976967309

theorem tailTrace_3638400 : CollatzResearch.WordTrace tailWord_3638400 prefixEnd_3638400 1868248013318669976967309 := by
  unfold tailWord_3638400
  simp only [CollatzResearch.WordTrace]
  refine ⟨66351675009352832046892327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88468900012470442729189769 66351675009352832046892327)
  ·
    refine ⟨99527512514029248070338491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66351675009352832046892327 99527512514029248070338491)
    ·
      refine ⟨149291268771043872105507737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99527512514029248070338491 149291268771043872105507737)
      ·
        refine ⟨111968451578282904079130803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149291268771043872105507737 111968451578282904079130803)
        ·
          refine ⟨167952677367424356118696205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111968451578282904079130803 167952677367424356118696205)
          ·
            refine ⟨62982254012784133544511077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167952677367424356118696205 62982254012784133544511077)
            ·
              refine ⟨11809172627397025039595827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62982254012784133544511077 11809172627397025039595827)
              ·
                refine ⟨17713758941095537559393741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11809172627397025039595827 17713758941095537559393741)
                ·
                  refine ⟨6642659602910826584772653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17713758941095537559393741 6642659602910826584772653)
                  ·
                    refine ⟨2490997351091559969289745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6642659602910826584772653 2490997351091559969289745)
                    ·
                      refine ⟨1868248013318669976967309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2490997351091559969289745 1868248013318669976967309)
                      ·
                        rfl

theorem cell23_3638400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 3, 3, 2].length) (baseStart_3638400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638400 prefixEnd_3638400 := by exact prefixLift 3638400
  have htrace : WordTrace (prefixWord ++ tailWord_3638400) baseStart_3638400 baseEnd_3638400 := by
    simpa [prefixWord, tailWord_3638400, baseEnd_3638400] using wordTrace_append hprefix tailTrace_3638400
  have hstable : (prefixWord ++ tailWord_3638400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638400).length < 2 ^ (prefixWord ++ tailWord_3638400).sum := by decide
  have hdescent : baseEnd_3638400 < baseStart_3638400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638423 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 2, 6]
def baseStart_3638423 : Nat := 118140960795 + 3638423 * 2 ^ 59
def prefixEnd_3638423 : Nat := 4983230072969 + 3 ^ 40 * 3638423 * 2
def baseEnd_3638423 : Nat := 622753274457907795659901

theorem tailTrace_3638423 : CollatzResearch.WordTrace tailWord_3638423 prefixEnd_3638423 622753274457907795659901 := by
  unfold tailWord_3638423
  simp only [CollatzResearch.WordTrace]
  refine ⟨132704188897622339021871923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88469459265081559347914615 132704188897622339021871923)
  ·
    refine ⟨199056283346433508532807885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132704188897622339021871923 199056283346433508532807885)
    ·
      refine ⟨74646106254912565699802957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199056283346433508532807885 74646106254912565699802957)
      ·
        refine ⟨27992289845592212137426109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74646106254912565699802957 27992289845592212137426109)
        ·
          refine ⟨10497108692097079551534791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27992289845592212137426109 10497108692097079551534791)
          ·
            refine ⟨15745663038145619327302187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10497108692097079551534791 15745663038145619327302187)
            ·
              refine ⟨23618494557218428990953281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15745663038145619327302187 23618494557218428990953281)
              ·
                refine ⟨17713870917913821743214961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23618494557218428990953281 17713870917913821743214961)
                ·
                  refine ⟨13285403188435366307411221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17713870917913821743214961 13285403188435366307411221)
                  ·
                    refine ⟨622753274457907795659901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13285403188435366307411221 622753274457907795659901)
                    ·
                      rfl

theorem cell23_3638423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_3638423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638423 prefixEnd_3638423 := by exact prefixLift 3638423
  have htrace : WordTrace (prefixWord ++ tailWord_3638423) baseStart_3638423 baseEnd_3638423 := by
    simpa [prefixWord, tailWord_3638423, baseEnd_3638423] using wordTrace_append hprefix tailTrace_3638423
  have hstable : (prefixWord ++ tailWord_3638423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638423).length < 2 ^ (prefixWord ++ tailWord_3638423).sum := by decide
  have hdescent : baseEnd_3638423 < baseStart_3638423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638424 : List Nat := [2, 1, 2, 4, 2, 3, 1, 2, 2, 1, 3]
def baseStart_3638424 : Nat := 118140960795 + 3638424 * 2 ^ 59
def prefixEnd_3638424 : Nat := 4983230072969 + 3 ^ 40 * 3638424 * 2
def baseEnd_3638424 : Nat := 1868260336854377883067199

theorem tailTrace_3638424 : CollatzResearch.WordTrace tailWord_3638424 prefixEnd_3638424 1868260336854377883067199 := by
  unfold tailWord_3638424
  simp only [CollatzResearch.WordTrace]
  refine ⟨66352112685309358096329163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88469483580412477461772217 66352112685309358096329163)
  ·
    refine ⟨99528169027964037144493745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66352112685309358096329163 99528169027964037144493745)
    ·
      refine ⟨74646126770973027858370309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99528169027964037144493745 74646126770973027858370309)
      ·
        refine ⟨13996148769557442723444433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74646126770973027858370309 13996148769557442723444433)
        ·
          refine ⟨10497111577168082042583325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13996148769557442723444433 10497111577168082042583325)
          ·
            refine ⟨3936416841438030765968747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10497111577168082042583325 3936416841438030765968747)
            ·
              refine ⟨5904625262157046148953121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936416841438030765968747 5904625262157046148953121)
              ·
                refine ⟨4428468946617784611714841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5904625262157046148953121 4428468946617784611714841)
                ·
                  refine ⟨3321351709963338458786131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4428468946617784611714841 3321351709963338458786131)
                  ·
                    refine ⟨4982027564945007688179197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3321351709963338458786131 4982027564945007688179197)
                    ·
                      refine ⟨1868260336854377883067199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4982027564945007688179197 1868260336854377883067199)
                      ·
                        rfl

theorem cell23_3638424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_3638424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638424 prefixEnd_3638424 := by exact prefixLift 3638424
  have htrace : WordTrace (prefixWord ++ tailWord_3638424) baseStart_3638424 baseEnd_3638424 := by
    simpa [prefixWord, tailWord_3638424, baseEnd_3638424] using wordTrace_append hprefix tailTrace_3638424
  have hstable : (prefixWord ++ tailWord_3638424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638424).length < 2 ^ (prefixWord ++ tailWord_3638424).sum := by decide
  have hdescent : baseEnd_3638424 < baseStart_3638424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638447 : List Nat := [1, 1, 2, 1, 2, 3, 2, 5, 2, 2, 2]
def baseStart_3638447 : Nat := 118140960795 + 3638447 * 2 ^ 59
def prefixEnd_3638447 : Nat := 4983230072969 + 3 ^ 40 * 3638447 * 2
def baseEnd_3638447 : Nat := 1868272146909431293079593

theorem tailTrace_3638447 : CollatzResearch.WordTrace tailWord_3638447 prefixEnd_3638447 1868272146909431293079593 := by
  unfold tailWord_3638447
  simp only [CollatzResearch.WordTrace]
  refine ⟨132705064249535391120745595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88470042833023594080497063 132705064249535391120745595)
  ·
    refine ⟨199057596374303086681118393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132705064249535391120745595 199057596374303086681118393)
    ·
      refine ⟨149293197280727315010838795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199057596374303086681118393 149293197280727315010838795)
      ·
        refine ⟨223939795921090972516258193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149293197280727315010838795 223939795921090972516258193)
        ·
          refine ⟨167954846940818229387193645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223939795921090972516258193 167954846940818229387193645)
          ·
            refine ⟨62983067602806836020197617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167954846940818229387193645 62983067602806836020197617)
            ·
              refine ⟨47237300702105127015148213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62983067602806836020197617 47237300702105127015148213)
              ·
                refine ⟨4428496940822355657670145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47237300702105127015148213 4428496940822355657670145)
                ·
                  refine ⟨3321372705616766743252609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4428496940822355657670145 3321372705616766743252609)
                  ·
                    refine ⟨2491029529212575057439457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3321372705616766743252609 2491029529212575057439457)
                    ·
                      refine ⟨1868272146909431293079593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2491029529212575057439457 1868272146909431293079593)
                      ·
                        rfl

theorem cell23_3638447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 2, 2].length) (baseStart_3638447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638447 prefixEnd_3638447 := by exact prefixLift 3638447
  have htrace : WordTrace (prefixWord ++ tailWord_3638447) baseStart_3638447 baseEnd_3638447 := by
    simpa [prefixWord, tailWord_3638447, baseEnd_3638447] using wordTrace_append hprefix tailTrace_3638447
  have hstable : (prefixWord ++ tailWord_3638447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638447).length < 2 ^ (prefixWord ++ tailWord_3638447).sum := by decide
  have hdescent : baseEnd_3638447 < baseStart_3638447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638463 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 3]
def baseStart_3638463 : Nat := 118140960795 + 3638463 * 2 ^ 59
def prefixEnd_3638463 : Nat := 4983230072969 + 3 ^ 40 * 3638463 * 2
def baseEnd_3638463 : Nat := 1868280362599903230479519

theorem tailTrace_3638463 : CollatzResearch.WordTrace tailWord_3638463 prefixEnd_3638463 1868280362599903230479519 := by
  unfold tailWord_3638463
  simp only [CollatzResearch.WordTrace]
  refine ⟨132705647817477425853328043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88470431878318283902218695 132705647817477425853328043)
  ·
    refine ⟨199058471726216138779992065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132705647817477425853328043 199058471726216138779992065)
    ·
      refine ⟨149293853794662104084994049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199058471726216138779992065 149293853794662104084994049)
      ·
        refine ⟨111970390345996578063745537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149293853794662104084994049 111970390345996578063745537)
        ·
          refine ⟨83977792759497433547809153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111970390345996578063745537 83977792759497433547809153)
          ·
            refine ⟨62983344569623075160856865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83977792759497433547809153 62983344569623075160856865)
            ·
              refine ⟨47237508427217306370642649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62983344569623075160856865 47237508427217306370642649)
              ·
                refine ⟨35428131320412979777981987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47237508427217306370642649 35428131320412979777981987)
                ·
                  refine ⟨53142196980619469666972981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35428131320412979777981987 53142196980619469666972981)
                  ·
                    refine ⟨4982080966933075281278717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53142196980619469666972981 4982080966933075281278717)
                    ·
                      refine ⟨1868280362599903230479519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4982080966933075281278717 1868280362599903230479519)
                      ·
                        rfl

theorem cell23_3638463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_3638463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638463 prefixEnd_3638463 := by exact prefixLift 3638463
  have htrace : WordTrace (prefixWord ++ tailWord_3638463) baseStart_3638463 baseEnd_3638463 := by
    simpa [prefixWord, tailWord_3638463, baseEnd_3638463] using wordTrace_append hprefix tailTrace_3638463
  have hstable : (prefixWord ++ tailWord_3638463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638463).length < 2 ^ (prefixWord ++ tailWord_3638463).sum := by decide
  have hdescent : baseEnd_3638463 < baseStart_3638463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638483 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 2, 5]
def baseStart_3638483 : Nat := 118140960795 + 3638483 * 2 ^ 59
def prefixEnd_3638483 : Nat := 4983230072969 + 3 ^ 40 * 3638483 * 2
def baseEnd_3638483 : Nat := 622763544070997717409809

theorem tailTrace_3638483 : CollatzResearch.WordTrace tailWord_3638483 prefixEnd_3638483 622763544070997717409809 := by
  unfold tailWord_3638483
  simp only [CollatzResearch.WordTrace]
  refine ⟨132706377277404969269056103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88470918184936646179370735 132706377277404969269056103)
  ·
    refine ⟨199059565916107453903584155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132706377277404969269056103 199059565916107453903584155)
    ·
      refine ⟨298589348874161180855376233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199059565916107453903584155 298589348874161180855376233)
      ·
        refine ⟨223942011655620885641532175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298589348874161180855376233 223942011655620885641532175)
        ·
          refine ⟨335913017483431328462298263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223942011655620885641532175 335913017483431328462298263)
          ·
            refine ⟨503869526225146992693447395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335913017483431328462298263 503869526225146992693447395)
            ·
              refine ⟨755804289337720489040171093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503869526225146992693447395 755804289337720489040171093)
              ·
                refine ⟨8857081515676411980939505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 755804289337720489040171093 8857081515676411980939505)
                ·
                  refine ⟨6642811136757308985704629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8857081515676411980939505 6642811136757308985704629)
                  ·
                    refine ⟨622763544070997717409809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6642811136757308985704629 622763544070997717409809)
                    ·
                      rfl

theorem cell23_3638483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 5].length) (baseStart_3638483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638483 prefixEnd_3638483 := by exact prefixLift 3638483
  have htrace : WordTrace (prefixWord ++ tailWord_3638483) baseStart_3638483 baseEnd_3638483 := by
    simpa [prefixWord, tailWord_3638483, baseEnd_3638483] using wordTrace_append hprefix tailTrace_3638483
  have hstable : (prefixWord ++ tailWord_3638483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638483).length < 2 ^ (prefixWord ++ tailWord_3638483).sum := by decide
  have hdescent : baseEnd_3638483 < baseStart_3638483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638490 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2]
def baseStart_3638490 : Nat := 118140960795 + 3638490 * 2 ^ 59
def prefixEnd_3638490 : Nat := 4983230072969 + 3 ^ 40 * 3638490 * 2
def baseEnd_3638490 : Nat := 1868294226577574624841895

theorem tailTrace_3638490 : CollatzResearch.WordTrace tailWord_3638490 prefixEnd_3638490 1868294226577574624841895 := by
  unfold tailWord_3638490
  simp only [CollatzResearch.WordTrace]
  refine ⟨33176658147094902366140231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88471088392253072976373949 33176658147094902366140231)
  ·
    refine ⟨49764987220642353549210347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33176658147094902366140231 49764987220642353549210347)
    ·
      refine ⟨74647480830963530323815521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49764987220642353549210347 74647480830963530323815521)
      ·
        refine ⟨55985610623222647742861641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74647480830963530323815521 55985610623222647742861641)
        ·
          refine ⟨41989207967416985807146231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55985610623222647742861641 41989207967416985807146231)
          ·
            refine ⟨62983811951125478710719347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41989207967416985807146231 62983811951125478710719347)
            ·
              refine ⟨94475717926688218066079021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62983811951125478710719347 94475717926688218066079021)
              ·
                refine ⟨35428394222508081774779633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94475717926688218066079021 35428394222508081774779633)
                ·
                  refine ⟨26571295666881061331084725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35428394222508081774779633 26571295666881061331084725)
                  ·
                    refine ⟨2491058968770099499789193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26571295666881061331084725 2491058968770099499789193)
                    ·
                      refine ⟨1868294226577574624841895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2491058968770099499789193 1868294226577574624841895)
                      ·
                        rfl

theorem cell23_3638490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_3638490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638490 prefixEnd_3638490 := by exact prefixLift 3638490
  have htrace : WordTrace (prefixWord ++ tailWord_3638490) baseStart_3638490 baseEnd_3638490 := by
    simpa [prefixWord, tailWord_3638490, baseEnd_3638490] using wordTrace_append hprefix tailTrace_3638490
  have hstable : (prefixWord ++ tailWord_3638490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638490).length < 2 ^ (prefixWord ++ tailWord_3638490).sum := by decide
  have hdescent : baseEnd_3638490 < baseStart_3638490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638520 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 6, 4, 2]
def baseStart_3638520 : Nat := 118140960795 + 3638520 * 2 ^ 59
def prefixEnd_3638520 : Nat := 4983230072969 + 3 ^ 40 * 3638520 * 2
def baseEnd_3638520 : Nat := 1868309630997209507466757

theorem tailTrace_3638520 : CollatzResearch.WordTrace tailWord_3638520 prefixEnd_3638520 1868309630997209507466757 := by
  unfold tailWord_3638520
  simp only [CollatzResearch.WordTrace]
  refine ⟨66353863389135462294076507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88471817852180616392102009 66353863389135462294076507)
  ·
    refine ⟨99530795083703193441114761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66353863389135462294076507 99530795083703193441114761)
    ·
      refine ⟨74648096312777395080836071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99530795083703193441114761 74648096312777395080836071)
      ·
        refine ⟨111972144469166092621254107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74648096312777395080836071 111972144469166092621254107)
        ·
          refine ⟨167958216703749138931881161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111972144469166092621254107 167958216703749138931881161)
          ·
            refine ⟨125968662527811854198910871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167958216703749138931881161 125968662527811854198910871)
            ·
              refine ⟨188952993791717781298366307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125968662527811854198910871 188952993791717781298366307)
              ·
                refine ⟨283429490687576671947549461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188952993791717781298366307 283429490687576671947549461)
                ·
                  refine ⟨13285757375980156497541381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 283429490687576671947549461 13285757375980156497541381)
                  ·
                    refine ⟨2491079507996279343289009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13285757375980156497541381 2491079507996279343289009)
                    ·
                      refine ⟨1868309630997209507466757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2491079507996279343289009 1868309630997209507466757)
                      ·
                        rfl

theorem cell23_3638520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 6, 4, 2].length) (baseStart_3638520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638520 prefixEnd_3638520 := by exact prefixLift 3638520
  have htrace : WordTrace (prefixWord ++ tailWord_3638520) baseStart_3638520 baseEnd_3638520 := by
    simpa [prefixWord, tailWord_3638520, baseEnd_3638520] using wordTrace_append hprefix tailTrace_3638520
  have hstable : (prefixWord ++ tailWord_3638520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638520).length < 2 ^ (prefixWord ++ tailWord_3638520).sum := by decide
  have hdescent : baseEnd_3638520 < baseStart_3638520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638533 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_3638533 : Nat := 118140960795 + 3638533 * 2 ^ 59
def prefixEnd_3638533 : Nat := 4983230072969 + 3 ^ 40 * 3638533 * 2
def baseEnd_3638533 : Nat := 1868316306245717956604197

theorem tailTrace_3638533 : CollatzResearch.WordTrace tailWord_3638533 prefixEnd_3638533 1868316306245717956604197 := by
  unfold tailWord_3638533
  simp only [CollatzResearch.WordTrace]
  refine ⟨132708200927223827808376253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88472133951482551872250835 132708200927223827808376253)
  ·
    refine ⟨49765575347708935428141095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132708200927223827808376253 49765575347708935428141095)
    ·
      refine ⟨74648363021563403142211643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49765575347708935428141095 74648363021563403142211643)
      ·
        refine ⟨111972544532345104713317465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74648363021563403142211643 111972544532345104713317465)
        ·
          refine ⟨83979408399258828534988099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111972544532345104713317465 83979408399258828534988099)
          ·
            refine ⟨125969112598888242802482149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83979408399258828534988099 125969112598888242802482149)
            ·
              refine ⟨23619208612291545525465403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125969112598888242802482149 23619208612291545525465403)
              ·
                refine ⟨35428812918437318288198105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23619208612291545525465403 35428812918437318288198105)
                ·
                  refine ⟨26571609688827988716148579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35428812918437318288198105 26571609688827988716148579)
                  ·
                    refine ⟨39857414533241983074222869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26571609688827988716148579 39857414533241983074222869)
                    ·
                      refine ⟨1868316306245717956604197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39857414533241983074222869 1868316306245717956604197)
                      ·
                        rfl

theorem cell23_3638533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_3638533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638533 prefixEnd_3638533 := by exact prefixLift 3638533
  have htrace : WordTrace (prefixWord ++ tailWord_3638533) baseStart_3638533 baseEnd_3638533 := by
    simpa [prefixWord, tailWord_3638533, baseEnd_3638533] using wordTrace_append hprefix tailTrace_3638533
  have hstable : (prefixWord ++ tailWord_3638533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638533).length < 2 ^ (prefixWord ++ tailWord_3638533).sum := by decide
  have hdescent : baseEnd_3638533 < baseStart_3638533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638583 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_3638583 : Nat := 118140960795 + 3638583 * 2 ^ 59
def prefixEnd_3638583 : Nat := 4983230072969 + 3 ^ 40 * 3638583 * 2
def baseEnd_3638583 : Nat := 1868341980278442760978967

theorem tailTrace_3638583 : CollatzResearch.WordTrace tailWord_3638583 prefixEnd_3638583 1868341980278442760978967 := by
  unfold tailWord_3638583
  simp only [CollatzResearch.WordTrace]
  refine ⟨132710024577042686347696403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88473349718028457565130935 132710024577042686347696403)
  ·
    refine ⟨199065036865564029521544605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132710024577042686347696403 199065036865564029521544605)
    ·
      refine ⟨74649388824586511070579227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199065036865564029521544605 74649388824586511070579227)
      ·
        refine ⟨111974083236879766605868841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74649388824586511070579227 111974083236879766605868841)
        ·
          refine ⟨83980562427659824954401631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111974083236879766605868841 83980562427659824954401631)
          ·
            refine ⟨125970843641489737431602447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83980562427659824954401631 125970843641489737431602447)
            ·
              refine ⟨188956265462234606147403671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125970843641489737431602447 188956265462234606147403671)
              ·
                refine ⟨283434398193351909221105507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188956265462234606147403671 283434398193351909221105507)
                ·
                  refine ⟨425151597290027863831658261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283434398193351909221105507 425151597290027863831658261)
                  ·
                    refine ⟨19928981122970056117108981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 425151597290027863831658261 19928981122970056117108981)
                    ·
                      refine ⟨1868341980278442760978967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19928981122970056117108981 1868341980278442760978967)
                      ·
                        rfl

theorem cell23_3638583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_3638583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638583 prefixEnd_3638583 := by exact prefixLift 3638583
  have htrace : WordTrace (prefixWord ++ tailWord_3638583) baseStart_3638583 baseEnd_3638583 := by
    simpa [prefixWord, tailWord_3638583, baseEnd_3638583] using wordTrace_append hprefix tailTrace_3638583
  have hstable : (prefixWord ++ tailWord_3638583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638583).length < 2 ^ (prefixWord ++ tailWord_3638583).sum := by decide
  have hdescent : baseEnd_3638583 < baseStart_3638583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638597 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 2, 3, 2]
def baseStart_3638597 : Nat := 118140960795 + 3638597 * 2 ^ 59
def prefixEnd_3638597 : Nat := 4983230072969 + 3 ^ 40 * 3638597 * 2
def baseEnd_3638597 : Nat := 1868349169007605706203903

theorem tailTrace_3638597 : CollatzResearch.WordTrace tailWord_3638597 prefixEnd_3638597 1868349169007605706203903 := by
  unfold tailWord_3638597
  simp only [CollatzResearch.WordTrace]
  refine ⟨132710535198991966738706045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88473690132661311159137363 132710535198991966738706045)
  ·
    refine ⟨49766450699621987527014767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132710535198991966738706045 49766450699621987527014767)
    ·
      refine ⟨74649676049432981290522151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49766450699621987527014767 74649676049432981290522151)
      ·
        refine ⟨111974514074149471935783227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74649676049432981290522151 111974514074149471935783227)
        ·
          refine ⟨167961771111224207903674841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111974514074149471935783227 167961771111224207903674841)
          ·
            refine ⟨125971328333418155927756131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167961771111224207903674841 125971328333418155927756131)
            ·
              refine ⟨188956992500127233891634197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125971328333418155927756131 188956992500127233891634197)
              ·
                refine ⟨8857359023443464088670353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 188956992500127233891634197 8857359023443464088670353)
                ·
                  refine ⟨6643019267582598066502765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8857359023443464088670353 6643019267582598066502765)
                  ·
                    refine ⟨2491132225343474274938537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6643019267582598066502765 2491132225343474274938537)
                    ·
                      refine ⟨1868349169007605706203903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2491132225343474274938537 1868349169007605706203903)
                      ·
                        rfl

theorem cell23_3638597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 3, 2].length) (baseStart_3638597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638597 prefixEnd_3638597 := by exact prefixLift 3638597
  have htrace : WordTrace (prefixWord ++ tailWord_3638597) baseStart_3638597 baseEnd_3638597 := by
    simpa [prefixWord, tailWord_3638597, baseEnd_3638597] using wordTrace_append hprefix tailTrace_3638597
  have hstable : (prefixWord ++ tailWord_3638597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638597).length < 2 ^ (prefixWord ++ tailWord_3638597).sum := by decide
  have hdescent : baseEnd_3638597 < baseStart_3638597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638598 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_3638598 : Nat := 118140960795 + 3638598 * 2 ^ 59
def prefixEnd_3638598 : Nat := 4983230072969 + 3 ^ 40 * 3638598 * 2
def baseEnd_3638598 : Nat := 622783227496086734097133

theorem tailTrace_3638598 : CollatzResearch.WordTrace tailWord_3638598 prefixEnd_3638598 622783227496086734097133 := by
  unfold tailWord_3638598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4147205364749635747171639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88473714447992229272994965 4147205364749635747171639)
  ·
    refine ⟨6220808047124453620757459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4147205364749635747171639 6220808047124453620757459)
    ·
      refine ⟨9331212070686680431136189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6220808047124453620757459 9331212070686680431136189)
      ·
        refine ⟨3499204526507505161676071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9331212070686680431136189 3499204526507505161676071)
        ·
          refine ⟨5248806789761257742514107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3499204526507505161676071 5248806789761257742514107)
          ·
            refine ⟨7873210184641886613771161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5248806789761257742514107 7873210184641886613771161)
            ·
              refine ⟨5904907638481414960328371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7873210184641886613771161 5904907638481414960328371)
              ·
                refine ⟨8857361457722122440492557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904907638481414960328371 8857361457722122440492557)
                ·
                  refine ⟨3321510546645795915184709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8857361457722122440492557 3321510546645795915184709)
                  ·
                    refine ⟨622783227496086734097133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3321510546645795915184709 622783227496086734097133)
                    ·
                      rfl

theorem cell23_3638598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_3638598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638598 prefixEnd_3638598 := by exact prefixLift 3638598
  have htrace : WordTrace (prefixWord ++ tailWord_3638598) baseStart_3638598 baseEnd_3638598 := by
    simpa [prefixWord, tailWord_3638598, baseEnd_3638598] using wordTrace_append hprefix tailTrace_3638598
  have hstable : (prefixWord ++ tailWord_3638598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638598).length < 2 ^ (prefixWord ++ tailWord_3638598).sum := by decide
  have hdescent : baseEnd_3638598 < baseStart_3638598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638604 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 3, 1, 3]
def baseStart_3638604 : Nat := 118140960795 + 3638604 * 2 ^ 59
def prefixEnd_3638604 : Nat := 4983230072969 + 3 ^ 40 * 3638604 * 2
def baseEnd_3638604 : Nat := 1868352763372187178816371

theorem tailTrace_3638604 : CollatzResearch.WordTrace tailWord_3638604 prefixEnd_3638604 1868352763372187178816371 := by
  unfold tailWord_3638604
  simp only [CollatzResearch.WordTrace]
  refine ⟨66355395254983303467105433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88473860339977737956140577 66355395254983303467105433)
  ·
    refine ⟨49766546441237477600329075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66355395254983303467105433 49766546441237477600329075)
    ·
      refine ⟨74649819661856216400493613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49766546441237477600329075 74649819661856216400493613)
      ·
        refine ⟨27993682373196081150185105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74649819661856216400493613 27993682373196081150185105)
        ·
          refine ⟨20995261779897060862638829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27993682373196081150185105 20995261779897060862638829)
          ·
            refine ⟨7873223167461397823489561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20995261779897060862638829 7873223167461397823489561)
            ·
              refine ⟨5904917375596048367617171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7873223167461397823489561 5904917375596048367617171)
              ·
                refine ⟨8857376063394072551425757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5904917375596048367617171 8857376063394072551425757)
                ·
                  refine ⟨3321516023772777206784659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8857376063394072551425757 3321516023772777206784659)
                  ·
                    refine ⟨4982274035659165810176989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3321516023772777206784659 4982274035659165810176989)
                    ·
                      refine ⟨1868352763372187178816371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4982274035659165810176989 1868352763372187178816371)
                      ·
                        rfl

theorem cell23_3638604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_3638604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638604 prefixEnd_3638604 := by exact prefixLift 3638604
  have htrace : WordTrace (prefixWord ++ tailWord_3638604) baseStart_3638604 baseEnd_3638604 := by
    simpa [prefixWord, tailWord_3638604, baseEnd_3638604] using wordTrace_append hprefix tailTrace_3638604
  have hstable : (prefixWord ++ tailWord_3638604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638604).length < 2 ^ (prefixWord ++ tailWord_3638604).sum := by decide
  have hdescent : baseEnd_3638604 < baseStart_3638604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638627 : List Nat := [1, 1, 1, 5, 2, 2, 1, 4, 1, 1, 4]
def baseStart_3638627 : Nat := 118140960795 + 3638627 * 2 ^ 59
def prefixEnd_3638627 : Nat := 4983230072969 + 3 ^ 40 * 3638627 * 2
def baseEnd_3638627 : Nat := 1868364573427240588828765

theorem tailTrace_3638627 : CollatzResearch.WordTrace tailWord_3638627 prefixEnd_3638627 1868364573427240588828765 := by
  unfold tailWord_3638627
  simp only [CollatzResearch.WordTrace]
  refine ⟨132711629388883281862298135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88474419592588854574865423 132711629388883281862298135)
  ·
    refine ⟨199067444083324922793447203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132711629388883281862298135 199067444083324922793447203)
    ·
      refine ⟨298601166124987384190170805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199067444083324922793447203 298601166124987384190170805)
      ·
        refine ⟨27993859324217567267828513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 298601166124987384190170805 27993859324217567267828513)
        ·
          refine ⟨20995394493163175450871385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27993859324217567267828513 20995394493163175450871385)
          ·
            refine ⟨15746545869872381588153539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20995394493163175450871385 15746545869872381588153539)
            ·
              refine ⟨23619818804808572382230309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15746545869872381588153539 23619818804808572382230309)
              ·
                refine ⟨4428716025901607321668183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23619818804808572382230309 4428716025901607321668183)
                ·
                  refine ⟨6643074038852410982502275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4428716025901607321668183 6643074038852410982502275)
                  ·
                    refine ⟨9964611058278616473753413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6643074038852410982502275 9964611058278616473753413)
                    ·
                      refine ⟨1868364573427240588828765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9964611058278616473753413 1868364573427240588828765)
                      ·
                        rfl

theorem cell23_3638627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_3638627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638627 prefixEnd_3638627 := by exact prefixLift 3638627
  have htrace : WordTrace (prefixWord ++ tailWord_3638627) baseStart_3638627 baseEnd_3638627 := by
    simpa [prefixWord, tailWord_3638627, baseEnd_3638627] using wordTrace_append hprefix tailTrace_3638627
  have hstable : (prefixWord ++ tailWord_3638627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638627).length < 2 ^ (prefixWord ++ tailWord_3638627).sum := by decide
  have hdescent : baseEnd_3638627 < baseStart_3638627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638637 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_3638637 : Nat := 118140960795 + 3638637 * 2 ^ 59
def prefixEnd_3638637 : Nat := 4983230072969 + 3 ^ 40 * 3638637 * 2
def baseEnd_3638637 : Nat := 622789902744595183234573

theorem tailTrace_3638637 : CollatzResearch.WordTrace tailWord_3638637 prefixEnd_3638637 622789902744595183234573 := by
  unfold tailWord_3638637
  simp only [CollatzResearch.WordTrace]
  refine ⟨132711994118847053570162165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88474662745898035713441443 132711994118847053570162165)
  ·
    refine ⟨12441749448641911272202703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132711994118847053570162165 12441749448641911272202703)
    ·
      refine ⟨18662624172962866908304055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12441749448641911272202703 18662624172962866908304055)
      ·
        refine ⟨27993936259444300362456083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18662624172962866908304055 27993936259444300362456083)
        ·
          refine ⟨41990904389166450543684125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27993936259444300362456083 41990904389166450543684125)
          ·
            refine ⟨15746589145937418953881547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41990904389166450543684125 15746589145937418953881547)
            ·
              refine ⟨23619883718906128430822321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15746589145937418953881547 23619883718906128430822321)
              ·
                refine ⟨17714912789179596323116741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23619883718906128430822321 17714912789179596323116741)
                ·
                  refine ⟨3321546147971174310584389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17714912789179596323116741 3321546147971174310584389)
                  ·
                    refine ⟨622789902744595183234573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3321546147971174310584389 622789902744595183234573)
                    ·
                      rfl

theorem cell23_3638637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_3638637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638637 prefixEnd_3638637 := by exact prefixLift 3638637
  have htrace : WordTrace (prefixWord ++ tailWord_3638637) baseStart_3638637 baseEnd_3638637 := by
    simpa [prefixWord, tailWord_3638637, baseEnd_3638637] using wordTrace_append hprefix tailTrace_3638637
  have hstable : (prefixWord ++ tailWord_3638637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638637).length < 2 ^ (prefixWord ++ tailWord_3638637).sum := by decide
  have hdescent : baseEnd_3638637 < baseStart_3638637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638640 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 4]
def baseStart_3638640 : Nat := 118140960795 + 3638640 * 2 ^ 59
def prefixEnd_3638640 : Nat := 4983230072969 + 3 ^ 40 * 3638640 * 2
def baseEnd_3638640 : Nat := 1868371248675749037966205

theorem tailTrace_3638640 : CollatzResearch.WordTrace tailWord_3638640 prefixEnd_3638640 1868371248675749037966205 := by
  unfold tailWord_3638640
  simp only [CollatzResearch.WordTrace]
  refine ⟨66356051768918092541260687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88474735691890790055014249 66356051768918092541260687)
  ·
    refine ⟨99534077653377138811891031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66356051768918092541260687 99534077653377138811891031)
    ·
      refine ⟨149301116480065708217836547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99534077653377138811891031 149301116480065708217836547)
      ·
        refine ⟨223951674720098562326754821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149301116480065708217836547 223951674720098562326754821)
        ·
          refine ⟨41990939010018480436266529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223951674720098562326754821 41990939010018480436266529)
          ·
            refine ⟨31493204257513860327199897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41990939010018480436266529 31493204257513860327199897)
            ·
              refine ⟨23619903193135395245399923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31493204257513860327199897 23619903193135395245399923)
              ·
                refine ⟨35429854789703092868099885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23619903193135395245399923 35429854789703092868099885)
                ·
                  refine ⟨13286195546138659825537457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35429854789703092868099885 13286195546138659825537457)
                  ·
                    refine ⟨9964646659603994869153093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13286195546138659825537457 9964646659603994869153093)
                    ·
                      refine ⟨1868371248675749037966205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9964646659603994869153093 1868371248675749037966205)
                      ·
                        rfl

theorem cell23_3638640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_3638640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638640 prefixEnd_3638640 := by exact prefixLift 3638640
  have htrace : WordTrace (prefixWord ++ tailWord_3638640) baseStart_3638640 baseEnd_3638640 := by
    simpa [prefixWord, tailWord_3638640, baseEnd_3638640] using wordTrace_append hprefix tailTrace_3638640
  have hstable : (prefixWord ++ tailWord_3638640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638640).length < 2 ^ (prefixWord ++ tailWord_3638640).sum := by decide
  have hdescent : baseEnd_3638640 < baseStart_3638640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638647 : List Nat := [1, 1, 3, 1, 1, 2, 3, 5, 1, 2, 3]
def baseStart_3638647 : Nat := 118140960795 + 3638647 * 2 ^ 59
def prefixEnd_3638647 : Nat := 4983230072969 + 3 ^ 40 * 3638647 * 2
def baseEnd_3638647 : Nat := 1868374843040330510578673

theorem tailTrace_3638647 : CollatzResearch.WordTrace tailWord_3638647 prefixEnd_3638647 1868374843040330510578673 := by
  unfold tailWord_3638647
  simp only [CollatzResearch.WordTrace]
  refine ⟨132712358848810825278026195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88474905899207216852017463 132712358848810825278026195)
  ·
    refine ⟨199068538273216237917039293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132712358848810825278026195 199068538273216237917039293)
    ·
      refine ⟨74650701852456089218889735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199068538273216237917039293 74650701852456089218889735)
      ·
        refine ⟨111976052778684133828334603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74650701852456089218889735 111976052778684133828334603)
        ·
          refine ⟨167964079168026200742501905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111976052778684133828334603 167964079168026200742501905)
          ·
            refine ⟨125973059376019650556876429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167964079168026200742501905 125973059376019650556876429)
            ·
              refine ⟨47239897266007368958828661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125973059376019650556876429 47239897266007368958828661)
              ·
                refine ⟨4428740368688190839890187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47239897266007368958828661 4428740368688190839890187)
                ·
                  refine ⟨6643110553032286259835281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4428740368688190839890187 6643110553032286259835281)
                  ·
                    refine ⟨4982332914774214694876461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6643110553032286259835281 4982332914774214694876461)
                    ·
                      refine ⟨1868374843040330510578673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4982332914774214694876461 1868374843040330510578673)
                      ·
                        rfl

theorem cell23_3638647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_3638647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638647 prefixEnd_3638647 := by exact prefixLift 3638647
  have htrace : WordTrace (prefixWord ++ tailWord_3638647) baseStart_3638647 baseEnd_3638647 := by
    simpa [prefixWord, tailWord_3638647, baseEnd_3638647] using wordTrace_append hprefix tailTrace_3638647
  have hstable : (prefixWord ++ tailWord_3638647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638647).length < 2 ^ (prefixWord ++ tailWord_3638647).sum := by decide
  have hdescent : baseEnd_3638647 < baseStart_3638647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638661 : List Nat := [1, 3, 1, 1, 3, 1, 2, 6, 1, 2, 2]
def baseStart_3638661 : Nat := 118140960795 + 3638661 * 2 ^ 59
def prefixEnd_3638661 : Nat := 4983230072969 + 3 ^ 40 * 3638661 * 2
def baseEnd_3638661 : Nat := 1868382031769493455803609

theorem tailTrace_3638661 : CollatzResearch.WordTrace tailWord_3638661 prefixEnd_3638661 1868382031769493455803609 := by
  unfold tailWord_3638661
  simp only [CollatzResearch.WordTrace]
  refine ⟨132712869470760105669035837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88475246313840070446023891 132712869470760105669035837)
  ·
    refine ⟨49767326051535039625888439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132712869470760105669035837 49767326051535039625888439)
    ·
      refine ⟨74650989077302559438832659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49767326051535039625888439 74650989077302559438832659)
      ·
        refine ⟨111976483615953839158248989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74650989077302559438832659 111976483615953839158248989)
        ·
          refine ⟨41991181355982689684343371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111976483615953839158248989 41991181355982689684343371)
          ·
            refine ⟨62986772033974034526515057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41991181355982689684343371 62986772033974034526515057)
            ·
              refine ⟨47240079025480525894886293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62986772033974034526515057 47240079025480525894886293)
              ·
                refine ⟨2214378704319399651322795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47240079025480525894886293 2214378704319399651322795)
                ·
                  refine ⟨3321568056479099476984193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2214378704319399651322795 3321568056479099476984193)
                  ·
                    refine ⟨2491176042359324607738145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3321568056479099476984193 2491176042359324607738145)
                    ·
                      refine ⟨1868382031769493455803609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2491176042359324607738145 1868382031769493455803609)
                      ·
                        rfl

theorem cell23_3638661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 1, 2, 2].length) (baseStart_3638661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638661 prefixEnd_3638661 := by exact prefixLift 3638661
  have htrace : WordTrace (prefixWord ++ tailWord_3638661) baseStart_3638661 baseEnd_3638661 := by
    simpa [prefixWord, tailWord_3638661, baseEnd_3638661] using wordTrace_append hprefix tailTrace_3638661
  have hstable : (prefixWord ++ tailWord_3638661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638661).length < 2 ^ (prefixWord ++ tailWord_3638661).sum := by decide
  have hdescent : baseEnd_3638661 < baseStart_3638661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638720 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 5]
def baseStart_3638720 : Nat := 118140960795 + 3638720 * 2 ^ 59
def prefixEnd_3638720 : Nat := 4983230072969 + 3 ^ 40 * 3638720 * 2
def baseEnd_3638720 : Nat := 1868412327128108724965837

theorem tailTrace_3638720 : CollatzResearch.WordTrace tailWord_3638720 prefixEnd_3638720 1868412327128108724965837 := by
  unfold tailWord_3638720
  simp only [CollatzResearch.WordTrace]
  refine ⟨66357510688773179372716807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88476680918364239163622409 66357510688773179372716807)
  ·
    refine ⟨99536266033159769059075211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66357510688773179372716807 99536266033159769059075211)
    ·
      refine ⟨149304399049739653588612817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99536266033159769059075211 149304399049739653588612817)
      ·
        refine ⟨111978299287304740191459613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149304399049739653588612817 111978299287304740191459613)
        ·
          refine ⟨41991862232739277571797355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111978299287304740191459613 41991862232739277571797355)
          ·
            refine ⟨62987793349108916357696033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41991862232739277571797355 62987793349108916357696033)
            ·
              refine ⟨47240845011831687268272025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62987793349108916357696033 47240845011831687268272025)
              ·
                refine ⟨35430633758873765451204019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47240845011831687268272025 35430633758873765451204019)
                ·
                  refine ⟨53145950638310648176806029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35430633758873765451204019 53145950638310648176806029)
                  ·
                    refine ⟨19929731489366493066302261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53145950638310648176806029 19929731489366493066302261)
                    ·
                      refine ⟨1868412327128108724965837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19929731489366493066302261 1868412327128108724965837)
                      ·
                        rfl

theorem cell23_3638720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_3638720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638720 prefixEnd_3638720 := by exact prefixLift 3638720
  have htrace : WordTrace (prefixWord ++ tailWord_3638720) baseStart_3638720 baseEnd_3638720 := by
    simpa [prefixWord, tailWord_3638720, baseEnd_3638720] using wordTrace_append hprefix tailTrace_3638720
  have hstable : (prefixWord ++ tailWord_3638720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638720).length < 2 ^ (prefixWord ++ tailWord_3638720).sum := by decide
  have hdescent : baseEnd_3638720 < baseStart_3638720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638734 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2]
def baseStart_3638734 : Nat := 118140960795 + 3638734 * 2 ^ 59
def prefixEnd_3638734 : Nat := 4983230072969 + 3 ^ 40 * 3638734 * 2
def baseEnd_3638734 : Nat := 1868419515857271670190773

theorem tailTrace_3638734 : CollatzResearch.WordTrace tailWord_3638734 prefixEnd_3638734 1868419515857271670190773 := by
  unfold tailWord_3638734
  simp only [CollatzResearch.WordTrace]
  refine ⟨16589441499936954892055407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88477021332997092757628837 16589441499936954892055407)
  ·
    refine ⟨24884162249905432338083111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16589441499936954892055407 24884162249905432338083111)
    ·
      refine ⟨37326243374858148507124667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24884162249905432338083111 37326243374858148507124667)
      ·
        refine ⟨55989365062287222760687001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37326243374858148507124667 55989365062287222760687001)
        ·
          refine ⟨41992023796715417070515251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55989365062287222760687001 41992023796715417070515251)
          ·
            refine ⟨62988035695073125605772877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41992023796715417070515251 62988035695073125605772877)
            ·
              refine ⟨23620513385652422102164829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62988035695073125605772877 23620513385652422102164829)
              ·
                refine ⟨8857692519619658288311811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23620513385652422102164829 8857692519619658288311811)
                ·
                  refine ⟨13286538779429487432467717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8857692519619658288311811 13286538779429487432467717)
                  ·
                    refine ⟨2491226021143028893587697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13286538779429487432467717 2491226021143028893587697)
                    ·
                      refine ⟨1868419515857271670190773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2491226021143028893587697 1868419515857271670190773)
                      ·
                        rfl

theorem cell23_3638734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_3638734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638734 prefixEnd_3638734 := by exact prefixLift 3638734
  have htrace : WordTrace (prefixWord ++ tailWord_3638734) baseStart_3638734 baseEnd_3638734 := by
    simpa [prefixWord, tailWord_3638734, baseEnd_3638734] using wordTrace_append hprefix tailTrace_3638734
  have hstable : (prefixWord ++ tailWord_3638734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638734).length < 2 ^ (prefixWord ++ tailWord_3638734).sum := by decide
  have hdescent : baseEnd_3638734 < baseStart_3638734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638767 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 3]
def baseStart_3638767 : Nat := 118140960795 + 3638767 * 2 ^ 59
def prefixEnd_3638767 : Nat := 4983230072969 + 3 ^ 40 * 3638767 * 2
def baseEnd_3638767 : Nat := 1868436460718870041078121

theorem tailTrace_3638767 : CollatzResearch.WordTrace tailWord_3638767 prefixEnd_3638767 1868436460718870041078121 := by
  unfold tailWord_3638767
  simp only [CollatzResearch.WordTrace]
  refine ⟨132716735608376085772394555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88477823738917390514929703 132716735608376085772394555)
  ·
    refine ⟨199075103412564128658591833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132716735608376085772394555 199075103412564128658591833)
    ·
      refine ⟨149306327559423096493943875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199075103412564128658591833 149306327559423096493943875)
      ·
        refine ⟨223959491339134644740915813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149306327559423096493943875 223959491339134644740915813)
        ·
          refine ⟨41992404626087745888921715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223959491339134644740915813 41992404626087745888921715)
          ·
            refine ⟨62988606939131618833382573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41992404626087745888921715 62988606939131618833382573)
            ·
              refine ⟨23620727602174357062518465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62988606939131618833382573 23620727602174357062518465)
              ·
                refine ⟨17715545701630767796888849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23620727602174357062518465 17715545701630767796888849)
                ·
                  refine ⟨13286659276223075847666637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17715545701630767796888849 13286659276223075847666637)
                  ·
                    refine ⟨4982497228583653442874989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13286659276223075847666637 4982497228583653442874989)
                    ·
                      refine ⟨1868436460718870041078121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4982497228583653442874989 1868436460718870041078121)
                      ·
                        rfl

theorem cell23_3638767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 3].length) (baseStart_3638767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638767 prefixEnd_3638767 := by exact prefixLift 3638767
  have htrace : WordTrace (prefixWord ++ tailWord_3638767) baseStart_3638767 baseEnd_3638767 := by
    simpa [prefixWord, tailWord_3638767, baseEnd_3638767] using wordTrace_append hprefix tailTrace_3638767
  have hstable : (prefixWord ++ tailWord_3638767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638767).length < 2 ^ (prefixWord ++ tailWord_3638767).sum := by decide
  have hdescent : baseEnd_3638767 < baseStart_3638767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638768 : List Nat := [2, 1, 1, 1, 3, 6, 1, 2, 2, 2, 2]
def baseStart_3638768 : Nat := 118140960795 + 3638768 * 2 ^ 59
def prefixEnd_3638768 : Nat := 4983230072969 + 3 ^ 40 * 3638768 * 2
def baseEnd_3638768 : Nat := 1868436974199524537165617

theorem tailTrace_3638768 : CollatzResearch.WordTrace tailWord_3638768 prefixEnd_3638768 1868436974199524537165617 := by
  unfold tailWord_3638768
  simp only [CollatzResearch.WordTrace]
  refine ⟨66358386040686231471590479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88477848054248308628787305 66358386040686231471590479)
  ·
    refine ⟨99537579061029347207385719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66358386040686231471590479 99537579061029347207385719)
    ·
      refine ⟨149306368591544020811078579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99537579061029347207385719 149306368591544020811078579)
      ·
        refine ⟨223959552887316031216617869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149306368591544020811078579 223959552887316031216617869)
        ·
          refine ⟨83984832332743511706231701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223959552887316031216617869 83984832332743511706231701)
          ·
            refine ⟨3936789015597352111229611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 83984832332743511706231701 3936789015597352111229611)
            ·
              refine ⟨5905183523396028166844417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936789015597352111229611 5905183523396028166844417)
              ·
                refine ⟨4428887642547021125133313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5905183523396028166844417 4428887642547021125133313)
                ·
                  refine ⟨3321665731910265843849985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4428887642547021125133313 3321665731910265843849985)
                  ·
                    refine ⟨2491249298932699382887489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3321665731910265843849985 2491249298932699382887489)
                    ·
                      refine ⟨1868436974199524537165617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2491249298932699382887489 1868436974199524537165617)
                      ·
                        rfl

theorem cell23_3638768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 2, 2, 2].length) (baseStart_3638768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638768 prefixEnd_3638768 := by exact prefixLift 3638768
  have htrace : WordTrace (prefixWord ++ tailWord_3638768) baseStart_3638768 baseEnd_3638768 := by
    simpa [prefixWord, tailWord_3638768, baseEnd_3638768] using wordTrace_append hprefix tailTrace_3638768
  have hstable : (prefixWord ++ tailWord_3638768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638768).length < 2 ^ (prefixWord ++ tailWord_3638768).sum := by decide
  have hdescent : baseEnd_3638768 < baseStart_3638768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638774 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_3638774 : Nat := 118140960795 + 3638774 * 2 ^ 59
def prefixEnd_3638774 : Nat := 4983230072969 + 3 ^ 40 * 3638774 * 2
def baseEnd_3638774 : Nat := 207604450564827945965621

theorem tailTrace_3638774 : CollatzResearch.WordTrace tailWord_3638774 prefixEnd_3638774 207604450564827945965621 := by
  unfold tailWord_3638774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8294811932459420372993711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88477993946233817311932917 8294811932459420372993711)
  ·
    refine ⟨12442217898689130559490567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8294811932459420372993711 12442217898689130559490567)
    ·
      refine ⟨18663326848033695839235851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12442217898689130559490567 18663326848033695839235851)
      ·
        refine ⟨27994990272050543758853777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18663326848033695839235851 27994990272050543758853777)
        ·
          refine ⟨20996242704037907819140333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27994990272050543758853777 20996242704037907819140333)
          ·
            refine ⟨7873591014014215432177625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20996242704037907819140333 7873591014014215432177625)
            ·
              refine ⟨5905193260510661574133219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7873591014014215432177625 5905193260510661574133219)
              ·
                refine ⟨8857789890765992361199829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5905193260510661574133219 8857789890765992361199829)
                ·
                  refine ⟨207604450564827945965621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8857789890765992361199829 207604450564827945965621)
                  ·
                    rfl

theorem cell23_3638774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_3638774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638774 prefixEnd_3638774 := by exact prefixLift 3638774
  have htrace : WordTrace (prefixWord ++ tailWord_3638774) baseStart_3638774 baseEnd_3638774 := by
    simpa [prefixWord, tailWord_3638774, baseEnd_3638774] using wordTrace_append hprefix tailTrace_3638774
  have hstable : (prefixWord ++ tailWord_3638774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638774).length < 2 ^ (prefixWord ++ tailWord_3638774).sum := by decide
  have hdescent : baseEnd_3638774 < baseStart_3638774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638785 : List Nat := [1, 2, 4, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_3638785 : Nat := 118140960795 + 3638785 * 2 ^ 59
def prefixEnd_3638785 : Nat := 4983230072969 + 3 ^ 40 * 3638785 * 2
def baseEnd_3638785 : Nat := 1868445703370650970653039

theorem tailTrace_3638785 : CollatzResearch.WordTrace tailWord_3638785 prefixEnd_3638785 1868445703370650970653039 := by
  unfold tailWord_3638785
  simp only [CollatzResearch.WordTrace]
  refine ⟨132717392122310874846549809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88478261414873916564366539 132717392122310874846549809)
  ·
    refine ⟨99538044091733156134912357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132717392122310874846549809 99538044091733156134912357)
    ·
      refine ⟨18663383267199966775296067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99538044091733156134912357 18663383267199966775296067)
      ·
        refine ⟨27995074900799950162944101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18663383267199966775296067 27995074900799950162944101)
        ·
          refine ⟨5249076543899990655552019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27995074900799950162944101 5249076543899990655552019)
          ·
            refine ⟨7873614815849985983328029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5249076543899990655552019 7873614815849985983328029)
            ·
              refine ⟨2952605555943744743748011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7873614815849985983328029 2952605555943744743748011)
              ·
                refine ⟨4428908333915617115622017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2952605555943744743748011 4428908333915617115622017)
                ·
                  refine ⟨3321681250436712836716513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4428908333915617115622017 3321681250436712836716513)
                  ·
                    refine ⟨2491260937827534627537385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3321681250436712836716513 2491260937827534627537385)
                    ·
                      refine ⟨1868445703370650970653039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2491260937827534627537385 1868445703370650970653039)
                      ·
                        rfl

theorem cell23_3638785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_3638785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638785 prefixEnd_3638785 := by exact prefixLift 3638785
  have htrace : WordTrace (prefixWord ++ tailWord_3638785) baseStart_3638785 baseEnd_3638785 := by
    simpa [prefixWord, tailWord_3638785, baseEnd_3638785] using wordTrace_append hprefix tailTrace_3638785
  have hstable : (prefixWord ++ tailWord_3638785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638785).length < 2 ^ (prefixWord ++ tailWord_3638785).sum := by decide
  have hdescent : baseEnd_3638785 < baseStart_3638785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638808 : List Nat := [2, 1, 2, 3, 5, 1, 1, 3, 5]
def baseStart_3638808 : Nat := 118140960795 + 3638808 * 2 ^ 59
def prefixEnd_3638808 : Nat := 4983230072969 + 3 ^ 40 * 3638808 * 2
def baseEnd_3638808 : Nat := 207606390380633820073937

theorem tailTrace_3638808 : CollatzResearch.WordTrace tailWord_3638808 prefixEnd_3638808 207606390380633820073937 := by
  unfold tailWord_3638808
  simp only [CollatzResearch.WordTrace]
  refine ⟨66359115500613774887318539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88478820667485033183091385 66359115500613774887318539)
  ·
    refine ⟨99538673250920662330977809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66359115500613774887318539 99538673250920662330977809)
    ·
      refine ⟨74654004938190496748233357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99538673250920662330977809 74654004938190496748233357)
      ·
        refine ⟨27995251851821436280587509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74654004938190496748233357 27995251851821436280587509)
        ·
          refine ⟨2624554861108259651305079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27995251851821436280587509 2624554861108259651305079)
          ·
            refine ⟨3936832291662389476957619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2624554861108259651305079 3936832291662389476957619)
            ·
              refine ⟨5905248437493584215436429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936832291662389476957619 5905248437493584215436429)
              ·
                refine ⟨2214468164060094080788661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5905248437493584215436429 2214468164060094080788661)
                ·
                  refine ⟨207606390380633820073937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2214468164060094080788661 207606390380633820073937)
                  ·
                    rfl

theorem cell23_3638808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 5].length) (baseStart_3638808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638808 prefixEnd_3638808 := by exact prefixLift 3638808
  have htrace : WordTrace (prefixWord ++ tailWord_3638808) baseStart_3638808 baseEnd_3638808 := by
    simpa [prefixWord, tailWord_3638808, baseEnd_3638808] using wordTrace_append hprefix tailTrace_3638808
  have hstable : (prefixWord ++ tailWord_3638808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638808).length < 2 ^ (prefixWord ++ tailWord_3638808).sum := by decide
  have hdescent : baseEnd_3638808 < baseStart_3638808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638857 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 2, 5, 3]
def baseStart_3638857 : Nat := 118140960795 + 3638857 * 2 ^ 59
def prefixEnd_3638857 : Nat := 4983230072969 + 3 ^ 40 * 3638857 * 2
def baseEnd_3638857 : Nat := 1868482673977774688952707

theorem tailTrace_3638857 : CollatzResearch.WordTrace tailWord_3638857 prefixEnd_3638857 1868482673977774688952707 := by
  unfold tailWord_3638857
  simp only [CollatzResearch.WordTrace]
  refine ⟨132720018178050031143170825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88480012118700020762113883 132720018178050031143170825)
  ·
    refine ⟨99540013633537523357378119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132720018178050031143170825 99540013633537523357378119)
    ·
      refine ⟨149310020450306285036067179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99540013633537523357378119 149310020450306285036067179)
      ·
        refine ⟨223965030675459427554100769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149310020450306285036067179 223965030675459427554100769)
        ·
          refine ⟨167973773006594570665575577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223965030675459427554100769 167973773006594570665575577)
          ·
            refine ⟨125980329754945927999181683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167973773006594570665575577 125980329754945927999181683)
            ·
              refine ⟨188970494632418891998772525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125980329754945927999181683 188970494632418891998772525)
              ·
                refine ⟨70863935487157084499539697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188970494632418891998772525 70863935487157084499539697)
                ·
                  refine ⟨53147951615367813374654773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70863935487157084499539697 53147951615367813374654773)
                  ·
                    refine ⟨4982620463940732503873885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53147951615367813374654773 4982620463940732503873885)
                    ·
                      refine ⟨1868482673977774688952707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4982620463940732503873885 1868482673977774688952707)
                      ·
                        rfl

theorem cell23_3638857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5, 3].length) (baseStart_3638857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638857 prefixEnd_3638857 := by exact prefixLift 3638857
  have htrace : WordTrace (prefixWord ++ tailWord_3638857) baseStart_3638857 baseEnd_3638857 := by
    simpa [prefixWord, tailWord_3638857, baseEnd_3638857] using wordTrace_append hprefix tailTrace_3638857
  have hstable : (prefixWord ++ tailWord_3638857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638857).length < 2 ^ (prefixWord ++ tailWord_3638857).sum := by decide
  have hdescent : baseEnd_3638857 < baseStart_3638857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638885 : List Nat := [1, 3, 1, 3, 3, 3, 2, 2, 1, 4]
def baseStart_3638885 : Nat := 118140960795 + 3638885 * 2 ^ 59
def prefixEnd_3638885 : Nat := 4983230072969 + 3 ^ 40 * 3638885 * 2
def baseEnd_3638885 : Nat := 622832350478700193134193

theorem tailTrace_3638885 : CollatzResearch.WordTrace tailWord_3638885 prefixEnd_3638885 622832350478700193134193 := by
  unfold tailWord_3638885
  simp only [CollatzResearch.WordTrace]
  refine ⟨132721039421948591925190109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88480692947965727950126739 132721039421948591925190109)
  ·
    refine ⟨49770389783230721971946291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132721039421948591925190109 49770389783230721971946291)
    ·
      refine ⟨74655584674846082957919437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49770389783230721971946291 74655584674846082957919437)
      ·
        refine ⟨27995844253067281109219789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74655584674846082957919437 27995844253067281109219789)
        ·
          refine ⟨10498441594900230415957421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27995844253067281109219789 10498441594900230415957421)
          ·
            refine ⟨3936915598087586405984033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10498441594900230415957421 3936915598087586405984033)
            ·
              refine ⟨2952686698565689804488025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3936915598087586405984033 2952686698565689804488025)
              ·
                refine ⟨2214515023924267353366019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2952686698565689804488025 2214515023924267353366019)
                ·
                  refine ⟨3321772535886401030049029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2214515023924267353366019 3321772535886401030049029)
                  ·
                    refine ⟨622832350478700193134193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3321772535886401030049029 622832350478700193134193)
                    ·
                      rfl

theorem cell23_3638885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_3638885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638885 prefixEnd_3638885 := by exact prefixLift 3638885
  have htrace : WordTrace (prefixWord ++ tailWord_3638885) baseStart_3638885 baseEnd_3638885 := by
    simpa [prefixWord, tailWord_3638885, baseEnd_3638885] using wordTrace_append hprefix tailTrace_3638885
  have hstable : (prefixWord ++ tailWord_3638885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638885).length < 2 ^ (prefixWord ++ tailWord_3638885).sum := by decide
  have hdescent : baseEnd_3638885 < baseStart_3638885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638924 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 4, 4]
def baseStart_3638924 : Nat := 118140960795 + 3638924 * 2 ^ 59
def prefixEnd_3638924 : Nat := 4983230072969 + 3 ^ 40 * 3638924 * 2
def baseEnd_3638924 : Nat := 622839025727208642271633

theorem tailTrace_3638924 : CollatzResearch.WordTrace tailWord_3638924 prefixEnd_3638924 622839025727208642271633 := by
  unfold tailWord_3638924
  simp only [CollatzResearch.WordTrace]
  refine ⟨66361230934403650792929913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88481641245871534390573217 66361230934403650792929913)
  ·
    refine ⟨49770923200802738094697435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66361230934403650792929913 49770923200802738094697435)
    ·
      refine ⟨74656384801204107142046153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49770923200802738094697435 74656384801204107142046153)
      ·
        refine ⟨55992288600903080356534615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74656384801204107142046153 55992288600903080356534615)
        ·
          refine ⟨83988432901354620534801923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55992288600903080356534615 83988432901354620534801923)
          ·
            refine ⟨125982649352031930802202885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83988432901354620534801923 125982649352031930802202885)
            ·
              refine ⟨23621746753505987025413041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125982649352031930802202885 23621746753505987025413041)
              ·
                refine ⟨17716310065129490269059781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23621746753505987025413041 17716310065129490269059781)
                ·
                  refine ⟨3321808137211779425448709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17716310065129490269059781 3321808137211779425448709)
                  ·
                    refine ⟨622839025727208642271633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3321808137211779425448709 622839025727208642271633)
                    ·
                      rfl

theorem cell23_3638924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_3638924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638924 prefixEnd_3638924 := by exact prefixLift 3638924
  have htrace : WordTrace (prefixWord ++ tailWord_3638924) baseStart_3638924 baseEnd_3638924 := by
    simpa [prefixWord, tailWord_3638924, baseEnd_3638924] using wordTrace_append hprefix tailTrace_3638924
  have hstable : (prefixWord ++ tailWord_3638924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638924).length < 2 ^ (prefixWord ++ tailWord_3638924).sum := by decide
  have hdescent : baseEnd_3638924 < baseStart_3638924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638948 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 3, 2, 2]
def baseStart_3638948 : Nat := 118140960795 + 3638948 * 2 ^ 59
def prefixEnd_3638948 : Nat := 4983230072969 + 3 ^ 40 * 3638948 * 2
def baseEnd_3638948 : Nat := 1868529400717333832914789

theorem tailTrace_3638948 : CollatzResearch.WordTrace tailWord_3638948 prefixEnd_3638948 1868529400717333832914789 := by
  unfold tailWord_3638948
  simp only [CollatzResearch.WordTrace]
  refine ⟨66361668610360176842366749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88482224813813569123155665 66361668610360176842366749)
  ·
    refine ⟨24885625728885066315887531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66361668610360176842366749 24885625728885066315887531)
    ·
      refine ⟨37328438593327599473831297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24885625728885066315887531 37328438593327599473831297)
      ·
        refine ⟨27996328944995699605373473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37328438593327599473831297 27996328944995699605373473)
        ·
          refine ⟨20997246708746774704030105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27996328944995699605373473 20997246708746774704030105)
          ·
            refine ⟨15747935031560081028022579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20997246708746774704030105 15747935031560081028022579)
            ·
              refine ⟨23621902547340121542033869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15747935031560081028022579 23621902547340121542033869)
              ·
                refine ⟨8858213455252545578262701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23621902547340121542033869 8858213455252545578262701)
                ·
                  refine ⟨3321830045719704591848513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8858213455252545578262701 3321830045719704591848513)
                  ·
                    refine ⟨2491372534289778443886385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3321830045719704591848513 2491372534289778443886385)
                    ·
                      refine ⟨1868529400717333832914789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2491372534289778443886385 1868529400717333832914789)
                      ·
                        rfl

theorem cell23_3638948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_3638948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638948 prefixEnd_3638948 := by exact prefixLift 3638948
  have htrace : WordTrace (prefixWord ++ tailWord_3638948) baseStart_3638948 baseEnd_3638948 := by
    simpa [prefixWord, tailWord_3638948, baseEnd_3638948] using wordTrace_append hprefix tailTrace_3638948
  have hstable : (prefixWord ++ tailWord_3638948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638948).length < 2 ^ (prefixWord ++ tailWord_3638948).sum := by decide
  have hdescent : baseEnd_3638948 < baseStart_3638948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3638987 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 8]
def baseStart_3638987 : Nat := 118140960795 + 3638987 * 2 ^ 59
def prefixEnd_3638987 : Nat := 4983230072969 + 3 ^ 40 * 3638987 * 2
def baseEnd_3638987 : Nat := 1868549426462859180327109

theorem tailTrace_3638987 : CollatzResearch.WordTrace tailWord_3638987 prefixEnd_3638987 1868549426462859180327109 := by
  unfold tailWord_3638987
  simp only [CollatzResearch.WordTrace]
  refine ⟨132724759667579063345403215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88483173111719375563602143 132724759667579063345403215)
  ·
    refine ⟨199087139501368595018104823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132724759667579063345403215 199087139501368595018104823)
    ·
      refine ⟨298630709252052892527157235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199087139501368595018104823 298630709252052892527157235)
      ·
        refine ⟨447946063878079338790735853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298630709252052892527157235 447946063878079338790735853)
        ·
          refine ⟨167979773954279752046525945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447946063878079338790735853 167979773954279752046525945)
          ·
            refine ⟨125984830465709814034894459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167979773954279752046525945 125984830465709814034894459)
            ·
              refine ⟨188977245698564721052341689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125984830465709814034894459 188977245698564721052341689)
              ·
                refine ⟨141732934273923540789256267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188977245698564721052341689 141732934273923540789256267)
                ·
                  refine ⟨212599401410885311183884401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141732934273923540789256267 212599401410885311183884401)
                  ·
                    refine ⟨159449551058163983387913301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212599401410885311183884401 159449551058163983387913301)
                    ·
                      refine ⟨1868549426462859180327109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 159449551058163983387913301 1868549426462859180327109)
                      ·
                        rfl

theorem cell23_3638987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_3638987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3638987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3638987 prefixEnd_3638987 := by exact prefixLift 3638987
  have htrace : WordTrace (prefixWord ++ tailWord_3638987) baseStart_3638987 baseEnd_3638987 := by
    simpa [prefixWord, tailWord_3638987, baseEnd_3638987] using wordTrace_append hprefix tailTrace_3638987
  have hstable : (prefixWord ++ tailWord_3638987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3638987).length < 2 ^ (prefixWord ++ tailWord_3638987).sum := by decide
  have hdescent : baseEnd_3638987 < baseStart_3638987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3638987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639024 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 3]
def baseStart_3639024 : Nat := 118140960795 + 3639024 * 2 ^ 59
def prefixEnd_3639024 : Nat := 4983230072969 + 3 ^ 40 * 3639024 * 2
def baseEnd_3639024 : Nat := 1868568425247075535564439

theorem tailTrace_3639024 : CollatzResearch.WordTrace tailWord_3639024 prefixEnd_3639024 1868568425247075535564439 := by
  unfold tailWord_3639024
  simp only [CollatzResearch.WordTrace]
  refine ⟨66363054584222509332250063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88484072778963345776333417 66363054584222509332250063)
  ·
    refine ⟨99544581876333763998375095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66363054584222509332250063 99544581876333763998375095)
    ·
      refine ⟨149316872814500645997562643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99544581876333763998375095 149316872814500645997562643)
      ·
        refine ⟨223975309221750968996343965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149316872814500645997562643 223975309221750968996343965)
        ·
          refine ⟨83990740958156613373628987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223975309221750968996343965 83990740958156613373628987)
          ·
            refine ⟨125986111437234920060443481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83990740958156613373628987 125986111437234920060443481)
            ·
              refine ⟨94489583577926190045332611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125986111437234920060443481 94489583577926190045332611)
              ·
                refine ⟨141734375366889285067998917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94489583577926190045332611 141734375366889285067998917)
                ·
                  refine ⟨26575195381291740950249797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141734375366889285067998917 26575195381291740950249797)
                  ·
                    refine ⟨4982849133992201428171837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26575195381291740950249797 4982849133992201428171837)
                    ·
                      refine ⟨1868568425247075535564439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4982849133992201428171837 1868568425247075535564439)
                      ·
                        rfl

theorem cell23_3639024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 3].length) (baseStart_3639024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639024 prefixEnd_3639024 := by exact prefixLift 3639024
  have htrace : WordTrace (prefixWord ++ tailWord_3639024) baseStart_3639024 baseEnd_3639024 := by
    simpa [prefixWord, tailWord_3639024, baseEnd_3639024] using wordTrace_append hprefix tailTrace_3639024
  have hstable : (prefixWord ++ tailWord_3639024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639024).length < 2 ^ (prefixWord ++ tailWord_3639024).sum := by decide
  have hdescent : baseEnd_3639024 < baseStart_3639024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639025 : List Nat := [1, 2, 2, 2, 2, 5, 1, 2, 1, 3, 2]
def baseStart_3639025 : Nat := 118140960795 + 3639025 * 2 ^ 59
def prefixEnd_3639025 : Nat := 4983230072969 + 3 ^ 40 * 3639025 * 2
def baseEnd_3639025 : Nat := 1868568938727730031651935

theorem tailTrace_3639025 : CollatzResearch.WordTrace tailWord_3639025 prefixEnd_3639025 1868568938727730031651935 := by
  unfold tailWord_3639025
  simp only [CollatzResearch.WordTrace]
  refine ⟨132726145641441395835286529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88484097094294263890191019 132726145641441395835286529)
  ·
    refine ⟨99544609231081046876464897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132726145641441395835286529 99544609231081046876464897)
    ·
      refine ⟨74658456923310785157348673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99544609231081046876464897 74658456923310785157348673)
      ·
        refine ⟨55993842692483088868011505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74658456923310785157348673 55993842692483088868011505)
        ·
          refine ⟨41995382019362316651008629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55993842692483088868011505 41995382019362316651008629)
          ·
            refine ⟨3937067064315217186032059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41995382019362316651008629 3937067064315217186032059)
            ·
              refine ⟨5905600596472825779048089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3937067064315217186032059 5905600596472825779048089)
              ·
                refine ⟨4429200447354619334286067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5905600596472825779048089 4429200447354619334286067)
                ·
                  refine ⟨6643800671031929001429101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429200447354619334286067 6643800671031929001429101)
                  ·
                    refine ⟨2491425251636973375535913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6643800671031929001429101 2491425251636973375535913)
                    ·
                      refine ⟨1868568938727730031651935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2491425251636973375535913 1868568938727730031651935)
                      ·
                        rfl

theorem cell23_3639025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_3639025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639025 prefixEnd_3639025 := by exact prefixLift 3639025
  have htrace : WordTrace (prefixWord ++ tailWord_3639025) baseStart_3639025 baseEnd_3639025 := by
    simpa [prefixWord, tailWord_3639025, baseEnd_3639025] using wordTrace_append hprefix tailTrace_3639025
  have hstable : (prefixWord ++ tailWord_3639025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639025).length < 2 ^ (prefixWord ++ tailWord_3639025).sum := by decide
  have hdescent : baseEnd_3639025 < baseStart_3639025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639034 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_3639034 : Nat := 118140960795 + 3639034 * 2 ^ 59
def prefixEnd_3639034 : Nat := 4983230072969 + 3 ^ 40 * 3639034 * 2
def baseEnd_3639034 : Nat := 1868573560053620496439393

theorem tailTrace_3639034 : CollatzResearch.WordTrace tailWord_3639034 prefixEnd_3639034 1868573560053620496439393 := by
  unfold tailWord_3639034
  simp only [CollatzResearch.WordTrace]
  refine ⟨33181618474602197593091039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88484315932272526914909437 33181618474602197593091039)
  ·
    refine ⟨49772427711903296389636559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33181618474602197593091039 49772427711903296389636559)
    ·
      refine ⟨74658641567854944584454839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49772427711903296389636559 74658641567854944584454839)
      ·
        refine ⟨111987962351782416876682259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74658641567854944584454839 111987962351782416876682259)
        ·
          refine ⟨167981943527673625315023389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111987962351782416876682259 167981943527673625315023389)
          ·
            refine ⟨62993228822877609493133771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167981943527673625315023389 62993228822877609493133771)
            ·
              refine ⟨94489843234316414239700657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62993228822877609493133771 94489843234316414239700657)
              ·
                refine ⟨70867382425737310679775493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94489843234316414239700657 70867382425737310679775493)
                ·
                  refine ⟨13287634204825745752457905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70867382425737310679775493 13287634204825745752457905)
                  ·
                    refine ⟨9965725653619309314343429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13287634204825745752457905 9965725653619309314343429)
                    ·
                      refine ⟨1868573560053620496439393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9965725653619309314343429 1868573560053620496439393)
                      ·
                        rfl

theorem cell23_3639034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_3639034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639034 prefixEnd_3639034 := by exact prefixLift 3639034
  have htrace : WordTrace (prefixWord ++ tailWord_3639034) baseStart_3639034 baseEnd_3639034 := by
    simpa [prefixWord, tailWord_3639034, baseEnd_3639034] using wordTrace_append hprefix tailTrace_3639034
  have hstable : (prefixWord ++ tailWord_3639034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639034).length < 2 ^ (prefixWord ++ tailWord_3639034).sum := by decide
  have hdescent : baseEnd_3639034 < baseStart_3639034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639042 : List Nat := [3, 4, 1, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_3639042 : Nat := 118140960795 + 3639042 * 2 ^ 59
def prefixEnd_3639042 : Nat := 4983230072969 + 3 ^ 40 * 3639042 * 2
def baseEnd_3639042 : Nat := 1868577667898856465139357

theorem tailTrace_3639042 : CollatzResearch.WordTrace tailWord_3639042 prefixEnd_3639042 1868577667898856465139357 := by
  unfold tailWord_3639042
  simp only [CollatzResearch.WordTrace]
  refine ⟨33181691420594951934663845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88484510454919871825770253 33181691420594951934663845)
  ·
    refine ⟨6221567141361553487749471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33181691420594951934663845 6221567141361553487749471)
    ·
      refine ⟨9332350712042330231624207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6221567141361553487749471 9332350712042330231624207)
      ·
        refine ⟨13998526068063495347436311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9332350712042330231624207 13998526068063495347436311)
        ·
          refine ⟨20997789102095243021154467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13998526068063495347436311 20997789102095243021154467)
          ·
            refine ⟨31496683653142864531731701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20997789102095243021154467 31496683653142864531731701)
            ·
              refine ⟨2952814092482143549849847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31496683653142864531731701 2952814092482143549849847)
              ·
                refine ⟨4429221138723215324774771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2952814092482143549849847 4429221138723215324774771)
                ·
                  refine ⟨6643831708084822987162157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429221138723215324774771 6643831708084822987162157)
                  ·
                    refine ⟨2491436890531808620185809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6643831708084822987162157 2491436890531808620185809)
                    ·
                      refine ⟨1868577667898856465139357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2491436890531808620185809 1868577667898856465139357)
                      ·
                        rfl

theorem cell23_3639042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_3639042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639042 prefixEnd_3639042 := by exact prefixLift 3639042
  have htrace : WordTrace (prefixWord ++ tailWord_3639042) baseStart_3639042 baseEnd_3639042 := by
    simpa [prefixWord, tailWord_3639042, baseEnd_3639042] using wordTrace_append hprefix tailTrace_3639042
  have hstable : (prefixWord ++ tailWord_3639042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639042).length < 2 ^ (prefixWord ++ tailWord_3639042).sum := by decide
  have hdescent : baseEnd_3639042 < baseStart_3639042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639054 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3639054 : Nat := 118140960795 + 3639054 * 2 ^ 59
def prefixEnd_3639054 : Nat := 4983230072969 + 3 ^ 40 * 3639054 * 2
def baseEnd_3639054 : Nat := 1868583829666710418189301

theorem tailTrace_3639054 : CollatzResearch.WordTrace tailWord_3639054 prefixEnd_3639054 1868583829666710418189301 := by
  unfold tailWord_3639054
  simp only [CollatzResearch.WordTrace]
  refine ⟨16590900419792041723511527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88484802238890889192061477 16590900419792041723511527)
  ·
    refine ⟨24886350629688062585267291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16590900419792041723511527 24886350629688062585267291)
    ·
      refine ⟨37329525944532093877900937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24886350629688062585267291 37329525944532093877900937)
      ·
        refine ⟨27997144458399070408425703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37329525944532093877900937 27997144458399070408425703)
        ·
          refine ⟨41995716687598605612638555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27997144458399070408425703 41995716687598605612638555)
          ·
            refine ⟨62993575031397908418957833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41995716687598605612638555 62993575031397908418957833)
            ·
              refine ⟨47245181273548431314218375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62993575031397908418957833 47245181273548431314218375)
              ·
                refine ⟨70867771910322646971327563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47245181273548431314218375 70867771910322646971327563)
                ·
                  refine ⟨106301657865483970456991345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70867771910322646971327563 106301657865483970456991345)
                  ·
                    refine ⟨79726243399112977842743509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106301657865483970456991345 79726243399112977842743509)
                    ·
                      refine ⟨1868583829666710418189301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79726243399112977842743509 1868583829666710418189301)
                      ·
                        rfl

theorem cell23_3639054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3639054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639054 prefixEnd_3639054 := by exact prefixLift 3639054
  have htrace : WordTrace (prefixWord ++ tailWord_3639054) baseStart_3639054 baseEnd_3639054 := by
    simpa [prefixWord, tailWord_3639054, baseEnd_3639054] using wordTrace_append hprefix tailTrace_3639054
  have hstable : (prefixWord ++ tailWord_3639054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639054).length < 2 ^ (prefixWord ++ tailWord_3639054).sum := by decide
  have hdescent : baseEnd_3639054 < baseStart_3639054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639058 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_3639058 : Nat := 118140960795 + 3639058 * 2 ^ 59
def prefixEnd_3639058 : Nat := 4983230072969 + 3 ^ 40 * 3639058 * 2
def baseEnd_3639058 : Nat := 1868585883589328402539283

theorem tailTrace_3639058 : CollatzResearch.WordTrace tailWord_3639058 prefixEnd_3639058 1868585883589328402539283 := by
  unfold tailWord_3639058
  simp only [CollatzResearch.WordTrace]
  refine ⟨33181837312580460617809457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88484899500214561647491885 33181837312580460617809457)
  ·
    refine ⟨24886377984435345463357093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33181837312580460617809457 24886377984435345463357093)
    ·
      refine ⟨4666195872081627274379455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24886377984435345463357093 4666195872081627274379455)
      ·
        refine ⟨6999293808122440911569183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4666195872081627274379455 6999293808122440911569183)
        ·
          refine ⟨10498940712183661367353775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6999293808122440911569183 10498940712183661367353775)
          ·
            refine ⟨15748411068275492051030663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10498940712183661367353775 15748411068275492051030663)
            ·
              refine ⟨23622616602413238076545995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15748411068275492051030663 23622616602413238076545995)
              ·
                refine ⟨35433924903619857114818993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23622616602413238076545995 35433924903619857114818993)
                ·
                  refine ⟨26575443677714892836114245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35433924903619857114818993 26575443677714892836114245)
                  ·
                    refine ⟨4982895689571542406771421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26575443677714892836114245 4982895689571542406771421)
                    ·
                      refine ⟨1868585883589328402539283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4982895689571542406771421 1868585883589328402539283)
                      ·
                        rfl

theorem cell23_3639058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_3639058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639058 prefixEnd_3639058 := by exact prefixLift 3639058
  have htrace : WordTrace (prefixWord ++ tailWord_3639058) baseStart_3639058 baseEnd_3639058 := by
    simpa [prefixWord, tailWord_3639058, baseEnd_3639058] using wordTrace_append hprefix tailTrace_3639058
  have hstable : (prefixWord ++ tailWord_3639058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639058).length < 2 ^ (prefixWord ++ tailWord_3639058).sum := by decide
  have hdescent : baseEnd_3639058 < baseStart_3639058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639071 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 3]
def baseStart_3639071 : Nat := 118140960795 + 3639071 * 2 ^ 59
def prefixEnd_3639071 : Nat := 4983230072969 + 3 ^ 40 * 3639071 * 2
def baseEnd_3639071 : Nat := 1868592558837836851676723

theorem tailTrace_3639071 : CollatzResearch.WordTrace tailWord_3639071 prefixEnd_3639071 1868592558837836851676723 := by
  unfold tailWord_3639071
  simp only [CollatzResearch.WordTrace]
  refine ⟨132727823399274745691461067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88485215599516497127640711 132727823399274745691461067)
  ·
    refine ⟨199091735098912118537191601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132727823399274745691461067 199091735098912118537191601)
    ·
      refine ⟨149318801324184088902893701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199091735098912118537191601 149318801324184088902893701)
      ·
        refine ⟨27997275248284516669292569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149318801324184088902893701 27997275248284516669292569)
        ·
          refine ⟨20997956436213387501969427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27997275248284516669292569 20997956436213387501969427)
          ·
            refine ⟨31496934654320081252954141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20997956436213387501969427 31496934654320081252954141)
            ·
              refine ⟨11811350495370030469857803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31496934654320081252954141 11811350495370030469857803)
              ·
                refine ⟨17717025743055045704786705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11811350495370030469857803 17717025743055045704786705)
                ·
                  refine ⟨13287769307291284278590029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17717025743055045704786705 13287769307291284278590029)
                  ·
                    refine ⟨4982913490234231604471261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13287769307291284278590029 4982913490234231604471261)
                    ·
                      refine ⟨1868592558837836851676723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4982913490234231604471261 1868592558837836851676723)
                      ·
                        rfl

theorem cell23_3639071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_3639071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639071 prefixEnd_3639071 := by exact prefixLift 3639071
  have htrace : WordTrace (prefixWord ++ tailWord_3639071) baseStart_3639071 baseEnd_3639071 := by
    simpa [prefixWord, tailWord_3639071, baseEnd_3639071] using wordTrace_append hprefix tailTrace_3639071
  have hstable : (prefixWord ++ tailWord_3639071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639071).length < 2 ^ (prefixWord ++ tailWord_3639071).sum := by decide
  have hdescent : baseEnd_3639071 < baseStart_3639071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639091 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 1, 7]
def baseStart_3639091 : Nat := 118140960795 + 3639091 * 2 ^ 59
def prefixEnd_3639091 : Nat := 4983230072969 + 3 ^ 40 * 3639091 * 2
def baseEnd_3639091 : Nat := 622867609483642257808877

theorem tailTrace_3639091 : CollatzResearch.WordTrace tailWord_3639091 prefixEnd_3639091 622867609483642257808877 := by
  unfold tailWord_3639091
  simp only [CollatzResearch.WordTrace]
  refine ⟨132728552859202289107189127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88485701906134859404792751 132728552859202289107189127)
  ·
    refine ⟨199092829288803433660783691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132728552859202289107189127 199092829288803433660783691)
    ·
      refine ⟨298639243933205150491175537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199092829288803433660783691 298639243933205150491175537)
      ·
        refine ⟨223979432949903862868381653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298639243933205150491175537 223979432949903862868381653)
        ·
          refine ⟨5249517959763371785977695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 223979432949903862868381653 5249517959763371785977695)
          ·
            refine ⟨7874276939645057678966543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5249517959763371785977695 7874276939645057678966543)
            ·
              refine ⟨11811415409467586518449815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7874276939645057678966543 11811415409467586518449815)
              ·
                refine ⟨17717123114201379777674723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11811415409467586518449815 17717123114201379777674723)
                ·
                  refine ⟨26575684671302069666512085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17717123114201379777674723 26575684671302069666512085)
                  ·
                    refine ⟨622867609483642257808877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26575684671302069666512085 622867609483642257808877)
                    ·
                      rfl

theorem cell23_3639091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 7].length) (baseStart_3639091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639091 prefixEnd_3639091 := by exact prefixLift 3639091
  have htrace : WordTrace (prefixWord ++ tailWord_3639091) baseStart_3639091 baseEnd_3639091 := by
    simpa [prefixWord, tailWord_3639091, baseEnd_3639091] using wordTrace_append hprefix tailTrace_3639091
  have hstable : (prefixWord ++ tailWord_3639091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639091).length < 2 ^ (prefixWord ++ tailWord_3639091).sum := by decide
  have hdescent : baseEnd_3639091 < baseStart_3639091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639111 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_3639111 : Nat := 118140960795 + 3639111 * 2 ^ 59
def prefixEnd_3639111 : Nat := 4983230072969 + 3 ^ 40 * 3639111 * 2
def baseEnd_3639111 : Nat := 1868613098064016695176539

theorem tailTrace_3639111 : CollatzResearch.WordTrace tailWord_3639111 prefixEnd_3639111 1868613098064016695176539 := by
  unfold tailWord_3639111
  simp only [CollatzResearch.WordTrace]
  refine ⟨132729282319129832522917187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88486188212753221681944791 132729282319129832522917187)
  ·
    refine ⟨199093923478694748784375781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132729282319129832522917187 199093923478694748784375781)
    ·
      refine ⟨37330110652255265397070459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199093923478694748784375781 37330110652255265397070459)
      ·
        refine ⟨55995165978382898095605689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37330110652255265397070459 55995165978382898095605689)
        ·
          refine ⟨41996374483787173571704267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55995165978382898095605689 41996374483787173571704267)
          ·
            refine ⟨62994561725680760357556401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41996374483787173571704267 62994561725680760357556401)
            ·
              refine ⟨47245921294260570268167301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62994561725680760357556401 47245921294260570268167301)
              ·
                refine ⟨8858610242673856925281369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47245921294260570268167301 8858610242673856925281369)
                ·
                  refine ⟨6643957682005392693961027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8858610242673856925281369 6643957682005392693961027)
                  ·
                    refine ⟨9965936523008089040941541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6643957682005392693961027 9965936523008089040941541)
                    ·
                      refine ⟨1868613098064016695176539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9965936523008089040941541 1868613098064016695176539)
                      ·
                        rfl

theorem cell23_3639111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_3639111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639111 prefixEnd_3639111 := by exact prefixLift 3639111
  have htrace : WordTrace (prefixWord ++ tailWord_3639111) baseStart_3639111 baseEnd_3639111 := by
    simpa [prefixWord, tailWord_3639111, baseEnd_3639111] using wordTrace_append hprefix tailTrace_3639111
  have hstable : (prefixWord ++ tailWord_3639111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639111).length < 2 ^ (prefixWord ++ tailWord_3639111).sum := by decide
  have hdescent : baseEnd_3639111 < baseStart_3639111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639218 : List Nat := [3, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4]
def baseStart_3639218 : Nat := 118140960795 + 3639218 * 2 ^ 59
def prefixEnd_3639218 : Nat := 4983230072969 + 3 ^ 40 * 3639218 * 2
def baseEnd_3639218 : Nat := 1868668040494047776538547

theorem tailTrace_3639218 : CollatzResearch.WordTrace tailWord_3639218 prefixEnd_3639218 1868668040494047776538547 := by
  unfold tailWord_3639218
  simp only [CollatzResearch.WordTrace]
  refine ⟨33183296232435547449265577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88488789953161459864708205 33183296232435547449265577)
  ·
    refine ⟨24887472174326660586949183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33183296232435547449265577 24887472174326660586949183)
    ·
      refine ⟨37331208261489990880423775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24887472174326660586949183 37331208261489990880423775)
      ·
        refine ⟨55996812392234986320635663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37331208261489990880423775 55996812392234986320635663)
        ·
          refine ⟨83995218588352479480953495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55996812392234986320635663 83995218588352479480953495)
          ·
            refine ⟨125992827882528719221430243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83995218588352479480953495 125992827882528719221430243)
            ·
              refine ⟨188989241823793078832145365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125992827882528719221430243 188989241823793078832145365)
              ·
                refine ⟨4429435355245150285128407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 188989241823793078832145365 4429435355245150285128407)
                ·
                  refine ⟨6644153032867725427692611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429435355245150285128407 6644153032867725427692611)
                  ·
                    refine ⟨9966229549301588141538917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6644153032867725427692611 9966229549301588141538917)
                    ·
                      refine ⟨1868668040494047776538547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9966229549301588141538917 1868668040494047776538547)
                      ·
                        rfl

theorem cell23_3639218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_3639218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639218 prefixEnd_3639218 := by exact prefixLift 3639218
  have htrace : WordTrace (prefixWord ++ tailWord_3639218) baseStart_3639218 baseEnd_3639218 := by
    simpa [prefixWord, tailWord_3639218, baseEnd_3639218] using wordTrace_append hprefix tailTrace_3639218
  have hstable : (prefixWord ++ tailWord_3639218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639218).length < 2 ^ (prefixWord ++ tailWord_3639218).sum := by decide
  have hdescent : baseEnd_3639218 < baseStart_3639218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639229 : List Nat := [1, 4, 1, 2, 3, 1, 4, 2, 1, 1, 3]
def baseStart_3639229 : Nat := 118140960795 + 3639229 * 2 ^ 59
def prefixEnd_3639229 : Nat := 4983230072969 + 3 ^ 40 * 3639229 * 2
def baseEnd_3639229 : Nat := 1868673688781247233500997

theorem tailTrace_3639229 : CollatzResearch.WordTrace tailWord_3639229 prefixEnd_3639229 1868673688781247233500997 := by
  unfold tailWord_3639229
  simp only [CollatzResearch.WordTrace]
  refine ⟨132733586132702338675712741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88489057421801559117141827 132733586132702338675712741)
  ·
    refine ⟨24887547399881688501696139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132733586132702338675712741 24887547399881688501696139)
    ·
      refine ⟨37331321099822532752544209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24887547399881688501696139 37331321099822532752544209)
      ·
        refine ⟨27998490824866899564408157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37331321099822532752544209 27998490824866899564408157)
        ·
          refine ⟨10499434059325087336653059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27998490824866899564408157 10499434059325087336653059)
          ·
            refine ⟨15749151088987631004979589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10499434059325087336653059 15749151088987631004979589)
            ·
              refine ⟨2952965829185180813433673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15749151088987631004979589 2952965829185180813433673)
              ·
                refine ⟨2214724371888885610075255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2952965829185180813433673 2214724371888885610075255)
                ·
                  refine ⟨3322086557833328415112883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2214724371888885610075255 3322086557833328415112883)
                  ·
                    refine ⟨4983129836749992622669325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3322086557833328415112883 4983129836749992622669325)
                    ·
                      refine ⟨1868673688781247233500997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4983129836749992622669325 1868673688781247233500997)
                      ·
                        rfl

theorem cell23_3639229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_3639229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639229 prefixEnd_3639229 := by exact prefixLift 3639229
  have htrace : WordTrace (prefixWord ++ tailWord_3639229) baseStart_3639229 baseEnd_3639229 := by
    simpa [prefixWord, tailWord_3639229, baseEnd_3639229] using wordTrace_append hprefix tailTrace_3639229
  have hstable : (prefixWord ++ tailWord_3639229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639229).length < 2 ^ (prefixWord ++ tailWord_3639229).sum := by decide
  have hdescent : baseEnd_3639229 < baseStart_3639229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639231 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 4]
def baseStart_3639231 : Nat := 118140960795 + 3639231 * 2 ^ 59
def prefixEnd_3639231 : Nat := 4983230072969 + 3 ^ 40 * 3639231 * 2
def baseEnd_3639231 : Nat := 1868674715742556225675987

theorem tailTrace_3639231 : CollatzResearch.WordTrace tailWord_3639231 prefixEnd_3639231 1868674715742556225675987 := by
  unfold tailWord_3639231
  simp only [CollatzResearch.WordTrace]
  refine ⟨132733659078695093017285547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88489106052463395344857031 132733659078695093017285547)
  ·
    refine ⟨199100488618042639525928321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132733659078695093017285547 199100488618042639525928321)
    ·
      refine ⟨149325366463531979644446241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199100488618042639525928321 149325366463531979644446241)
      ·
        refine ⟨111994024847648984733334681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149325366463531979644446241 111994024847648984733334681)
        ·
          refine ⟨83995518635736738550001011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111994024847648984733334681 83995518635736738550001011)
          ·
            refine ⟨125993277953605107825001517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83995518635736738550001011 125993277953605107825001517)
            ·
              refine ⟨47247479232601915434375569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125993277953605107825001517 47247479232601915434375569)
              ·
                refine ⟨35435609424451436575781677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47247479232601915434375569 35435609424451436575781677)
                ·
                  refine ⟨13288353534169288715918129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35435609424451436575781677 13288353534169288715918129)
                  ·
                    refine ⟨9966265150626966536938597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13288353534169288715918129 9966265150626966536938597)
                    ·
                      refine ⟨1868674715742556225675987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9966265150626966536938597 1868674715742556225675987)
                      ·
                        rfl

theorem cell23_3639231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_3639231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639231 prefixEnd_3639231 := by exact prefixLift 3639231
  have htrace : WordTrace (prefixWord ++ tailWord_3639231) baseStart_3639231 baseEnd_3639231 := by
    simpa [prefixWord, tailWord_3639231, baseEnd_3639231] using wordTrace_append hprefix tailTrace_3639231
  have hstable : (prefixWord ++ tailWord_3639231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639231).length < 2 ^ (prefixWord ++ tailWord_3639231).sum := by decide
  have hdescent : baseEnd_3639231 < baseStart_3639231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639252 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_3639252 : Nat := 118140960795 + 3639252 * 2 ^ 59
def prefixEnd_3639252 : Nat := 4983230072969 + 3 ^ 40 * 3639252 * 2
def baseEnd_3639252 : Nat := 1868685498836300643513391

theorem tailTrace_3639252 : CollatzResearch.WordTrace tailWord_3639252 prefixEnd_3639252 1868685498836300643513391 := by
  unfold tailWord_3639252
  simp only [CollatzResearch.WordTrace]
  refine ⟨66367212505809506801900005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88489616674412675735866673 66367212505809506801900005)
  ·
    refine ⟨12443852344839282525356251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66367212505809506801900005 12443852344839282525356251)
    ·
      refine ⟨18665778517258923788034377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12443852344839282525356251 18665778517258923788034377)
      ·
        refine ⟨13999333887944192841025783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18665778517258923788034377 13999333887944192841025783)
        ·
          refine ⟨20999000831916289261538675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13999333887944192841025783 20999000831916289261538675)
          ·
            refine ⟨31498501247874433892308013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20999000831916289261538675 31498501247874433892308013)
            ·
              refine ⟨11811937967952912709615505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31498501247874433892308013 11811937967952912709615505)
              ·
                refine ⟨8858953475964684532211629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11811937967952912709615505 8858953475964684532211629)
                ·
                  refine ⟨3322107553486756699579361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8858953475964684532211629 3322107553486756699579361)
                  ·
                    refine ⟨2491580665115067524684521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3322107553486756699579361 2491580665115067524684521)
                    ·
                      refine ⟨1868685498836300643513391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2491580665115067524684521 1868685498836300643513391)
                      ·
                        rfl

theorem cell23_3639252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_3639252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639252 prefixEnd_3639252 := by exact prefixLift 3639252
  have htrace : WordTrace (prefixWord ++ tailWord_3639252) baseStart_3639252 baseEnd_3639252 := by
    simpa [prefixWord, tailWord_3639252, baseEnd_3639252] using wordTrace_append hprefix tailTrace_3639252
  have hstable : (prefixWord ++ tailWord_3639252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639252).length < 2 ^ (prefixWord ++ tailWord_3639252).sum := by decide
  have hdescent : baseEnd_3639252 < baseStart_3639252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639266 : List Nat := [3, 3, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3639266 : Nat := 118140960795 + 3639266 * 2 ^ 59
def prefixEnd_3639266 : Nat := 4983230072969 + 3 ^ 40 * 3639266 * 2
def baseEnd_3639266 : Nat := 622897562521821196246109

theorem tailTrace_3639266 : CollatzResearch.WordTrace tailWord_3639266 prefixEnd_3639266 622897562521821196246109 := by
  unfold tailWord_3639266
  simp only [CollatzResearch.WordTrace]
  refine ⟨33183733908392073498702413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88489957089045529329873101 33183733908392073498702413)
  ·
    refine ⟨12443900215647027562013405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33183733908392073498702413 12443900215647027562013405)
    ·
      refine ⟨4666462580867635335755027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12443900215647027562013405 4666462580867635335755027)
      ·
        refine ⟨6999693871301453003632541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4666462580867635335755027 6999693871301453003632541)
        ·
          refine ⟨2624885201738044876362203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6999693871301453003632541 2624885201738044876362203)
          ·
            refine ⟨3937327802607067314543305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2624885201738044876362203 3937327802607067314543305)
            ·
              refine ⟨2952995851955300485907479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3937327802607067314543305 2952995851955300485907479)
              ·
                refine ⟨4429493777932950728861219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2952995851955300485907479 4429493777932950728861219)
                ·
                  refine ⟨6644240666899426093291829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429493777932950728861219 6644240666899426093291829)
                  ·
                    refine ⟨622897562521821196246109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6644240666899426093291829 622897562521821196246109)
                    ·
                      rfl

theorem cell23_3639266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3639266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639266 prefixEnd_3639266 := by exact prefixLift 3639266
  have htrace : WordTrace (prefixWord ++ tailWord_3639266) baseStart_3639266 baseEnd_3639266 := by
    simpa [prefixWord, tailWord_3639266, baseEnd_3639266] using wordTrace_append hprefix tailTrace_3639266
  have hstable : (prefixWord ++ tailWord_3639266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639266).length < 2 ^ (prefixWord ++ tailWord_3639266).sum := by decide
  have hdescent : baseEnd_3639266 < baseStart_3639266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639268 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_3639268 : Nat := 118140960795 + 3639268 * 2 ^ 59
def prefixEnd_3639268 : Nat := 4983230072969 + 3 ^ 40 * 3639268 * 2
def baseEnd_3639268 : Nat := 1868693714526772580913317

theorem tailTrace_3639268 : CollatzResearch.WordTrace tailWord_3639268 prefixEnd_3639268 1868693714526772580913317 := by
  unfold tailWord_3639268
  simp only [CollatzResearch.WordTrace]
  refine ⟨66367504289780524168191229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88490005719707365557588305 66367504289780524168191229)
  ·
    refine ⟨24887814108667696563071711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66367504289780524168191229 24887814108667696563071711)
    ·
      refine ⟨37331721163001544844607567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24887814108667696563071711 37331721163001544844607567)
      ·
        refine ⟨55997581744502317266911351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37331721163001544844607567 55997581744502317266911351)
        ·
          refine ⟨83996372616753475900367027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55997581744502317266911351 83996372616753475900367027)
          ·
            refine ⟨125994558925130213850550541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83996372616753475900367027 125994558925130213850550541)
            ·
              refine ⟨47247959596923830193956453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125994558925130213850550541 47247959596923830193956453)
              ·
                refine ⟨8858992424423218161366835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47247959596923830193956453 8858992424423218161366835)
                ·
                  refine ⟨13288488636634827242050253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8858992424423218161366835 13288488636634827242050253)
                  ·
                    refine ⟨4983183238738060215768845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13288488636634827242050253 4983183238738060215768845)
                    ·
                      refine ⟨1868693714526772580913317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4983183238738060215768845 1868693714526772580913317)
                      ·
                        rfl

theorem cell23_3639268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_3639268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639268 prefixEnd_3639268 := by exact prefixLift 3639268
  have htrace : WordTrace (prefixWord ++ tailWord_3639268) baseStart_3639268 baseEnd_3639268 := by
    simpa [prefixWord, tailWord_3639268, baseEnd_3639268] using wordTrace_append hprefix tailTrace_3639268
  have hstable : (prefixWord ++ tailWord_3639268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639268).length < 2 ^ (prefixWord ++ tailWord_3639268).sum := by decide
  have hdescent : baseEnd_3639268 < baseStart_3639268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639291 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 4]
def baseStart_3639291 : Nat := 118140960795 + 3639291 * 2 ^ 59
def prefixEnd_3639291 : Nat := 4983230072969 + 3 ^ 40 * 3639291 * 2
def baseEnd_3639291 : Nat := 1868705524581825990925711

theorem tailTrace_3639291 : CollatzResearch.WordTrace tailWord_3639291 prefixEnd_3639291 1868705524581825990925711 := by
  unfold tailWord_3639291
  simp only [CollatzResearch.WordTrace]
  refine ⟨132735847458477723264469727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88490564972318482176313151 132735847458477723264469727)
  ·
    refine ⟨199103771187716584896704591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132735847458477723264469727 199103771187716584896704591)
    ·
      refine ⟨298655656781574877345056887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199103771187716584896704591 298655656781574877345056887)
      ·
        refine ⟨447983485172362316017585331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298655656781574877345056887 447983485172362316017585331)
        ·
          refine ⟨671975227758543474026377997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447983485172362316017585331 671975227758543474026377997)
          ·
            refine ⟨251990710409453802759891749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 671975227758543474026377997 251990710409453802759891749)
            ·
              refine ⟨47248258201772588017479703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251990710409453802759891749 47248258201772588017479703)
              ·
                refine ⟨70872387302658882026219555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47248258201772588017479703 70872387302658882026219555)
                ·
                  refine ⟨106308580953988323039329333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70872387302658882026219555 106308580953988323039329333)
                  ·
                    refine ⟨9966429464436405284937125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106308580953988323039329333 9966429464436405284937125)
                    ·
                      refine ⟨1868705524581825990925711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9966429464436405284937125 1868705524581825990925711)
                      ·
                        rfl

theorem cell23_3639291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 4].length) (baseStart_3639291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639291 prefixEnd_3639291 := by exact prefixLift 3639291
  have htrace : WordTrace (prefixWord ++ tailWord_3639291) baseStart_3639291 baseEnd_3639291 := by
    simpa [prefixWord, tailWord_3639291, baseEnd_3639291] using wordTrace_append hprefix tailTrace_3639291
  have hstable : (prefixWord ++ tailWord_3639291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639291).length < 2 ^ (prefixWord ++ tailWord_3639291).sum := by decide
  have hdescent : baseEnd_3639291 < baseStart_3639291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639359 : List Nat := [1, 1, 2, 2, 3, 1, 6, 1, 2, 2, 2]
def baseStart_3639359 : Nat := 118140960795 + 3639359 * 2 ^ 59
def prefixEnd_3639359 : Nat := 4983230072969 + 3 ^ 40 * 3639359 * 2
def baseEnd_3639359 : Nat := 1868740441266331724875399

theorem tailTrace_3639359 : CollatzResearch.WordTrace tailWord_3639359 prefixEnd_3639359 1868740441266331724875399 := by
  unfold tailWord_3639359
  simp only [CollatzResearch.WordTrace]
  refine ⟨132738327622231370877945131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88492218414820913918630087 132738327622231370877945131)
  ·
    refine ⟨199107491433347056316917697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132738327622231370877945131 199107491433347056316917697)
    ·
      refine ⟨149330618575010292237688273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199107491433347056316917697 149330618575010292237688273)
      ·
        refine ⟨111997963931257719178266205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149330618575010292237688273 111997963931257719178266205)
        ·
          refine ⟨41999236474221644691849827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111997963931257719178266205 41999236474221644691849827)
          ·
            refine ⟨62998854711332467037774741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41999236474221644691849827 62998854711332467037774741)
            ·
              refine ⟨2953071314593709392395691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62998854711332467037774741 2953071314593709392395691)
              ·
                refine ⟨4429606971890564088593537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2953071314593709392395691 4429606971890564088593537)
                ·
                  refine ⟨3322205228917923066445153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4429606971890564088593537 3322205228917923066445153)
                  ·
                    refine ⟨2491653921688442299833865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3322205228917923066445153 2491653921688442299833865)
                    ·
                      refine ⟨1868740441266331724875399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2491653921688442299833865 1868740441266331724875399)
                      ·
                        rfl

theorem cell23_3639359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 2, 2, 2].length) (baseStart_3639359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639359 prefixEnd_3639359 := by exact prefixLift 3639359
  have htrace : WordTrace (prefixWord ++ tailWord_3639359) baseStart_3639359 baseEnd_3639359 := by
    simpa [prefixWord, tailWord_3639359, baseEnd_3639359] using wordTrace_append hprefix tailTrace_3639359
  have hstable : (prefixWord ++ tailWord_3639359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639359).length < 2 ^ (prefixWord ++ tailWord_3639359).sum := by decide
  have hdescent : baseEnd_3639359 < baseStart_3639359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639415 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 1, 6, 2]
def baseStart_3639415 : Nat := 118140960795 + 3639415 * 2 ^ 59
def prefixEnd_3639415 : Nat := 4983230072969 + 3 ^ 40 * 3639415 * 2
def baseEnd_3639415 : Nat := 1868769196182983505775141

theorem tailTrace_3639415 : CollatzResearch.WordTrace tailWord_3639415 prefixEnd_3639415 1868769196182983505775141 := by
  unfold tailWord_3639415
  simp only [CollatzResearch.WordTrace]
  refine ⟨132740370110028492441983699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88493580073352328294655799 132740370110028492441983699)
  ·
    refine ⟨199110555165042738662975549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132740370110028492441983699 199110555165042738662975549)
    ·
      refine ⟨74666458186891026998615831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199110555165042738662975549 74666458186891026998615831)
      ·
        refine ⟨111999687280336540497923747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74666458186891026998615831 111999687280336540497923747)
        ·
          refine ⟨167999530920504810746885621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111999687280336540497923747 167999530920504810746885621)
          ·
            refine ⟨15749956023797326007520527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167999530920504810746885621 15749956023797326007520527)
            ·
              refine ⟨23624934035695989011280791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15749956023797326007520527 23624934035695989011280791)
              ·
                refine ⟨35437401053543983516921187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23624934035695989011280791 35437401053543983516921187)
                ·
                  refine ⟨53156101580315975275381781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35437401053543983516921187 53156101580315975275381781)
                  ·
                    refine ⟨2491692261577311341033521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53156101580315975275381781 2491692261577311341033521)
                    ·
                      refine ⟨1868769196182983505775141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2491692261577311341033521 1868769196182983505775141)
                      ·
                        rfl

theorem cell23_3639415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 6, 2].length) (baseStart_3639415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639415 prefixEnd_3639415 := by exact prefixLift 3639415
  have htrace : WordTrace (prefixWord ++ tailWord_3639415) baseStart_3639415 baseEnd_3639415 := by
    simpa [prefixWord, tailWord_3639415, baseEnd_3639415] using wordTrace_append hprefix tailTrace_3639415
  have hstable : (prefixWord ++ tailWord_3639415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639415).length < 2 ^ (prefixWord ++ tailWord_3639415).sum := by decide
  have hdescent : baseEnd_3639415 < baseStart_3639415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639432 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3639432 : Nat := 118140960795 + 3639432 * 2 ^ 59
def prefixEnd_3639432 : Nat := 4983230072969 + 3 ^ 40 * 3639432 * 2
def baseEnd_3639432 : Nat := 1868777925354109939262563

theorem tailTrace_3639432 : CollatzResearch.WordTrace tailWord_3639432 prefixEnd_3639432 1868777925354109939262563 := by
  unfold tailWord_3639432
  simp only [CollatzResearch.WordTrace]
  refine ⟨66370495075483452172676275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88493993433977936230235033 66370495075483452172676275)
  ·
    refine ⟨99555742613225178259014413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66370495075483452172676275 99555742613225178259014413)
    ·
      refine ⟨37333403479959441847130405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99555742613225178259014413 37333403479959441847130405)
      ·
        refine ⟨7000013152492395346336951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37333403479959441847130405 7000013152492395346336951)
        ·
          refine ⟨10500019728738593019505427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7000013152492395346336951 10500019728738593019505427)
          ·
            refine ⟨15750029593107889529258141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10500019728738593019505427 15750029593107889529258141)
            ·
              refine ⟨5906261097415458573471803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15750029593107889529258141 5906261097415458573471803)
              ·
                refine ⟨8859391646123187860207705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5906261097415458573471803 8859391646123187860207705)
                ·
                  refine ⟨6644543734592390895155779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8859391646123187860207705 6644543734592390895155779)
                  ·
                    refine ⟨9966815601888586342733669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6644543734592390895155779 9966815601888586342733669)
                    ·
                      refine ⟨1868777925354109939262563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9966815601888586342733669 1868777925354109939262563)
                      ·
                        rfl

theorem cell23_3639432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3639432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639432 prefixEnd_3639432 := by exact prefixLift 3639432
  have htrace : WordTrace (prefixWord ++ tailWord_3639432) baseStart_3639432 baseEnd_3639432 := by
    simpa [prefixWord, tailWord_3639432, baseEnd_3639432] using wordTrace_append hprefix tailTrace_3639432
  have hstable : (prefixWord ++ tailWord_3639432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639432).length < 2 ^ (prefixWord ++ tailWord_3639432).sum := by decide
  have hdescent : baseEnd_3639432 < baseStart_3639432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639455 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 8]
def baseStart_3639455 : Nat := 118140960795 + 3639455 * 2 ^ 59
def prefixEnd_3639455 : Nat := 4983230072969 + 3 ^ 40 * 3639455 * 2
def baseEnd_3639455 : Nat := 207643303934351483252773

theorem tailTrace_3639455 : CollatzResearch.WordTrace tailWord_3639455 prefixEnd_3639455 207643303934351483252773 := by
  unfold tailWord_3639455
  simp only [CollatzResearch.WordTrace]
  refine ⟨132741829029883579273439819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88494552686589052848959879 132741829029883579273439819)
  ·
    refine ⟨199112743544825368910159729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132741829029883579273439819 199112743544825368910159729)
    ·
      refine ⟨149334557658619026682619797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199112743544825368910159729 149334557658619026682619797)
      ·
        refine ⟨7000057390247766875747803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149334557658619026682619797 7000057390247766875747803)
        ·
          refine ⟨10500086085371650313621705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7000057390247766875747803 10500086085371650313621705)
          ·
            refine ⟨7875064564028737735216279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10500086085371650313621705 7875064564028737735216279)
            ·
              refine ⟨11812596846043106602824419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7875064564028737735216279 11812596846043106602824419)
              ·
                refine ⟨17718895269064659904236629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11812596846043106602824419 17718895269064659904236629)
                ·
                  refine ⟨207643303934351483252773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17718895269064659904236629 207643303934351483252773)
                  ·
                    rfl

theorem cell23_3639455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 8].length) (baseStart_3639455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639455 prefixEnd_3639455 := by exact prefixLift 3639455
  have htrace : WordTrace (prefixWord ++ tailWord_3639455) baseStart_3639455 baseEnd_3639455 := by
    simpa [prefixWord, tailWord_3639455, baseEnd_3639455] using wordTrace_append hprefix tailTrace_3639455
  have hstable : (prefixWord ++ tailWord_3639455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639455).length < 2 ^ (prefixWord ++ tailWord_3639455).sum := by decide
  have hdescent : baseEnd_3639455 < baseStart_3639455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639482 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3]
def baseStart_3639482 : Nat := 118140960795 + 3639482 * 2 ^ 59
def prefixEnd_3639482 : Nat := 4983230072969 + 3 ^ 40 * 3639482 * 2
def baseEnd_3639482 : Nat := 1868803599386834743637333

theorem tailTrace_3639482 : CollatzResearch.WordTrace tailWord_3639482 prefixEnd_3639482 1868803599386834743637333 := by
  unfold tailWord_3639482
  simp only [CollatzResearch.WordTrace]
  refine ⟨33185703450196440721168175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88495209200523841923115133 33185703450196440721168175)
  ·
    refine ⟨49778555175294661081752263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33185703450196440721168175 49778555175294661081752263)
    ·
      refine ⟨74667832762941991622628395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49778555175294661081752263 74667832762941991622628395)
      ·
        refine ⟨112001749144412987433942593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74667832762941991622628395 112001749144412987433942593)
        ·
          refine ⟨84001311858309740575456945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112001749144412987433942593 84001311858309740575456945)
          ·
            refine ⟨63000983893732305431592709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84001311858309740575456945 63000983893732305431592709)
            ·
              refine ⟨11812684480074807268423633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63000983893732305431592709 11812684480074807268423633)
              ·
                refine ⟨8859513360056105451317725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11812684480074807268423633 8859513360056105451317725)
                ·
                  refine ⟨3322317510021039544244147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8859513360056105451317725 3322317510021039544244147)
                  ·
                    refine ⟨4983476265031559316366221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3322317510021039544244147 4983476265031559316366221)
                    ·
                      refine ⟨1868803599386834743637333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4983476265031559316366221 1868803599386834743637333)
                      ·
                        rfl

theorem cell23_3639482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_3639482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639482 prefixEnd_3639482 := by exact prefixLift 3639482
  have htrace : WordTrace (prefixWord ++ tailWord_3639482) baseStart_3639482 baseEnd_3639482 := by
    simpa [prefixWord, tailWord_3639482, baseEnd_3639482] using wordTrace_append hprefix tailTrace_3639482
  have hstable : (prefixWord ++ tailWord_3639482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639482).length < 2 ^ (prefixWord ++ tailWord_3639482).sum := by decide
  have hdescent : baseEnd_3639482 < baseStart_3639482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639502 : List Nat := [4, 1, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_3639502 : Nat := 118140960795 + 3639502 * 2 ^ 59
def prefixEnd_3639502 : Nat := 4983230072969 + 3 ^ 40 * 3639502 * 2
def baseEnd_3639502 : Nat := 622937956333308221795747

theorem tailTrace_3639502 : CollatzResearch.WordTrace tailWord_3639502 prefixEnd_3639502 622937956333308221795747 := by
  unfold tailWord_3639502
  simp only [CollatzResearch.WordTrace]
  refine ⟨16592942907589163287550095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88495695507142204200267173 16592942907589163287550095)
  ·
    refine ⟨24889414361383744931325143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16592942907589163287550095 24889414361383744931325143)
    ·
      refine ⟨37334121542075617396987715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24889414361383744931325143 37334121542075617396987715)
      ·
        refine ⟨56001182313113426095481573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37334121542075617396987715 56001182313113426095481573)
        ·
          refine ⟨10500221683708767392902795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56001182313113426095481573 10500221683708767392902795)
          ·
            refine ⟨15750332525563151089354193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10500221683708767392902795 15750332525563151089354193)
            ·
              refine ⟨11812749394172363317015645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15750332525563151089354193 11812749394172363317015645)
              ·
                refine ⟨4429781022814636243880867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11812749394172363317015645 4429781022814636243880867)
                ·
                  refine ⟨6644671534221954365821301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429781022814636243880867 6644671534221954365821301)
                  ·
                    refine ⟨622937956333308221795747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6644671534221954365821301 622937956333308221795747)
                    ·
                      rfl

theorem cell23_3639502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_3639502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639502 prefixEnd_3639502 := by exact prefixLift 3639502
  have htrace : WordTrace (prefixWord ++ tailWord_3639502) baseStart_3639502 baseEnd_3639502 := by
    simpa [prefixWord, tailWord_3639502, baseEnd_3639502] using wordTrace_append hprefix tailTrace_3639502
  have hstable : (prefixWord ++ tailWord_3639502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639502).length < 2 ^ (prefixWord ++ tailWord_3639502).sum := by decide
  have hdescent : baseEnd_3639502 < baseStart_3639502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639532 : List Nat := [2, 2, 1, 1, 2, 3, 3, 3, 2, 4]
def baseStart_3639532 : Nat := 118140960795 + 3639532 * 2 ^ 59
def prefixEnd_3639532 : Nat := 4983230072969 + 3 ^ 40 * 3639532 * 2
def baseEnd_3639532 : Nat := 622943091139853182670701

theorem tailTrace_3639532 : CollatzResearch.WordTrace tailWord_3639532 prefixEnd_3639532 622943091139853182670701 := by
  unfold tailWord_3639532
  simp only [CollatzResearch.WordTrace]
  refine ⟨66372318725302310711996425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88496424967069747615995233 66372318725302310711996425)
  ·
    refine ⟨49779239043976733033997319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66372318725302310711996425 49779239043976733033997319)
    ·
      refine ⟨74668858565965099550995979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49779239043976733033997319 74668858565965099550995979)
      ·
        refine ⟨112003287848947649326493969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74668858565965099550995979 112003287848947649326493969)
        ·
          refine ⟨84002465886710736994870477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112003287848947649326493969 84002465886710736994870477)
          ·
            refine ⟨31500924707516526373076429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84002465886710736994870477 31500924707516526373076429)
            ·
              refine ⟨11812846765318697389903661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31500924707516526373076429 11812846765318697389903661)
              ·
                refine ⟨4429817536994511521213873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11812846765318697389903661 4429817536994511521213873)
                ·
                  refine ⟨3322363152745883640910405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4429817536994511521213873 3322363152745883640910405)
                  ·
                    refine ⟨622943091139853182670701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3322363152745883640910405 622943091139853182670701)
                    ·
                      rfl

theorem cell23_3639532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_3639532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639532 prefixEnd_3639532 := by exact prefixLift 3639532
  have htrace : WordTrace (prefixWord ++ tailWord_3639532) baseStart_3639532 baseEnd_3639532 := by
    simpa [prefixWord, tailWord_3639532, baseEnd_3639532] using wordTrace_append hprefix tailTrace_3639532
  have hstable : (prefixWord ++ tailWord_3639532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639532).length < 2 ^ (prefixWord ++ tailWord_3639532).sum := by decide
  have hdescent : baseEnd_3639532 < baseStart_3639532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639535 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 6]
def baseStart_3639535 : Nat := 118140960795 + 3639535 * 2 ^ 59
def prefixEnd_3639535 : Nat := 4983230072969 + 3 ^ 40 * 3639535 * 2
def baseEnd_3639535 : Nat := 1868830813861523036274589

theorem tailTrace_3639535 : CollatzResearch.WordTrace tailWord_3639535 prefixEnd_3639535 1868830813861523036274589 := by
  unfold tailWord_3639535
  simp only [CollatzResearch.WordTrace]
  refine ⟨132744746869593752936352059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88496497913062501957568039 132744746869593752936352059)
  ·
    refine ⟨199117120304390629404528089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132744746869593752936352059 199117120304390629404528089)
    ·
      refine ⟨149337840228292972053396067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199117120304390629404528089 149337840228292972053396067)
      ·
        refine ⟨224006760342439458080094101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149337840228292972053396067 224006760342439458080094101)
        ·
          refine ⟨10500316891051849597504411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 224006760342439458080094101 10500316891051849597504411)
          ·
            refine ⟨15750475336577774396256617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10500316891051849597504411 15750475336577774396256617)
            ·
              refine ⟨11812856502433330797192463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15750475336577774396256617 11812856502433330797192463)
              ·
                refine ⟨17719284753649996195788695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11812856502433330797192463 17719284753649996195788695)
                ·
                  refine ⟨26578927130474994293683043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17719284753649996195788695 26578927130474994293683043)
                  ·
                    refine ⟨39868390695712491440524565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26578927130474994293683043 39868390695712491440524565)
                    ·
                      refine ⟨1868830813861523036274589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39868390695712491440524565 1868830813861523036274589)
                      ·
                        rfl

theorem cell23_3639535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_3639535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639535 prefixEnd_3639535 := by exact prefixLift 3639535
  have htrace : WordTrace (prefixWord ++ tailWord_3639535) baseStart_3639535 baseEnd_3639535 := by
    simpa [prefixWord, tailWord_3639535, baseEnd_3639535] using wordTrace_append hprefix tailTrace_3639535
  have hstable : (prefixWord ++ tailWord_3639535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639535).length < 2 ^ (prefixWord ++ tailWord_3639535).sum := by decide
  have hdescent : baseEnd_3639535 < baseStart_3639535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639556 : List Nat := [2, 3, 2, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_3639556 : Nat := 118140960795 + 3639556 * 2 ^ 59
def prefixEnd_3639556 : Nat := 4983230072969 + 3 ^ 40 * 3639556 * 2
def baseEnd_3639556 : Nat := 1868841596955267454111993

theorem tailTrace_3639556 : CollatzResearch.WordTrace tailWord_3639556 prefixEnd_3639556 1868841596955267454111993 := by
  unfold tailWord_3639556
  simp only [CollatzResearch.WordTrace]
  refine ⟨66372756401258836761433261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88497008535011782348577681 66372756401258836761433261)
  ·
    refine ⟨24889783650472063785537473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66372756401258836761433261 24889783650472063785537473)
    ·
      refine ⟨18667337737854047839153105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24889783650472063785537473 18667337737854047839153105)
      ·
        refine ⟨14000503303390535879364829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18667337737854047839153105 14000503303390535879364829)
        ·
          refine ⟨5250188738771450954761811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14000503303390535879364829 5250188738771450954761811)
          ·
            refine ⟨7875283108157176432142717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5250188738771450954761811 7875283108157176432142717)
            ·
              refine ⟨2953231165558941162053519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7875283108157176432142717 2953231165558941162053519)
              ·
                refine ⟨4429846748338411743080279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2953231165558941162053519 4429846748338411743080279)
                ·
                  refine ⟨6644770122507617614620419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4429846748338411743080279 6644770122507617614620419)
                  ·
                    refine ⟨9967155183761426421930629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6644770122507617614620419 9967155183761426421930629)
                    ·
                      refine ⟨1868841596955267454111993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9967155183761426421930629 1868841596955267454111993)
                      ·
                        rfl

theorem cell23_3639556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_3639556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639556 prefixEnd_3639556 := by exact prefixLift 3639556
  have htrace : WordTrace (prefixWord ++ tailWord_3639556) baseStart_3639556 baseEnd_3639556 := by
    simpa [prefixWord, tailWord_3639556, baseEnd_3639556] using wordTrace_append hprefix tailTrace_3639556
  have hstable : (prefixWord ++ tailWord_3639556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639556).length < 2 ^ (prefixWord ++ tailWord_3639556).sum := by decide
  have hdescent : baseEnd_3639556 < baseStart_3639556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639573 : List Nat := [1, 3, 2, 1, 2, 1, 6, 2, 1, 2, 2]
def baseStart_3639573 : Nat := 118140960795 + 3639573 * 2 ^ 59
def prefixEnd_3639573 : Nat := 4983230072969 + 3 ^ 40 * 3639573 * 2
def baseEnd_3639573 : Nat := 1868850326126393887599415

theorem tailTrace_3639573 : CollatzResearch.WordTrace tailWord_3639573 prefixEnd_3639573 1868850326126393887599415 := by
  unfold tailWord_3639573
  simp only [CollatzResearch.WordTrace]
  refine ⟨132746132843456085426235373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88497421895637390284156915 132746132843456085426235373)
  ·
    refine ⟨49779799816296032034838265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132746132843456085426235373 49779799816296032034838265)
    ·
      refine ⟨37334849862222024026128699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49779799816296032034838265 37334849862222024026128699)
      ·
        refine ⟨56002274793333036039193049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37334849862222024026128699 56002274793333036039193049)
        ·
          refine ⟨42001706094999777029394787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56002274793333036039193049 42001706094999777029394787)
          ·
            refine ⟨63002559142499665544092181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42001706094999777029394787 63002559142499665544092181)
            ·
              refine ⟨2953244959804671822379321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63002559142499665544092181 2953244959804671822379321)
              ·
                refine ⟨2214933719853503866784491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2953244959804671822379321 2214933719853503866784491)
                ·
                  refine ⟨3322400579780255800176737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2214933719853503866784491 3322400579780255800176737)
                  ·
                    refine ⟨2491800434835191850132553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3322400579780255800176737 2491800434835191850132553)
                    ·
                      refine ⟨1868850326126393887599415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2491800434835191850132553 1868850326126393887599415)
                      ·
                        rfl

theorem cell23_3639573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_3639573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639573 prefixEnd_3639573 := by exact prefixLift 3639573
  have htrace : WordTrace (prefixWord ++ tailWord_3639573) baseStart_3639573 baseEnd_3639573 := by
    simpa [prefixWord, tailWord_3639573, baseEnd_3639573] using wordTrace_append hprefix tailTrace_3639573
  have hstable : (prefixWord ++ tailWord_3639573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639573).length < 2 ^ (prefixWord ++ tailWord_3639573).sum := by decide
  have hdescent : baseEnd_3639573 < baseStart_3639573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639575 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 2, 7]
def baseStart_3639575 : Nat := 118140960795 + 3639575 * 2 ^ 59
def prefixEnd_3639575 : Nat := 4983230072969 + 3 ^ 40 * 3639575 * 2
def baseEnd_3639575 : Nat := 622950451029234293258135

theorem tailTrace_3639575 : CollatzResearch.WordTrace tailWord_3639575 prefixEnd_3639575 622950451029234293258135 := by
  unfold tailWord_3639575
  simp only [CollatzResearch.WordTrace]
  refine ⟨132746205789448839767808179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88497470526299226511872119 132746205789448839767808179)
  ·
    refine ⟨199119308684173259651712269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132746205789448839767808179 199119308684173259651712269)
    ·
      refine ⟨74669740756564972369392101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199119308684173259651712269 74669740756564972369392101)
      ·
        refine ⟨14000576391855932319261019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74669740756564972369392101 14000576391855932319261019)
        ·
          refine ⟨21000864587783898478891529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14000576391855932319261019 21000864587783898478891529)
          ·
            refine ⟨15750648440837923859168647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21000864587783898478891529 15750648440837923859168647)
            ·
              refine ⟨23625972661256885788752971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15750648440837923859168647 23625972661256885788752971)
              ·
                refine ⟨35438958991885328683129457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23625972661256885788752971 35438958991885328683129457)
                ·
                  refine ⟨26579219243913996512347093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35438958991885328683129457 26579219243913996512347093)
                  ·
                    refine ⟨622950451029234293258135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26579219243913996512347093 622950451029234293258135)
                    ·
                      rfl

theorem cell23_3639575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_3639575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639575 prefixEnd_3639575 := by exact prefixLift 3639575
  have htrace : WordTrace (prefixWord ++ tailWord_3639575) baseStart_3639575 baseEnd_3639575 := by
    simpa [prefixWord, tailWord_3639575, baseEnd_3639575] using wordTrace_append hprefix tailTrace_3639575
  have hstable : (prefixWord ++ tailWord_3639575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639575).length < 2 ^ (prefixWord ++ tailWord_3639575).sum := by decide
  have hdescent : baseEnd_3639575 < baseStart_3639575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639589 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 1, 3, 3]
def baseStart_3639589 : Nat := 118140960795 + 3639589 * 2 ^ 59
def prefixEnd_3639589 : Nat := 4983230072969 + 3 ^ 40 * 3639589 * 2
def baseEnd_3639589 : Nat := 1868858541816865824999341

theorem tailTrace_3639589 : CollatzResearch.WordTrace tailWord_3639589 prefixEnd_3639589 1868858541816865824999341 := by
  unfold tailWord_3639589
  simp only [CollatzResearch.WordTrace]
  refine ⟨132746716411398120158817821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88497810940932080105878547 132746716411398120158817821)
  ·
    refine ⟨49780018654274295059556683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132746716411398120158817821 49780018654274295059556683)
    ·
      refine ⟨74670027981411442589335025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49780018654274295059556683 74670027981411442589335025)
      ·
        refine ⟨56002520986058581942001269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74670027981411442589335025 56002520986058581942001269)
        ·
          refine ⟨5250236342442992057062619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56002520986058581942001269 5250236342442992057062619)
          ·
            refine ⟨7875354513664488085593929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5250236342442992057062619 7875354513664488085593929)
            ·
              refine ⟨5906515885248366064195447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7875354513664488085593929 5906515885248366064195447)
              ·
                refine ⟨8859773827872549096293171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5906515885248366064195447 8859773827872549096293171)
                ·
                  refine ⟨13289660741808823644439757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8859773827872549096293171 13289660741808823644439757)
                  ·
                    refine ⟨4983622778178308866664909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13289660741808823644439757 4983622778178308866664909)
                    ·
                      refine ⟨1868858541816865824999341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4983622778178308866664909 1868858541816865824999341)
                      ·
                        rfl

theorem cell23_3639589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_3639589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639589 prefixEnd_3639589 := by exact prefixLift 3639589
  have htrace : WordTrace (prefixWord ++ tailWord_3639589) baseStart_3639589 baseEnd_3639589 := by
    simpa [prefixWord, tailWord_3639589, baseEnd_3639589] using wordTrace_append hprefix tailTrace_3639589
  have hstable : (prefixWord ++ tailWord_3639589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639589).length < 2 ^ (prefixWord ++ tailWord_3639589).sum := by decide
  have hdescent : baseEnd_3639589 < baseStart_3639589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639605 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 1, 8]
def baseStart_3639605 : Nat := 118140960795 + 3639605 * 2 ^ 59
def prefixEnd_3639605 : Nat := 4983230072969 + 3 ^ 40 * 3639605 * 2
def baseEnd_3639605 : Nat := 622955585835779254133089

theorem tailTrace_3639605 : CollatzResearch.WordTrace tailWord_3639605 prefixEnd_3639605 622955585835779254133089 := by
  unfold tailWord_3639605
  simp only [CollatzResearch.WordTrace]
  refine ⟨132747299979340154891400269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88498199986226769927600179 132747299979340154891400269)
  ·
    refine ⟨49780237492252558084275101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132747299979340154891400269 49780237492252558084275101)
    ·
      refine ⟨18667589059594709281603163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49780237492252558084275101 18667589059594709281603163)
      ·
        refine ⟨28001383589392063922404745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18667589059594709281603163 28001383589392063922404745)
        ·
          refine ⟨21001037692044047941803559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28001383589392063922404745 21001037692044047941803559)
          ·
            refine ⟨31501556538066071912705339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21001037692044047941803559 31501556538066071912705339)
            ·
              refine ⟨47252334807099107869058009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31501556538066071912705339 47252334807099107869058009)
              ·
                refine ⟨35439251105324330901793507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47252334807099107869058009 35439251105324330901793507)
                ·
                  refine ⟨53158876657986496352690261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35439251105324330901793507 53158876657986496352690261)
                  ·
                    refine ⟨622955585835779254133089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53158876657986496352690261 622955585835779254133089)
                    ·
                      rfl

theorem cell23_3639605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_3639605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639605 prefixEnd_3639605 := by exact prefixLift 3639605
  have htrace : WordTrace (prefixWord ++ tailWord_3639605) baseStart_3639605 baseEnd_3639605 := by
    simpa [prefixWord, tailWord_3639605, baseEnd_3639605] using wordTrace_append hprefix tailTrace_3639605
  have hstable : (prefixWord ++ tailWord_3639605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639605).length < 2 ^ (prefixWord ++ tailWord_3639605).sum := by decide
  have hdescent : baseEnd_3639605 < baseStart_3639605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639615 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 5]
def baseStart_3639615 : Nat := 118140960795 + 3639615 * 2 ^ 59
def prefixEnd_3639615 : Nat := 4983230072969 + 3 ^ 40 * 3639615 * 2
def baseEnd_3639615 : Nat := 1868871892313882723274221

theorem tailTrace_3639615 : CollatzResearch.WordTrace tailWord_3639615 prefixEnd_3639615 1868871892313882723274221 := by
  unfold tailWord_3639615
  simp only [CollatzResearch.WordTrace]
  refine ⟨132747664709303926599264299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88498443139535951066176199 132747664709303926599264299)
  ·
    refine ⟨199121497063955889898896449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132747664709303926599264299 199121497063955889898896449)
    ·
      refine ⟨149341122797966917424172337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199121497063955889898896449 149341122797966917424172337)
      ·
        refine ⟨112005842098475188068129253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149341122797966917424172337 112005842098475188068129253)
        ·
          refine ⟨21001095393464097762774235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112005842098475188068129253 21001095393464097762774235)
          ·
            refine ⟨31501643090196146644161353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21001095393464097762774235 31501643090196146644161353)
            ·
              refine ⟨23626232317647109983121015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31501643090196146644161353 23626232317647109983121015)
              ·
                refine ⟨35439348476470664974681523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23626232317647109983121015 35439348476470664974681523)
                ·
                  refine ⟨53159022714705997462022285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35439348476470664974681523 53159022714705997462022285)
                  ·
                    refine ⟨19934633518014749048258357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53159022714705997462022285 19934633518014749048258357)
                    ·
                      refine ⟨1868871892313882723274221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19934633518014749048258357 1868871892313882723274221)
                      ·
                        rfl

theorem cell23_3639615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_3639615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639615 prefixEnd_3639615 := by exact prefixLift 3639615
  have htrace : WordTrace (prefixWord ++ tailWord_3639615) baseStart_3639615 baseEnd_3639615 := by
    simpa [prefixWord, tailWord_3639615, baseEnd_3639615] using wordTrace_append hprefix tailTrace_3639615
  have hstable : (prefixWord ++ tailWord_3639615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639615).length < 2 ^ (prefixWord ++ tailWord_3639615).sum := by decide
  have hdescent : baseEnd_3639615 < baseStart_3639615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639692 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 1, 2, 5]
def baseStart_3639692 : Nat := 118140960795 + 3639692 * 2 ^ 59
def prefixEnd_3639692 : Nat := 4983230072969 + 3 ^ 40 * 3639692 * 2
def baseEnd_3639692 : Nat := 1868911430324278922011367

theorem tailTrace_3639692 : CollatzResearch.WordTrace tailWord_3639692 prefixEnd_3639692 1868911430324278922011367 := by
  unfold tailWord_3639692
  simp only [CollatzResearch.WordTrace]
  refine ⟨66375236565012484374908665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88500315420016645833211553 66375236565012484374908665)
  ·
    refine ⟨49781427423759363281181499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66375236565012484374908665 49781427423759363281181499)
    ·
      refine ⟨74672141135639044921772249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49781427423759363281181499 74672141135639044921772249)
      ·
        refine ⟨56004105851729283691329187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74672141135639044921772249 56004105851729283691329187)
        ·
          refine ⟨84006158777593925536993781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56004105851729283691329187 84006158777593925536993781)
          ·
            refine ⟨7875577385399430519093167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84006158777593925536993781 7875577385399430519093167)
            ·
              refine ⟨11813366078099145778639751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7875577385399430519093167 11813366078099145778639751)
              ·
                refine ⟨17720049117148718667959627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11813366078099145778639751 17720049117148718667959627)
                ·
                  refine ⟨26580073675723078001939441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17720049117148718667959627 26580073675723078001939441)
                  ·
                    refine ⟨19935055256792308501454581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26580073675723078001939441 19935055256792308501454581)
                    ·
                      refine ⟨1868911430324278922011367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19935055256792308501454581 1868911430324278922011367)
                      ·
                        rfl

theorem cell23_3639692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_3639692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639692 prefixEnd_3639692 := by exact prefixLift 3639692
  have htrace : WordTrace (prefixWord ++ tailWord_3639692) baseStart_3639692 baseEnd_3639692 := by
    simpa [prefixWord, tailWord_3639692, baseEnd_3639692] using wordTrace_append hprefix tailTrace_3639692
  have hstable : (prefixWord ++ tailWord_3639692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639692).length < 2 ^ (prefixWord ++ tailWord_3639692).sum := by decide
  have hdescent : baseEnd_3639692 < baseStart_3639692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639719 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_3639719 : Nat := 118140960795 + 3639719 * 2 ^ 59
def prefixEnd_3639719 : Nat := 4983230072969 + 3 ^ 40 * 3639719 * 2
def baseEnd_3639719 : Nat := 1868925294301950316373743

theorem tailTrace_3639719 : CollatzResearch.WordTrace tailWord_3639719 prefixEnd_3639719 1868925294301950316373743 := by
  unfold tailWord_3639719
  simp only [CollatzResearch.WordTrace]
  refine ⟨132751457900927152361050211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88500971933951434907366807 132751457900927152361050211)
  ·
    refine ⟨199127186851390728541575317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132751457900927152361050211 199127186851390728541575317)
    ·
      refine ⟨9334086883658940400386343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 199127186851390728541575317 9334086883658940400386343)
      ·
        refine ⟨14001130325488410600579515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9334086883658940400386343 14001130325488410600579515)
        ·
          refine ⟨21001695488232615900869273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14001130325488410600579515 21001695488232615900869273)
          ·
            refine ⟨15751271616174461925651955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21001695488232615900869273 15751271616174461925651955)
            ·
              refine ⟨23626907424261692888477933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15751271616174461925651955 23626907424261692888477933)
              ·
                refine ⟨8860090284098134833179225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23626907424261692888477933 8860090284098134833179225)
                ·
                  refine ⟨6645067713073601124884419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8860090284098134833179225 6645067713073601124884419)
                  ·
                    refine ⟨9967601569610401687326629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6645067713073601124884419 9967601569610401687326629)
                    ·
                      refine ⟨1868925294301950316373743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9967601569610401687326629 1868925294301950316373743)
                      ·
                        rfl

theorem cell23_3639719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_3639719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639719 prefixEnd_3639719 := by exact prefixLift 3639719
  have htrace : WordTrace (prefixWord ++ tailWord_3639719) baseStart_3639719 baseEnd_3639719 := by
    simpa [prefixWord, tailWord_3639719, baseEnd_3639719] using wordTrace_append hprefix tailTrace_3639719
  have hstable : (prefixWord ++ tailWord_3639719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639719).length < 2 ^ (prefixWord ++ tailWord_3639719).sum := by decide
  have hdescent : baseEnd_3639719 < baseStart_3639719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639742 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 8]
def baseStart_3639742 : Nat := 118140960795 + 3639742 * 2 ^ 59
def prefixEnd_3639742 : Nat := 4983230072969 + 3 ^ 40 * 3639742 * 2
def baseEnd_3639742 : Nat := 207659678261889302931793

theorem tailTrace_3639742 : CollatzResearch.WordTrace tailWord_3639742 prefixEnd_3639742 207659678261889302931793 := by
  unfold tailWord_3639742
  simp only [CollatzResearch.WordTrace]
  refine ⟨16594037097480478411142185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88501531186562551526091653 16594037097480478411142185)
  ·
    refine ⟨12445527823110358808356639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16594037097480478411142185 12445527823110358808356639)
    ·
      refine ⟨18668291734665538212534959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12445527823110358808356639 18668291734665538212534959)
      ·
        refine ⟨28002437601998307318802439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18668291734665538212534959 28002437601998307318802439)
        ·
          refine ⟨42003656402997460978203659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28002437601998307318802439 42003656402997460978203659)
          ·
            refine ⟨63005484604496191467305489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42003656402997460978203659 63005484604496191467305489)
            ·
              refine ⟨47254113453372143600479117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63005484604496191467305489 47254113453372143600479117)
              ·
                refine ⟨17720292545014553850179669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47254113453372143600479117 17720292545014553850179669)
                ·
                  refine ⟨207659678261889302931793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17720292545014553850179669 207659678261889302931793)
                  ·
                    rfl

theorem cell23_3639742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_3639742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639742 prefixEnd_3639742 := by exact prefixLift 3639742
  have htrace : WordTrace (prefixWord ++ tailWord_3639742) baseStart_3639742 baseEnd_3639742 := by
    simpa [prefixWord, tailWord_3639742, baseEnd_3639742] using wordTrace_append hprefix tailTrace_3639742
  have hstable : (prefixWord ++ tailWord_3639742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639742).length < 2 ^ (prefixWord ++ tailWord_3639742).sum := by decide
  have hdescent : baseEnd_3639742 < baseStart_3639742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639819 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 1, 6]
def baseStart_3639819 : Nat := 118140960795 + 3639819 * 2 ^ 59
def prefixEnd_3639819 : Nat := 4983230072969 + 3 ^ 40 * 3639819 * 2
def baseEnd_3639819 : Nat := 622992214122466641707761

theorem tailTrace_3639819 : CollatzResearch.WordTrace tailWord_3639819 prefixEnd_3639819 622992214122466641707761 := by
  unfold tailWord_3639819
  simp only [CollatzResearch.WordTrace]
  refine ⟨132755105200564869439690511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88503403467043246293127007 132755105200564869439690511)
  ·
    refine ⟨199132657800847304159535767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132755105200564869439690511 199132657800847304159535767)
    ·
      refine ⟨298698986701270956239303651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199132657800847304159535767 298698986701270956239303651)
      ·
        refine ⟨448048480051906434358955477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298698986701270956239303651 448048480051906434358955477)
        ·
          refine ⟨10501136251216557055288019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 448048480051906434358955477 10501136251216557055288019)
          ·
            refine ⟨15751704376824835582932029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10501136251216557055288019 15751704376824835582932029)
            ·
              refine ⟨5906889141309313343599511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15751704376824835582932029 5906889141309313343599511)
              ·
                refine ⟨8860333711963970015399267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5906889141309313343599511 8860333711963970015399267)
                ·
                  refine ⟨13290500567945955023098901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8860333711963970015399267 13290500567945955023098901)
                  ·
                    refine ⟨622992214122466641707761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13290500567945955023098901 622992214122466641707761)
                    ·
                      rfl

theorem cell23_3639819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 6].length) (baseStart_3639819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639819 prefixEnd_3639819 := by exact prefixLift 3639819
  have htrace : WordTrace (prefixWord ++ tailWord_3639819) baseStart_3639819 baseEnd_3639819 := by
    simpa [prefixWord, tailWord_3639819, baseEnd_3639819] using wordTrace_append hprefix tailTrace_3639819
  have hstable : (prefixWord ++ tailWord_3639819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639819).length < 2 ^ (prefixWord ++ tailWord_3639819).sum := by decide
  have hdescent : baseEnd_3639819 < baseStart_3639819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639870 : List Nat := [4, 2, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_3639870 : Nat := 118140960795 + 3639870 * 2 ^ 59
def prefixEnd_3639870 : Nat := 4983230072969 + 3 ^ 40 * 3639870 * 2
def baseEnd_3639870 : Nat := 623000943293593075195183

theorem tailTrace_3639870 : CollatzResearch.WordTrace tailWord_3639870 prefixEnd_3639870 623000943293593075195183 := by
  unfold tailWord_3639870
  simp only [CollatzResearch.WordTrace]
  refine ⟨16594620665422513143724633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88504643548920070099864709 16594620665422513143724633)
  ·
    refine ⟨12445965499066884857793475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16594620665422513143724633 12445965499066884857793475)
    ·
      refine ⟨18668948248600327286690213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12445965499066884857793475 18668948248600327286690213)
      ·
        refine ⟨3500427796612561366254415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18668948248600327286690213 3500427796612561366254415)
        ·
          refine ⟨5250641694918842049381623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3500427796612561366254415 5250641694918842049381623)
          ·
            refine ⟨7875962542378263074072435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5250641694918842049381623 7875962542378263074072435)
            ·
              refine ⟨11813943813567394611108653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7875962542378263074072435 11813943813567394611108653)
              ·
                refine ⟨4430228930087772979165745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11813943813567394611108653 4430228930087772979165745)
                ·
                  refine ⟨3322671697565829734374309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4430228930087772979165745 3322671697565829734374309)
                  ·
                    refine ⟨623000943293593075195183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3322671697565829734374309 623000943293593075195183)
                    ·
                      rfl

theorem cell23_3639870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_3639870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639870 prefixEnd_3639870 := by exact prefixLift 3639870
  have htrace : WordTrace (prefixWord ++ tailWord_3639870) baseStart_3639870 baseEnd_3639870 := by
    simpa [prefixWord, tailWord_3639870, baseEnd_3639870] using wordTrace_append hprefix tailTrace_3639870
  have hstable : (prefixWord ++ tailWord_3639870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639870).length < 2 ^ (prefixWord ++ tailWord_3639870).sum := by decide
  have hdescent : baseEnd_3639870 < baseStart_3639870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639919 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 3]
def baseStart_3639919 : Nat := 118140960795 + 3639919 * 2 ^ 59
def prefixEnd_3639919 : Nat := 4983230072969 + 3 ^ 40 * 3639919 * 2
def baseEnd_3639919 : Nat := 1869027990432849533872823

theorem tailTrace_3639919 : CollatzResearch.WordTrace tailWord_3639919 prefixEnd_3639919 1869027990432849533872823 := by
  unfold tailWord_3639919
  simp only [CollatzResearch.WordTrace]
  refine ⟨132758752500202586518330811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88505835000135057678887207 132758752500202586518330811)
  ·
    refine ⟨199138128750303879777496217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132758752500202586518330811 199138128750303879777496217)
    ·
      refine ⟨149353596562727909833122163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199138128750303879777496217 149353596562727909833122163)
      ·
        refine ⟨224030394844091864749683245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149353596562727909833122163 224030394844091864749683245)
        ·
          refine ⟨84011398066534449281131217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224030394844091864749683245 84011398066534449281131217)
          ·
            refine ⟨63008548549900836960848413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84011398066534449281131217 63008548549900836960848413)
            ·
              refine ⟨23628205706212813860318155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63008548549900836960848413 23628205706212813860318155)
              ·
                refine ⟨35442308559319220790477233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23628205706212813860318155 35442308559319220790477233)
                ·
                  refine ⟨26581731419489415592857925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35442308559319220790477233 26581731419489415592857925)
                  ·
                    refine ⟨4984074641154265423660861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26581731419489415592857925 4984074641154265423660861)
                    ·
                      refine ⟨1869027990432849533872823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4984074641154265423660861 1869027990432849533872823)
                      ·
                        rfl

theorem cell23_3639919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 3].length) (baseStart_3639919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639919 prefixEnd_3639919 := by exact prefixLift 3639919
  have htrace : WordTrace (prefixWord ++ tailWord_3639919) baseStart_3639919 baseEnd_3639919 := by
    simpa [prefixWord, tailWord_3639919, baseEnd_3639919] using wordTrace_append hprefix tailTrace_3639919
  have hstable : (prefixWord ++ tailWord_3639919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639919).length < 2 ^ (prefixWord ++ tailWord_3639919).sum := by decide
  have hdescent : baseEnd_3639919 < baseStart_3639919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3639929 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 1, 4, 4]
def baseStart_3639929 : Nat := 118140960795 + 3639929 * 2 ^ 59
def prefixEnd_3639929 : Nat := 4983230072969 + 3 ^ 40 * 3639929 * 2
def baseEnd_3639929 : Nat := 1869033125239394494747777

theorem tailTrace_3639929 : CollatzResearch.WordTrace tailWord_3639929 prefixEnd_3639929 1869033125239394494747777 := by
  unfold tailWord_3639929
  simp only [CollatzResearch.WordTrace]
  refine ⟨132759117230166358226194841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88506078153444238817463227 132759117230166358226194841)
  ·
    refine ⟨99569337922624768669646131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132759117230166358226194841 99569337922624768669646131)
    ·
      refine ⟨149354006883937153004469197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99569337922624768669646131 149354006883937153004469197)
      ·
        refine ⟨56007752581476432376675949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149354006883937153004469197 56007752581476432376675949)
        ·
          refine ⟨21002907218053662141253481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56007752581476432376675949 21002907218053662141253481)
          ·
            refine ⟨15752180413540246605940111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21002907218053662141253481 15752180413540246605940111)
            ·
              refine ⟨23628270620310369908910167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15752180413540246605940111 23628270620310369908910167)
              ·
                refine ⟨35442405930465554863365251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23628270620310369908910167 35442405930465554863365251)
                ·
                  refine ⟨53163608895698332295047877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35442405930465554863365251 53163608895698332295047877)
                  ·
                    refine ⟨9968176667943437305321477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53163608895698332295047877 9968176667943437305321477)
                    ·
                      refine ⟨1869033125239394494747777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9968176667943437305321477 1869033125239394494747777)
                      ·
                        rfl

theorem cell23_3639929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_3639929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3639929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3639929 prefixEnd_3639929 := by exact prefixLift 3639929
  have htrace : WordTrace (prefixWord ++ tailWord_3639929) baseStart_3639929 baseEnd_3639929 := by
    simpa [prefixWord, tailWord_3639929, baseEnd_3639929] using wordTrace_append hprefix tailTrace_3639929
  have hstable : (prefixWord ++ tailWord_3639929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3639929).length < 2 ^ (prefixWord ++ tailWord_3639929).sum := by decide
  have hdescent : baseEnd_3639929 < baseStart_3639929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3639929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640033 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 3, 4]
def baseStart_3640033 : Nat := 118140960795 + 3640033 * 2 ^ 59
def prefixEnd_3640033 : Nat := 4983230072969 + 3 ^ 40 * 3640033 * 2
def baseEnd_3640033 : Nat := 623028842409154029282433

theorem tailTrace_3640033 : CollatzResearch.WordTrace tailWord_3640033 prefixEnd_3640033 623028842409154029282433 := by
  unfold tailWord_3640033
  simp only [CollatzResearch.WordTrace]
  refine ⟨132762910421789583987980753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88508606947859722658653835 132762910421789583987980753)
  ·
    refine ⟨99572182816342187990985565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132762910421789583987980753 99572182816342187990985565)
    ·
      refine ⟨37339568556128320496619587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99572182816342187990985565 37339568556128320496619587)
      ·
        refine ⟨56009352834192480744929381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37339568556128320496619587 56009352834192480744929381)
        ·
          refine ⟨10501753656411090139674259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56009352834192480744929381 10501753656411090139674259)
          ·
            refine ⟨15752630484616635209511389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10501753656411090139674259 15752630484616635209511389)
            ·
              refine ⟨5907236431731238203566771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15752630484616635209511389 5907236431731238203566771)
              ·
                refine ⟨8860854647596857305350157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5907236431731238203566771 8860854647596857305350157)
                ·
                  refine ⟨3322820492848821489506309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8860854647596857305350157 3322820492848821489506309)
                  ·
                    refine ⟨623028842409154029282433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3322820492848821489506309 623028842409154029282433)
                    ·
                      rfl

theorem cell23_3640033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_3640033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640033 prefixEnd_3640033 := by exact prefixLift 3640033
  have htrace : WordTrace (prefixWord ++ tailWord_3640033) baseStart_3640033 baseEnd_3640033 := by
    simpa [prefixWord, tailWord_3640033, baseEnd_3640033] using wordTrace_append hprefix tailTrace_3640033
  have hstable : (prefixWord ++ tailWord_3640033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640033).length < 2 ^ (prefixWord ++ tailWord_3640033).sum := by decide
  have hdescent : baseEnd_3640033 < baseStart_3640033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640069 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_3640069 : Nat := 118140960795 + 3640069 * 2 ^ 59
def prefixEnd_3640069 : Nat := 4983230072969 + 3 ^ 40 * 3640069 * 2
def baseEnd_3640069 : Nat := 1869105012531023946997133

theorem tailTrace_3640069 : CollatzResearch.WordTrace tailWord_3640069 prefixEnd_3640069 1869105012531023946997133 := by
  unfold tailWord_3640069
  simp only [CollatzResearch.WordTrace]
  refine ⟨132764223449659162136291261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88509482299772774757527507 132764223449659162136291261)
  ·
    refine ⟨49786583793622185801109223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132764223449659162136291261 49786583793622185801109223)
    ·
      refine ⟨74679875690433278701663835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49786583793622185801109223 74679875690433278701663835)
      ·
        refine ⟨112019813535649918052495753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74679875690433278701663835 112019813535649918052495753)
        ·
          refine ⟨84014860151737438539371815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112019813535649918052495753 84014860151737438539371815)
          ·
            refine ⟨126022290227606157809057723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84014860151737438539371815 126022290227606157809057723)
            ·
              refine ⟨189033435341409236713586585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126022290227606157809057723 189033435341409236713586585)
              ·
                refine ⟨141775076506056927535189939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189033435341409236713586585 141775076506056927535189939)
                ·
                  refine ⟨212662614759085391302784909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141775076506056927535189939 212662614759085391302784909)
                  ·
                    refine ⟨79748480534657021738544341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212662614759085391302784909 79748480534657021738544341)
                    ·
                      refine ⟨1869105012531023946997133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79748480534657021738544341 1869105012531023946997133)
                      ·
                        rfl

theorem cell23_3640069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_3640069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640069 prefixEnd_3640069 := by exact prefixLift 3640069
  have htrace : WordTrace (prefixWord ++ tailWord_3640069) baseStart_3640069 baseEnd_3640069 := by
    simpa [prefixWord, tailWord_3640069, baseEnd_3640069] using wordTrace_append hprefix tailTrace_3640069
  have hstable : (prefixWord ++ tailWord_3640069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640069).length < 2 ^ (prefixWord ++ tailWord_3640069).sum := by decide
  have hdescent : baseEnd_3640069 < baseStart_3640069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640083 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 2, 3, 2]
def baseStart_3640083 : Nat := 118140960795 + 3640083 * 2 ^ 59
def prefixEnd_3640083 : Nat := 4983230072969 + 3 ^ 40 * 3640083 * 2
def baseEnd_3640083 : Nat := 1869112201260186892222069

theorem tailTrace_3640083 : CollatzResearch.WordTrace tailWord_3640083 prefixEnd_3640083 1869112201260186892222069 := by
  unfold tailWord_3640083
  simp only [CollatzResearch.WordTrace]
  refine ⟨132764734071608442527300903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88509822714405628351533935 132764734071608442527300903)
  ·
    refine ⟨199147101107412663790951355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132764734071608442527300903 199147101107412663790951355)
    ·
      refine ⟨298720651661118995686427033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199147101107412663790951355 298720651661118995686427033)
      ·
        refine ⟨224040488745839246764820275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298720651661118995686427033 224040488745839246764820275)
        ·
          refine ⟨336060733118758870147230413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224040488745839246764820275 336060733118758870147230413)
          ·
            refine ⟨126022774919534576305211405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336060733118758870147230413 126022774919534576305211405)
            ·
              refine ⟨47258540594825466114454277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126022774919534576305211405 47258540594825466114454277)
              ·
                refine ⟨8860976361529774896460177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47258540594825466114454277 8860976361529774896460177)
                ·
                  refine ⟨6645732271147331172345133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8860976361529774896460177 6645732271147331172345133)
                  ·
                    refine ⟨2492149601680249189629425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6645732271147331172345133 2492149601680249189629425)
                    ·
                      refine ⟨1869112201260186892222069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2492149601680249189629425 1869112201260186892222069)
                      ·
                        rfl

theorem cell23_3640083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 3, 2].length) (baseStart_3640083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640083 prefixEnd_3640083 := by exact prefixLift 3640083
  have htrace : WordTrace (prefixWord ++ tailWord_3640083) baseStart_3640083 baseEnd_3640083 := by
    simpa [prefixWord, tailWord_3640083, baseEnd_3640083] using wordTrace_append hprefix tailTrace_3640083
  have hstable : (prefixWord ++ tailWord_3640083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640083).length < 2 ^ (prefixWord ++ tailWord_3640083).sum := by decide
  have hdescent : baseEnd_3640083 < baseStart_3640083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640113 : List Nat := [1, 2, 2, 3, 2, 1, 2, 4, 1, 1, 4]
def baseStart_3640113 : Nat := 118140960795 + 3640113 * 2 ^ 59
def prefixEnd_3640113 : Nat := 4983230072969 + 3 ^ 40 * 3640113 * 2
def baseEnd_3640113 : Nat := 1869127605679821774846931

theorem tailTrace_3640113 : CollatzResearch.WordTrace tailWord_3640113 prefixEnd_3640113 1869127605679821774846931 := by
  unfold tailWord_3640113
  simp only [CollatzResearch.WordTrace]
  refine ⟨132765828261499757650892993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88510552174333171767261995 132765828261499757650892993)
  ·
    refine ⟨99574371196124818238169745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132765828261499757650892993 99574371196124818238169745)
    ·
      refine ⟨74680778397093613678627309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99574371196124818238169745 74680778397093613678627309)
      ·
        refine ⟨28005291898910105129485241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74680778397093613678627309 28005291898910105129485241)
        ·
          refine ⟨21003968924182578847113931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28005291898910105129485241 21003968924182578847113931)
          ·
            refine ⟨31505953386273868270670897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21003968924182578847113931 31505953386273868270670897)
            ·
              refine ⟨23629465039705401203003173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31505953386273868270670897 23629465039705401203003173)
              ·
                refine ⟨4430524694944762725563095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23629465039705401203003173 4430524694944762725563095)
                ·
                  refine ⟨6645787042417144088344643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4430524694944762725563095 6645787042417144088344643)
                  ·
                    refine ⟨9968680563625716132516965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6645787042417144088344643 9968680563625716132516965)
                    ·
                      refine ⟨1869127605679821774846931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9968680563625716132516965 1869127605679821774846931)
                      ·
                        rfl

theorem cell23_3640113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_3640113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640113 prefixEnd_3640113 := by exact prefixLift 3640113
  have htrace : WordTrace (prefixWord ++ tailWord_3640113) baseStart_3640113 baseEnd_3640113 := by
    simpa [prefixWord, tailWord_3640113, baseEnd_3640113] using wordTrace_append hprefix tailTrace_3640113
  have hstable : (prefixWord ++ tailWord_3640113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640113).length < 2 ^ (prefixWord ++ tailWord_3640113).sum := by decide
  have hdescent : baseEnd_3640113 < baseStart_3640113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640117 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_3640117 : Nat := 118140960795 + 3640117 * 2 ^ 59
def prefixEnd_3640117 : Nat := 4983230072969 + 3 ^ 40 * 3640117 * 2
def baseEnd_3640117 : Nat := 1869129659602439759196913

theorem tailTrace_3640117 : CollatzResearch.WordTrace tailWord_3640117 prefixEnd_3640117 1869129659602439759196913 := by
  unfold tailWord_3640117
  simp only [CollatzResearch.WordTrace]
  refine ⟨132765974153485266334038605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88510649435656844222692403 132765974153485266334038605)
  ·
    refine ⟨49787240307556974875264477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132765974153485266334038605 49787240307556974875264477)
    ·
      refine ⟨18670215115333865578224179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49787240307556974875264477 18670215115333865578224179)
      ·
        refine ⟨28005322673000798367336269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18670215115333865578224179 28005322673000798367336269)
        ·
          refine ⟨10501996002375299387751101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28005322673000798367336269 10501996002375299387751101)
          ·
            refine ⟨3938248500890737270406663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10501996002375299387751101 3938248500890737270406663)
            ·
              refine ⟨5907372751336105905609995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3938248500890737270406663 5907372751336105905609995)
              ·
                refine ⟨8861059127004158858414993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5907372751336105905609995 8861059127004158858414993)
                ·
                  refine ⟨6645794345253119143811245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8861059127004158858414993 6645794345253119143811245)
                  ·
                    refine ⟨2492172879469919678929217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6645794345253119143811245 2492172879469919678929217)
                    ·
                      refine ⟨1869129659602439759196913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2492172879469919678929217 1869129659602439759196913)
                      ·
                        rfl

theorem cell23_3640117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_3640117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640117 prefixEnd_3640117 := by exact prefixLift 3640117
  have htrace : WordTrace (prefixWord ++ tailWord_3640117) baseStart_3640117 baseEnd_3640117 := by
    simpa [prefixWord, tailWord_3640117, baseEnd_3640117] using wordTrace_append hprefix tailTrace_3640117
  have hstable : (prefixWord ++ tailWord_3640117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640117).length < 2 ^ (prefixWord ++ tailWord_3640117).sum := by decide
  have hdescent : baseEnd_3640117 < baseStart_3640117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640140 : List Nat := [2, 2, 1, 3, 3, 1, 3, 2, 2, 4]
def baseStart_3640140 : Nat := 118140960795 + 3640140 * 2 ^ 59
def prefixEnd_3640140 : Nat := 4983230072969 + 3 ^ 40 * 3640140 * 2
def baseEnd_3640140 : Nat := 623047156552497723069769

theorem tailTrace_3640140 : CollatzResearch.WordTrace tailWord_3640140 prefixEnd_3640140 623047156552497723069769 := by
  unfold tailWord_3640140
  simp only [CollatzResearch.WordTrace]
  refine ⟨66383406516200970631062937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88511208688267960841417249 66383406516200970631062937)
  ·
    refine ⟨49787554887150727973297203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66383406516200970631062937 49787554887150727973297203)
    ·
      refine ⟨74681332330726091959945805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49787554887150727973297203 74681332330726091959945805)
      ·
        refine ⟨28005499624022284484979677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74681332330726091959945805 28005499624022284484979677)
        ·
          refine ⟨10502062359008356681867379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28005499624022284484979677 10502062359008356681867379)
          ·
            refine ⟨15753093538512535022801069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10502062359008356681867379 15753093538512535022801069)
            ·
              refine ⟨5907410076942200633550401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15753093538512535022801069 5907410076942200633550401)
              ·
                refine ⟨4430557557706650475162801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5907410076942200633550401 4430557557706650475162801)
                ·
                  refine ⟨3322918168279987856372101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4430557557706650475162801 3322918168279987856372101)
                  ·
                    refine ⟨623047156552497723069769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3322918168279987856372101 623047156552497723069769)
                    ·
                      rfl

theorem cell23_3640140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_3640140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640140 prefixEnd_3640140 := by exact prefixLift 3640140
  have htrace : WordTrace (prefixWord ++ tailWord_3640140) baseStart_3640140 baseEnd_3640140 := by
    simpa [prefixWord, tailWord_3640140, baseEnd_3640140] using wordTrace_append hprefix tailTrace_3640140
  have hstable : (prefixWord ++ tailWord_3640140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640140).length < 2 ^ (prefixWord ++ tailWord_3640140).sum := by decide
  have hdescent : baseEnd_3640140 < baseStart_3640140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640176 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 5]
def baseStart_3640176 : Nat := 118140960795 + 3640176 * 2 ^ 59
def prefixEnd_3640176 : Nat := 4983230072969 + 3 ^ 40 * 3640176 * 2
def baseEnd_3640176 : Nat := 1869159954961055028359141

theorem tailTrace_3640176 : CollatzResearch.WordTrace tailWord_3640176 prefixEnd_3640176 1869159954961055028359141 := by
  unfold tailWord_3640176
  simp only [CollatzResearch.WordTrace]
  refine ⟨66384063030135759705218191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88512084040181012940290921 66384063030135759705218191)
  ·
    refine ⟨99576094545203639557827287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66384063030135759705218191 99576094545203639557827287)
    ·
      refine ⟨149364141817805459336740931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99576094545203639557827287 149364141817805459336740931)
      ·
        refine ⟨224046212726708189005111397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149364141817805459336740931 224046212726708189005111397)
        ·
          refine ⟨42008664886257785438458387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224046212726708189005111397 42008664886257785438458387)
          ·
            refine ⟨63012997329386678157687581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42008664886257785438458387 63012997329386678157687581)
            ·
              refine ⟨23629873998520004309132843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63012997329386678157687581 23629873998520004309132843)
              ·
                refine ⟨35444810997780006463699265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23629873998520004309132843 35444810997780006463699265)
                ·
                  refine ⟨26583608248335004847774449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35444810997780006463699265 26583608248335004847774449)
                  ·
                    refine ⟨19937706186251253635830837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26583608248335004847774449 19937706186251253635830837)
                    ·
                      refine ⟨1869159954961055028359141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19937706186251253635830837 1869159954961055028359141)
                      ·
                        rfl

theorem cell23_3640176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_3640176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640176 prefixEnd_3640176 := by exact prefixLift 3640176
  have htrace : WordTrace (prefixWord ++ tailWord_3640176) baseStart_3640176 baseEnd_3640176 := by
    simpa [prefixWord, tailWord_3640176, baseEnd_3640176] using wordTrace_append hprefix tailTrace_3640176
  have hstable : (prefixWord ++ tailWord_3640176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640176).length < 2 ^ (prefixWord ++ tailWord_3640176).sum := by decide
  have hdescent : baseEnd_3640176 < baseStart_3640176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640181 : List Nat := [1, 3, 4, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_3640181 : Nat := 118140960795 + 3640181 * 2 ^ 59
def prefixEnd_3640181 : Nat := 4983230072969 + 3 ^ 40 * 3640181 * 2
def baseEnd_3640181 : Nat := 1869162522364327508796619

theorem tailTrace_3640181 : CollatzResearch.WordTrace tailWord_3640181 prefixEnd_3640181 1869162522364327508796619 := by
  unfold tailWord_3640181
  simp only [CollatzResearch.WordTrace]
  refine ⟨132768308425253405264368397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88512205616835603509578931 132768308425253405264368397)
  ·
    refine ⟨49788115659470026974138149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132768308425253405264368397 49788115659470026974138149)
    ·
      refine ⟨9335271686150630057650903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49788115659470026974138149 9335271686150630057650903)
      ·
        refine ⟨14002907529225945086476355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9335271686150630057650903 14002907529225945086476355)
        ·
          refine ⟨21004361293838917629714533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14002907529225945086476355 21004361293838917629714533)
          ·
            refine ⟨3938317742594797055571475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21004361293838917629714533 3938317742594797055571475)
            ·
              refine ⟨5907476613892195583357213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3938317742594797055571475 5907476613892195583357213)
              ·
                refine ⟨2215303730209573343758955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5907476613892195583357213 2215303730209573343758955)
                ·
                  refine ⟨3322955595314360015638433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215303730209573343758955 3322955595314360015638433)
                  ·
                    refine ⟨2492216696485770011728825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3322955595314360015638433 2492216696485770011728825)
                    ·
                      refine ⟨1869162522364327508796619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2492216696485770011728825 1869162522364327508796619)
                      ·
                        rfl

theorem cell23_3640181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_3640181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640181 prefixEnd_3640181 := by exact prefixLift 3640181
  have htrace : WordTrace (prefixWord ++ tailWord_3640181) baseStart_3640181 baseEnd_3640181 := by
    simpa [prefixWord, tailWord_3640181, baseEnd_3640181] using wordTrace_append hprefix tailTrace_3640181
  have hstable : (prefixWord ++ tailWord_3640181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640181).length < 2 ^ (prefixWord ++ tailWord_3640181).sum := by decide
  have hdescent : baseEnd_3640181 < baseStart_3640181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640186 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_3640186 : Nat := 118140960795 + 3640186 * 2 ^ 59
def prefixEnd_3640186 : Nat := 4983230072969 + 3 ^ 40 * 3640186 * 2
def baseEnd_3640186 : Nat := 1869165089767599989234095

theorem tailTrace_3640186 : CollatzResearch.WordTrace tailWord_3640186 prefixEnd_3640186 1869165089767599989234095 := by
  unfold tailWord_3640186
  simp only [CollatzResearch.WordTrace]
  refine ⟨33192122697558822779575103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88512327193490194078866941 33192122697558822779575103)
  ·
    refine ⟨49788184046338234169362655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33192122697558822779575103 49788184046338234169362655)
    ·
      refine ⟨74682276069507351254043983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49788184046338234169362655 74682276069507351254043983)
      ·
        refine ⟨112023414104261026881065975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74682276069507351254043983 112023414104261026881065975)
        ·
          refine ⟨168035121156391540321598963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112023414104261026881065975 168035121156391540321598963)
          ·
            refine ⟨252052681734587310482398445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168035121156391540321598963 252052681734587310482398445)
            ·
              refine ⟨94519755650470241430899417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252052681734587310482398445 94519755650470241430899417)
              ·
                refine ⟨70889816737852681073174563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94519755650470241430899417 70889816737852681073174563)
                ·
                  refine ⟨106334725106779021609761845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70889816737852681073174563 106334725106779021609761845)
                  ·
                    refine ⟨9968880478760533275915173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106334725106779021609761845 9968880478760533275915173)
                    ·
                      refine ⟨1869165089767599989234095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9968880478760533275915173 1869165089767599989234095)
                      ·
                        rfl

theorem cell23_3640186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_3640186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640186 prefixEnd_3640186 := by exact prefixLift 3640186
  have htrace : WordTrace (prefixWord ++ tailWord_3640186) baseStart_3640186 baseEnd_3640186 := by
    simpa [prefixWord, tailWord_3640186, baseEnd_3640186] using wordTrace_append hprefix tailTrace_3640186
  have hstable : (prefixWord ++ tailWord_3640186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640186).length < 2 ^ (prefixWord ++ tailWord_3640186).sum := by decide
  have hdescent : baseEnd_3640186 < baseStart_3640186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640223 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3640223 : Nat := 118140960795 + 3640223 * 2 ^ 59
def prefixEnd_3640223 : Nat := 4983230072969 + 3 ^ 40 * 3640223 * 2
def baseEnd_3640223 : Nat := 1869184088551816344471425

theorem tailTrace_3640223 : CollatzResearch.WordTrace tailWord_3640223 prefixEnd_3640223 1869184088551816344471425 := by
  unfold tailWord_3640223
  simp only [CollatzResearch.WordTrace]
  refine ⟨132769840291101246437397323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88513226860734164291598215 132769840291101246437397323)
  ·
    refine ⟨199154760436651869656095985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132769840291101246437397323 199154760436651869656095985)
    ·
      refine ⟨149366070327488902242071989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199154760436651869656095985 149366070327488902242071989)
      ·
        refine ⟨14003069093202084585194249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149366070327488902242071989 14003069093202084585194249)
        ·
          refine ⟨10502301819901563438895687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14003069093202084585194249 10502301819901563438895687)
          ·
            refine ⟨15753452729852345158343531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10502301819901563438895687 15753452729852345158343531)
            ·
              refine ⟨23630179094778517737515297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15753452729852345158343531 23630179094778517737515297)
              ·
                refine ⟨17722634321083888303136473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23630179094778517737515297 17722634321083888303136473)
                ·
                  refine ⟨13291975740812916227352355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17722634321083888303136473 13291975740812916227352355)
                  ·
                    refine ⟨19937963611219374341028533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13291975740812916227352355 19937963611219374341028533)
                    ·
                      refine ⟨1869184088551816344471425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19937963611219374341028533 1869184088551816344471425)
                      ·
                        rfl

theorem cell23_3640223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3640223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640223 prefixEnd_3640223 := by exact prefixLift 3640223
  have htrace : WordTrace (prefixWord ++ tailWord_3640223) baseStart_3640223 baseEnd_3640223 := by
    simpa [prefixWord, tailWord_3640223, baseEnd_3640223] using wordTrace_append hprefix tailTrace_3640223
  have hstable : (prefixWord ++ tailWord_3640223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640223).length < 2 ^ (prefixWord ++ tailWord_3640223).sum := by decide
  have hdescent : baseEnd_3640223 < baseStart_3640223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640254 : List Nat := [4, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_3640254 : Nat := 118140960795 + 3640254 * 2 ^ 59
def prefixEnd_3640254 : Nat := 4983230072969 + 3 ^ 40 * 3640254 * 2
def baseEnd_3640254 : Nat := 1869200006452105723183783

theorem tailTrace_3640254 : CollatzResearch.WordTrace tailWord_3640254 prefixEnd_3640254 1869200006452105723183783 := by
  unfold tailWord_3640254
  simp only [CollatzResearch.WordTrace]
  refine ⟨16596371369248617341471977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88513980635992625821183877 16596371369248617341471977)
  ·
    refine ⟨12447278526936463006103983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16596371369248617341471977 12447278526936463006103983)
    ·
      refine ⟨18670917790404694509155975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12447278526936463006103983 18670917790404694509155975)
      ·
        refine ⟨28006376685607041763733963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18670917790404694509155975 28006376685607041763733963)
        ·
          refine ⟨42009565028410562645600945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28006376685607041763733963 42009565028410562645600945)
          ·
            refine ⟨31507173771307921984200709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42009565028410562645600945 31507173771307921984200709)
            ·
              refine ⟨5907595082120235372037633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31507173771307921984200709 5907595082120235372037633)
              ·
                refine ⟨4430696311590176529028225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5907595082120235372037633 4430696311590176529028225)
                ·
                  refine ⟨3323022233692632396771169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4430696311590176529028225 3323022233692632396771169)
                  ·
                    refine ⟨2492266675269474297578377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3323022233692632396771169 2492266675269474297578377)
                    ·
                      refine ⟨1869200006452105723183783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2492266675269474297578377 1869200006452105723183783)
                      ·
                        rfl

theorem cell23_3640254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_3640254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640254 prefixEnd_3640254 := by exact prefixLift 3640254
  have htrace : WordTrace (prefixWord ++ tailWord_3640254) baseStart_3640254 baseEnd_3640254 := by
    simpa [prefixWord, tailWord_3640254, baseEnd_3640254] using wordTrace_append hprefix tailTrace_3640254
  have hstable : (prefixWord ++ tailWord_3640254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640254).length < 2 ^ (prefixWord ++ tailWord_3640254).sum := by decide
  have hdescent : baseEnd_3640254 < baseStart_3640254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640270 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_3640270 : Nat := 118140960795 + 3640270 * 2 ^ 59
def prefixEnd_3640270 : Nat := 4983230072969 + 3 ^ 40 * 3640270 * 2
def baseEnd_3640270 : Nat := 1869208222142577660583709

theorem tailTrace_3640270 : CollatzResearch.WordTrace tailWord_3640270 prefixEnd_3640270 1869208222142577660583709 := by
  unfold tailWord_3640270
  simp only [CollatzResearch.WordTrace]
  refine ⟨16596444315241371683044783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88514369681287315642905509 16596444315241371683044783)
  ·
    refine ⟨24894666472862057524567175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16596444315241371683044783 24894666472862057524567175)
    ·
      refine ⟨37341999709293086286850763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24894666472862057524567175 37341999709293086286850763)
      ·
        refine ⟨56012999563939629430276145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37341999709293086286850763 56012999563939629430276145)
        ·
          refine ⟨42009749672954722072707109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56012999563939629430276145 42009749672954722072707109)
          ·
            refine ⟨7876828063679010388632583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42009749672954722072707109 7876828063679010388632583)
            ·
              refine ⟨11815242095518515582948875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7876828063679010388632583 11815242095518515582948875)
              ·
                refine ⟨17722863143277773374423313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11815242095518515582948875 17722863143277773374423313)
                ·
                  refine ⟨13292147357458330030817485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17722863143277773374423313 13292147357458330030817485)
                  ·
                    refine ⟨4984555259046873761556557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13292147357458330030817485 4984555259046873761556557)
                    ·
                      refine ⟨1869208222142577660583709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4984555259046873761556557 1869208222142577660583709)
                      ·
                        rfl

theorem cell23_3640270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_3640270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640270 prefixEnd_3640270 := by exact prefixLift 3640270
  have htrace : WordTrace (prefixWord ++ tailWord_3640270) baseStart_3640270 baseEnd_3640270 := by
    simpa [prefixWord, tailWord_3640270, baseEnd_3640270] using wordTrace_append hprefix tailTrace_3640270
  have hstable : (prefixWord ++ tailWord_3640270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640270).length < 2 ^ (prefixWord ++ tailWord_3640270).sum := by decide
  have hdescent : baseEnd_3640270 < baseStart_3640270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640330 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_3640330 : Nat := 118140960795 + 3640330 * 2 ^ 59
def prefixEnd_3640330 : Nat := 4983230072969 + 3 ^ 40 * 3640330 * 2
def baseEnd_3640330 : Nat := 1869239030981847425833433

theorem tailTrace_3640330 : CollatzResearch.WordTrace tailWord_3640330 prefixEnd_3640330 1869239030981847425833433 := by
  unfold tailWord_3640330
  simp only [CollatzResearch.WordTrace]
  refine ⟨33193435725428400927885611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88515828601142402474361629 33193435725428400927885611)
  ·
    refine ⟨49790153588142601391828417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33193435725428400927885611 49790153588142601391828417)
    ·
      refine ⟨37342615191106951043871313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49790153588142601391828417 37342615191106951043871313)
      ·
        refine ⟨28006961393330213282903485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37342615191106951043871313 28006961393330213282903485)
        ·
          refine ⟨10502610522498829981088807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28006961393330213282903485 10502610522498829981088807)
          ·
            refine ⟨15753915783748244971633211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10502610522498829981088807 15753915783748244971633211)
            ·
              refine ⟨23630873675622367457449817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15753915783748244971633211 23630873675622367457449817)
              ·
                refine ⟨17723155256716775593087363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23630873675622367457449817 17723155256716775593087363)
                ·
                  refine ⟨26584732885075163389631045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17723155256716775593087363 26584732885075163389631045)
                  ·
                    refine ⟨4984637415951593135555821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26584732885075163389631045 4984637415951593135555821)
                    ·
                      refine ⟨1869239030981847425833433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4984637415951593135555821 1869239030981847425833433)
                      ·
                        rfl

theorem cell23_3640330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_3640330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640330 prefixEnd_3640330 := by exact prefixLift 3640330
  have htrace : WordTrace (prefixWord ++ tailWord_3640330) baseStart_3640330 baseEnd_3640330 := by
    simpa [prefixWord, tailWord_3640330, baseEnd_3640330] using wordTrace_append hprefix tailTrace_3640330
  have hstable : (prefixWord ++ tailWord_3640330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640330).length < 2 ^ (prefixWord ++ tailWord_3640330).sum := by decide
  have hdescent : baseEnd_3640330 < baseStart_3640330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640354 : List Nat := [3, 3, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_3640354 : Nat := 118140960795 + 3640354 * 2 ^ 59
def prefixEnd_3640354 : Nat := 4983230072969 + 3 ^ 40 * 3640354 * 2
def baseEnd_3640354 : Nat := 623083784839185110644441

theorem tailTrace_3640354 : CollatzResearch.WordTrace tailWord_3640354 prefixEnd_3640354 623083784839185110644441 := by
  unfold tailWord_3640354
  simp only [CollatzResearch.WordTrace]
  refine ⟨33193654563406663952604029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88516412169084437206944077 33193654563406663952604029)
  ·
    refine ⟨12447620461277498982226511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33193654563406663952604029 12447620461277498982226511)
    ·
      refine ⟨18671430691916248473339767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12447620461277498982226511 18671430691916248473339767)
      ·
        refine ⟨28007146037874372710009651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18671430691916248473339767 28007146037874372710009651)
        ·
          refine ⟨42010719056811559065014477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28007146037874372710009651 42010719056811559065014477)
          ·
            refine ⟨15754019646304334649380429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42010719056811559065014477 15754019646304334649380429)
            ·
              refine ⟨5907757367364125493517661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15754019646304334649380429 5907757367364125493517661)
              ·
                refine ⟨2215409012761547060069123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5907757367364125493517661 2215409012761547060069123)
                ·
                  refine ⟨3323113519142320590103685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215409012761547060069123 3323113519142320590103685)
                  ·
                    refine ⟨623083784839185110644441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3323113519142320590103685 623083784839185110644441)
                    ·
                      rfl

theorem cell23_3640354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_3640354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640354 prefixEnd_3640354 := by exact prefixLift 3640354
  have htrace : WordTrace (prefixWord ++ tailWord_3640354) baseStart_3640354 baseEnd_3640354 := by
    simpa [prefixWord, tailWord_3640354, baseEnd_3640354] using wordTrace_append hprefix tailTrace_3640354
  have hstable : (prefixWord ++ tailWord_3640354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640354).length < 2 ^ (prefixWord ++ tailWord_3640354).sum := by decide
  have hdescent : baseEnd_3640354 < baseStart_3640354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640373 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_3640373 : Nat := 118140960795 + 3640373 * 2 ^ 59
def prefixEnd_3640373 : Nat := 4983230072969 + 3 ^ 40 * 3640373 * 2
def baseEnd_3640373 : Nat := 1869261110649990757595735

theorem tailTrace_3640373 : CollatzResearch.WordTrace tailWord_3640373 prefixEnd_3640373 1869261110649990757595735 := by
  unfold tailWord_3640373
  simp only [CollatzResearch.WordTrace]
  refine ⟨132775311240557822055357773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88516874160371881370238515 132775311240557822055357773)
  ·
    refine ⟨49790741715209183270759165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132775311240557822055357773 49790741715209183270759165)
    ·
      refine ⟨18671528143203443726534687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49790741715209183270759165 18671528143203443726534687)
      ·
        refine ⟨28007292214805165589802031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18671528143203443726534687 28007292214805165589802031)
        ·
          refine ⟨42010938322207748384703047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28007292214805165589802031 42010938322207748384703047)
          ·
            refine ⟨63016407483311622577054571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42010938322207748384703047 63016407483311622577054571)
            ·
              refine ⟨94524611224967433865581857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63016407483311622577054571 94524611224967433865581857)
              ·
                refine ⟨70893458418725575399186393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94524611224967433865581857 70893458418725575399186393)
                ·
                  refine ⟨53170093814044181549389795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70893458418725575399186393 53170093814044181549389795)
                  ·
                    refine ⟨79755140721066272324084693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53170093814044181549389795 79755140721066272324084693)
                    ·
                      refine ⟨1869261110649990757595735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79755140721066272324084693 1869261110649990757595735)
                      ·
                        rfl

theorem cell23_3640373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_3640373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640373 prefixEnd_3640373 := by exact prefixLift 3640373
  have htrace : WordTrace (prefixWord ++ tailWord_3640373) baseStart_3640373 baseEnd_3640373 := by
    simpa [prefixWord, tailWord_3640373, baseEnd_3640373] using wordTrace_append hprefix tailTrace_3640373
  have hstable : (prefixWord ++ tailWord_3640373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640373).length < 2 ^ (prefixWord ++ tailWord_3640373).sum := by decide
  have hdescent : baseEnd_3640373 < baseStart_3640373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640383 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 4]
def baseStart_3640383 : Nat := 118140960795 + 3640383 * 2 ^ 59
def prefixEnd_3640383 : Nat := 4983230072969 + 3 ^ 40 * 3640383 * 2
def baseEnd_3640383 : Nat := 1869266245456535718470689

theorem tailTrace_3640383 : CollatzResearch.WordTrace tailWord_3640383 prefixEnd_3640383 1869266245456535718470689 := by
  unfold tailWord_3640383
  simp only [CollatzResearch.WordTrace]
  refine ⟨132775675970521593763221803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88517117313681062508814535 132775675970521593763221803)
  ·
    refine ⟨199163513955782390644832705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132775675970521593763221803 199163513955782390644832705)
    ·
      refine ⟨149372635466836792983624529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199163513955782390644832705 149372635466836792983624529)
      ·
        refine ⟨112029476600127594737718397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149372635466836792983624529 112029476600127594737718397)
        ·
          refine ⟨42011053725047848026644399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112029476600127594737718397 42011053725047848026644399)
          ·
            refine ⟨63016580587571772039966599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42011053725047848026644399 63016580587571772039966599)
            ·
              refine ⟨94524870881357658059949899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63016580587571772039966599 94524870881357658059949899)
              ·
                refine ⟨141787306322036487089924849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94524870881357658059949899 141787306322036487089924849)
                ·
                  refine ⟨106340479741527365317443637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141787306322036487089924849 106340479741527365317443637)
                  ·
                    refine ⟨9969419975768190498510341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106340479741527365317443637 9969419975768190498510341)
                    ·
                      refine ⟨1869266245456535718470689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9969419975768190498510341 1869266245456535718470689)
                      ·
                        rfl

theorem cell23_3640383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_3640383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640383 prefixEnd_3640383 := by exact prefixLift 3640383
  have htrace : WordTrace (prefixWord ++ tailWord_3640383) baseStart_3640383 baseEnd_3640383 := by
    simpa [prefixWord, tailWord_3640383, baseEnd_3640383] using wordTrace_append hprefix tailTrace_3640383
  have hstable : (prefixWord ++ tailWord_3640383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640383).length < 2 ^ (prefixWord ++ tailWord_3640383).sum := by decide
  have hdescent : baseEnd_3640383 < baseStart_3640383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640397 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_3640397 : Nat := 118140960795 + 3640397 * 2 ^ 59
def prefixEnd_3640397 : Nat := 4983230072969 + 3 ^ 40 * 3640397 * 2
def baseEnd_3640397 : Nat := 623091144728566221231875

theorem tailTrace_3640397 : CollatzResearch.WordTrace tailWord_3640397 prefixEnd_3640397 623091144728566221231875 := by
  unfold tailWord_3640397
  simp only [CollatzResearch.WordTrace]
  refine ⟨132776186592470874154231445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88517457728313916102820963 132776186592470874154231445)
  ·
    refine ⟨6223883746522072225979599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132776186592470874154231445 6223883746522072225979599)
    ·
      refine ⟨9335825619783108338969399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6223883746522072225979599 9335825619783108338969399)
      ·
        refine ⟨14003738429674662508454099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9335825619783108338969399 14003738429674662508454099)
        ·
          refine ⟨21005607644511993762681149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14003738429674662508454099 21005607644511993762681149)
          ·
            refine ⟨7877102866691997661005431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21005607644511993762681149 7877102866691997661005431)
            ·
              refine ⟨11815654300037996491508147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7877102866691997661005431 11815654300037996491508147)
              ·
                refine ⟨17723481450056994737262221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11815654300037996491508147 17723481450056994737262221)
                ·
                  refine ⟨6646305543771373026473333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17723481450056994737262221 6646305543771373026473333)
                  ·
                    refine ⟨623091144728566221231875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6646305543771373026473333 623091144728566221231875)
                    ·
                      rfl

theorem cell23_3640397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_3640397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640397 prefixEnd_3640397 := by exact prefixLift 3640397
  have htrace : WordTrace (prefixWord ++ tailWord_3640397) baseStart_3640397 baseEnd_3640397 := by
    simpa [prefixWord, tailWord_3640397, baseEnd_3640397] using wordTrace_append hprefix tailTrace_3640397
  have hstable : (prefixWord ++ tailWord_3640397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640397).length < 2 ^ (prefixWord ++ tailWord_3640397).sum := by decide
  have hdescent : baseEnd_3640397 < baseStart_3640397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640400 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 2, 6, 2]
def baseStart_3640400 : Nat := 118140960795 + 3640400 * 2 ^ 59
def prefixEnd_3640400 : Nat := 4983230072969 + 3 ^ 40 * 3640400 * 2
def baseEnd_3640400 : Nat := 1869274974627662151958111

theorem tailTrace_3640400 : CollatzResearch.WordTrace tailWord_3640400 prefixEnd_3640400 1869274974627662151958111 := by
  unfold tailWord_3640400
  simp only [CollatzResearch.WordTrace]
  refine ⟨66388148005730002833295327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88517530674306670444393769 66388148005730002833295327)
  ·
    refine ⟨99582222008595004249942991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66388148005730002833295327 99582222008595004249942991)
    ·
      refine ⟨149373333012892506374914487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99582222008595004249942991 149373333012892506374914487)
      ·
        refine ⟨224059999519338759562371731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149373333012892506374914487 224059999519338759562371731)
        ·
          refine ⟨336089999279008139343557597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224059999519338759562371731 336089999279008139343557597)
          ·
            refine ⟨126033749729628052253834099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336089999279008139343557597 126033749729628052253834099)
            ·
              refine ⟨189050624594442078380751149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126033749729628052253834099 189050624594442078380751149)
              ·
                refine ⟨70893984222915779392781681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189050624594442078380751149 70893984222915779392781681)
                ·
                  refine ⟨53170488167186834544586261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70893984222915779392781681 53170488167186834544586261)
                  ·
                    refine ⟨2492366632836882869277481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53170488167186834544586261 2492366632836882869277481)
                    ·
                      refine ⟨1869274974627662151958111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2492366632836882869277481 1869274974627662151958111)
                      ·
                        rfl

theorem cell23_3640400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 2, 6, 2].length) (baseStart_3640400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640400 prefixEnd_3640400 := by exact prefixLift 3640400
  have htrace : WordTrace (prefixWord ++ tailWord_3640400) baseStart_3640400 baseEnd_3640400 := by
    simpa [prefixWord, tailWord_3640400, baseEnd_3640400] using wordTrace_append hprefix tailTrace_3640400
  have hstable : (prefixWord ++ tailWord_3640400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640400).length < 2 ^ (prefixWord ++ tailWord_3640400).sum := by decide
  have hdescent : baseEnd_3640400 < baseStart_3640400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640403 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 5]
def baseStart_3640403 : Nat := 118140960795 + 3640403 * 2 ^ 59
def prefixEnd_3640403 : Nat := 4983230072969 + 3 ^ 40 * 3640403 * 2
def baseEnd_3640403 : Nat := 1869276515069625640220597

theorem tailTrace_3640403 : CollatzResearch.WordTrace tailWord_3640403 prefixEnd_3640403 1869276515069625640220597 := by
  unfold tailWord_3640403
  simp only [CollatzResearch.WordTrace]
  refine ⟨132776405430449137178949863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88517603620299424785966575 132776405430449137178949863)
  ·
    refine ⟨199164608145673705768424795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132776405430449137178949863 199164608145673705768424795)
    ·
      refine ⟨298746912218510558652637193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199164608145673705768424795 298746912218510558652637193)
      ·
        refine ⟨224060184163882918989477895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298746912218510558652637193 224060184163882918989477895)
        ·
          refine ⟨336090276245824378484216843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224060184163882918989477895 336090276245824378484216843)
          ·
            refine ⟨504135414368736567726325265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336090276245824378484216843 504135414368736567726325265)
            ·
              refine ⟨378101560776552425794743949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504135414368736567726325265 378101560776552425794743949)
              ·
                refine ⟨141788085291207159673028981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378101560776552425794743949 141788085291207159673028981)
                ·
                  refine ⟨13292632996050671219346467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141788085291207159673028981 13292632996050671219346467)
                  ·
                    refine ⟨19938949494076006829019701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13292632996050671219346467 19938949494076006829019701)
                    ·
                      refine ⟨1869276515069625640220597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19938949494076006829019701 1869276515069625640220597)
                      ·
                        rfl

theorem cell23_3640403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_3640403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640403 prefixEnd_3640403 := by exact prefixLift 3640403
  have htrace : WordTrace (prefixWord ++ tailWord_3640403) baseStart_3640403 baseEnd_3640403 := by
    simpa [prefixWord, tailWord_3640403, baseEnd_3640403] using wordTrace_append hprefix tailTrace_3640403
  have hstable : (prefixWord ++ tailWord_3640403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640403).length < 2 ^ (prefixWord ++ tailWord_3640403).sum := by decide
  have hdescent : baseEnd_3640403 < baseStart_3640403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640410 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 4, 4]
def baseStart_3640410 : Nat := 118140960795 + 3640410 * 2 ^ 59
def prefixEnd_3640410 : Nat := 4983230072969 + 3 ^ 40 * 3640410 * 2
def baseEnd_3640410 : Nat := 623093369811402370944355

theorem tailTrace_3640410 : CollatzResearch.WordTrace tailWord_3640410 prefixEnd_3640410 623093369811402370944355 := by
  unfold tailWord_3640410
  simp only [CollatzResearch.WordTrace]
  refine ⟨33194165185355944343613671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88517773827615851582969789 33194165185355944343613671)
  ·
    refine ⟨49791247778033916515420507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33194165185355944343613671 49791247778033916515420507)
    ·
      refine ⟨74686871667050874773130761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49791247778033916515420507 74686871667050874773130761)
      ·
        refine ⟨56015153750288156079848071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74686871667050874773130761 56015153750288156079848071)
        ·
          refine ⟨84022730625432234119772107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56015153750288156079848071 84022730625432234119772107)
          ·
            refine ⟨126034095938148351179658161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84022730625432234119772107 126034095938148351179658161)
            ·
              refine ⟨94525571953611263384743621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126034095938148351179658161 94525571953611263384743621)
              ·
                refine ⟨17723544741302111884639429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94525571953611263384743621 17723544741302111884639429)
                ·
                  refine ⟨3323164638994145978369893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17723544741302111884639429 3323164638994145978369893)
                  ·
                    refine ⟨623093369811402370944355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3323164638994145978369893 623093369811402370944355)
                    ·
                      rfl

theorem cell23_3640410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_3640410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640410 prefixEnd_3640410 := by exact prefixLift 3640410
  have htrace : WordTrace (prefixWord ++ tailWord_3640410) baseStart_3640410 baseEnd_3640410 := by
    simpa [prefixWord, tailWord_3640410, baseEnd_3640410] using wordTrace_append hprefix tailTrace_3640410
  have hstable : (prefixWord ++ tailWord_3640410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640410).length < 2 ^ (prefixWord ++ tailWord_3640410).sum := by decide
  have hdescent : baseEnd_3640410 < baseStart_3640410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640423 : List Nat := [1, 1, 5, 1, 1, 14]
def baseStart_3640423 : Nat := 118140960795 + 3640423 * 2 ^ 59
def prefixEnd_3640423 : Nat := 4983230072969 + 3 ^ 40 * 3640423 * 2
def baseEnd_3640423 : Nat := 7692538208570845934035

theorem tailTrace_3640423 : CollatzResearch.WordTrace tailWord_3640423 prefixEnd_3640423 7692538208570845934035 := by
  unfold tailWord_3640423
  simp only [CollatzResearch.WordTrace]
  refine ⟨132777134890376680594677923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88518089926917787063118615 132777134890376680594677923)
  ·
    refine ⟨199165702335565020892016885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132777134890376680594677923 199165702335565020892016885)
    ·
      refine ⟨18671784593959220708626583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199165702335565020892016885 18671784593959220708626583)
      ·
        refine ⟨28007676890938831062939875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18671784593959220708626583 28007676890938831062939875)
        ·
          refine ⟨42011515336408246594409813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28007676890938831062939875 42011515336408246594409813)
          ·
            refine ⟨7692538208570845934035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 42011515336408246594409813 7692538208570845934035)
            ·
              rfl

theorem cell23_3640423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 14].length) (baseStart_3640423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640423 prefixEnd_3640423 := by exact prefixLift 3640423
  have htrace : WordTrace (prefixWord ++ tailWord_3640423) baseStart_3640423 baseEnd_3640423 := by
    simpa [prefixWord, tailWord_3640423, baseEnd_3640423] using wordTrace_append hprefix tailTrace_3640423
  have hstable : (prefixWord ++ tailWord_3640423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640423).length < 2 ^ (prefixWord ++ tailWord_3640423).sum := by decide
  have hdescent : baseEnd_3640423 < baseStart_3640423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640433 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_3640433 : Nat := 118140960795 + 3640433 * 2 ^ 59
def prefixEnd_3640433 : Nat := 4983230072969 + 3 ^ 40 * 3640433 * 2
def baseEnd_3640433 : Nat := 1869291919489260522845459

theorem tailTrace_3640433 : CollatzResearch.WordTrace tailWord_3640433 prefixEnd_3640433 1869291919489260522845459 := by
  unfold tailWord_3640433
  simp only [CollatzResearch.WordTrace]
  refine ⟨132777499620340452302541953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88518333080226968201694635 132777499620340452302541953)
  ·
    refine ⟨99583124715255339226906465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132777499620340452302541953 99583124715255339226906465)
    ·
      refine ⟨74687343536441504420179849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99583124715255339226906465 74687343536441504420179849)
      ·
        refine ⟨56015507652331128315134887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74687343536441504420179849 56015507652331128315134887)
        ·
          refine ⟨84023261478496692472702331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56015507652331128315134887 84023261478496692472702331)
          ·
            refine ⟨126034892217745038709053497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84023261478496692472702331 126034892217745038709053497)
            ·
              refine ⟨94526169163308779031790123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126034892217745038709053497 94526169163308779031790123)
              ·
                refine ⟨141789253744963168547685185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94526169163308779031790123 141789253744963168547685185)
                ·
                  refine ⟨106341940308722376410763889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141789253744963168547685185 106341940308722376410763889)
                  ·
                    refine ⟨79756455231541782308072917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106341940308722376410763889 79756455231541782308072917)
                    ·
                      refine ⟨1869291919489260522845459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79756455231541782308072917 1869291919489260522845459)
                      ·
                        rfl

theorem cell23_3640433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_3640433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640433 prefixEnd_3640433 := by exact prefixLift 3640433
  have htrace : WordTrace (prefixWord ++ tailWord_3640433) baseStart_3640433 baseEnd_3640433 := by
    simpa [prefixWord, tailWord_3640433, baseEnd_3640433] using wordTrace_append hprefix tailTrace_3640433
  have hstable : (prefixWord ++ tailWord_3640433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640433).length < 2 ^ (prefixWord ++ tailWord_3640433).sum := by decide
  have hdescent : baseEnd_3640433 < baseStart_3640433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640434 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 3, 2, 2]
def baseStart_3640434 : Nat := 118140960795 + 3640434 * 2 ^ 59
def prefixEnd_3640434 : Nat := 4983230072969 + 3 ^ 40 * 3640434 * 2
def baseEnd_3640434 : Nat := 1869292432969915018932955

theorem tailTrace_3640434 : CollatzResearch.WordTrace tailWord_3640434 prefixEnd_3640434 1869292432969915018932955 := by
  unfold tailWord_3640434
  simp only [CollatzResearch.WordTrace]
  refine ⟨33194384023334207368332089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88518357395557886315552237 33194384023334207368332089)
  ·
    refine ⟨24895788017500655526249067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33194384023334207368332089 24895788017500655526249067)
    ·
      refine ⟨37343682026250983289373601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24895788017500655526249067 37343682026250983289373601)
      ·
        refine ⟨28007761519688237467030201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37343682026250983289373601 28007761519688237467030201)
        ·
          refine ⟨21005821139766178100272651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28007761519688237467030201 21005821139766178100272651)
          ·
            refine ⟨31508731709649267150408977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21005821139766178100272651 31508731709649267150408977)
            ·
              refine ⟨23631548782236950362806733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31508731709649267150408977 23631548782236950362806733)
              ·
                refine ⟨8861830793338856386052525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23631548782236950362806733 8861830793338856386052525)
                ·
                  refine ⟨3323186547502071144769697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8861830793338856386052525 3323186547502071144769697)
                  ·
                    refine ⟨2492389910626553358577273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3323186547502071144769697 2492389910626553358577273)
                    ·
                      refine ⟨1869292432969915018932955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2492389910626553358577273 1869292432969915018932955)
                      ·
                        rfl

theorem cell23_3640434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_3640434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640434 prefixEnd_3640434 := by exact prefixLift 3640434
  have htrace : WordTrace (prefixWord ++ tailWord_3640434) baseStart_3640434 baseEnd_3640434 := by
    simpa [prefixWord, tailWord_3640434, baseEnd_3640434] using wordTrace_append hprefix tailTrace_3640434
  have hstable : (prefixWord ++ tailWord_3640434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640434).length < 2 ^ (prefixWord ++ tailWord_3640434).sum := by decide
  have hdescent : baseEnd_3640434 < baseStart_3640434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640443 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 6]
def baseStart_3640443 : Nat := 118140960795 + 3640443 * 2 ^ 59
def prefixEnd_3640443 : Nat := 4983230072969 + 3 ^ 40 * 3640443 * 2
def baseEnd_3640443 : Nat := 1869297054295805483720413

theorem tailTrace_3640443 : CollatzResearch.WordTrace tailWord_3640443 prefixEnd_3640443 1869297054295805483720413 := by
  unfold tailWord_3640443
  simp only [CollatzResearch.WordTrace]
  refine ⟨132777864350304224010405983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88518576233536149340270655 132777864350304224010405983)
  ·
    refine ⟨199166796525456336015608975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132777864350304224010405983 199166796525456336015608975)
    ·
      refine ⟨298750194788184504023413463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199166796525456336015608975 298750194788184504023413463)
      ·
        refine ⟨448125292182276756035120195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298750194788184504023413463 448125292182276756035120195)
        ·
          refine ⟨672187938273415134052680293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448125292182276756035120195 672187938273415134052680293)
          ·
            refine ⟨126035238426265337634877555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 672187938273415134052680293 126035238426265337634877555)
            ·
              refine ⟨189052857639398006452316333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126035238426265337634877555 189052857639398006452316333)
              ·
                refine ⟨70894821614774252419618625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189052857639398006452316333 70894821614774252419618625)
                ·
                  refine ⟨53171116211080689314713969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70894821614774252419618625 53171116211080689314713969)
                  ·
                    refine ⟨39878337158310516986035477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53171116211080689314713969 39878337158310516986035477)
                    ·
                      refine ⟨1869297054295805483720413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39878337158310516986035477 1869297054295805483720413)
                      ·
                        rfl

theorem cell23_3640443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 6].length) (baseStart_3640443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640443 prefixEnd_3640443 := by exact prefixLift 3640443
  have htrace : WordTrace (prefixWord ++ tailWord_3640443) baseStart_3640443 baseEnd_3640443 := by
    simpa [prefixWord, tailWord_3640443, baseEnd_3640443] using wordTrace_append hprefix tailTrace_3640443
  have hstable : (prefixWord ++ tailWord_3640443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640443).length < 2 ^ (prefixWord ++ tailWord_3640443).sum := by decide
  have hdescent : baseEnd_3640443 < baseStart_3640443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640471 : List Nat := [1, 1, 3, 3, 3, 3, 2, 1, 1, 2, 3]
def baseStart_3640471 : Nat := 118140960795 + 3640471 * 2 ^ 59
def prefixEnd_3640471 : Nat := 4983230072969 + 3 ^ 40 * 3640471 * 2
def baseEnd_3640471 : Nat := 1869311431754131374170285

theorem tailTrace_3640471 : CollatzResearch.WordTrace tailWord_3640471 prefixEnd_3640471 1869311431754131374170285 := by
  unfold tailWord_3640471
  simp only [CollatzResearch.WordTrace]
  refine ⟨132778885594202784792425267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88519257062801856528283511 132778885594202784792425267)
  ·
    refine ⟨199168328391304177188637901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132778885594202784792425267 199168328391304177188637901)
    ·
      refine ⟨74688123146739066445739213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199168328391304177188637901 74688123146739066445739213)
      ·
        refine ⟨28008046180027149917152205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74688123146739066445739213 28008046180027149917152205)
        ·
          refine ⟨10503017317510181218932077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28008046180027149917152205 10503017317510181218932077)
          ·
            refine ⟨3938631494066317957099529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10503017317510181218932077 3938631494066317957099529)
            ·
              refine ⟨2953973620549738467824647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3938631494066317957099529 2953973620549738467824647)
              ·
                refine ⟨4430960430824607701736971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2953973620549738467824647 4430960430824607701736971)
                ·
                  refine ⟨6646440646236911552605457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4430960430824607701736971 6646440646236911552605457)
                  ·
                    refine ⟨4984830484677683664454093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6646440646236911552605457 4984830484677683664454093)
                    ·
                      refine ⟨1869311431754131374170285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4984830484677683664454093 1869311431754131374170285)
                      ·
                        rfl

theorem cell23_3640471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_3640471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640471 prefixEnd_3640471 := by exact prefixLift 3640471
  have htrace : WordTrace (prefixWord ++ tailWord_3640471) baseStart_3640471 baseEnd_3640471 := by
    simpa [prefixWord, tailWord_3640471, baseEnd_3640471] using wordTrace_append hprefix tailTrace_3640471
  have hstable : (prefixWord ++ tailWord_3640471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640471).length < 2 ^ (prefixWord ++ tailWord_3640471).sum := by decide
  have hdescent : baseEnd_3640471 < baseStart_3640471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640484 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 4, 1, 3]
def baseStart_3640484 : Nat := 118140960795 + 3640484 * 2 ^ 59
def prefixEnd_3640484 : Nat := 4983230072969 + 3 ^ 40 * 3640484 * 2
def baseEnd_3640484 : Nat := 1869318107002639823307725

theorem tailTrace_3640484 : CollatzResearch.WordTrace tailWord_3640484 prefixEnd_3640484 1869318107002639823307725 := by
  unfold tailWord_3640484
  simp only [CollatzResearch.WordTrace]
  refine ⟨66389679871577844006324253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88519573162103792008432337 66389679871577844006324253)
  ·
    refine ⟨24896129951841691502371595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66389679871577844006324253 24896129951841691502371595)
    ·
      refine ⟨37344194927762537253557393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24896129951841691502371595 37344194927762537253557393)
      ·
        refine ⟨28008146195821902940168045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37344194927762537253557393 28008146195821902940168045)
        ·
          refine ⟨10503054823433213602563017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28008146195821902940168045 10503054823433213602563017)
          ·
            refine ⟨7877291117574910201922263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10503054823433213602563017 7877291117574910201922263)
            ·
              refine ⟨11815936676362365302883395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7877291117574910201922263 11815936676362365302883395)
              ·
                refine ⟨17723905014543547954325093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11815936676362365302883395 17723905014543547954325093)
                ·
                  refine ⟨3323232190226915241435955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17723905014543547954325093 3323232190226915241435955)
                  ·
                    refine ⟨4984848285340372862153933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3323232190226915241435955 4984848285340372862153933)
                    ·
                      refine ⟨1869318107002639823307725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4984848285340372862153933 1869318107002639823307725)
                      ·
                        rfl

theorem cell23_3640484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_3640484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640484 prefixEnd_3640484 := by exact prefixLift 3640484
  have htrace : WordTrace (prefixWord ++ tailWord_3640484) baseStart_3640484 baseEnd_3640484 := by
    simpa [prefixWord, tailWord_3640484, baseEnd_3640484] using wordTrace_append hprefix tailTrace_3640484
  have hstable : (prefixWord ++ tailWord_3640484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640484).length < 2 ^ (prefixWord ++ tailWord_3640484).sum := by decide
  have hdescent : baseEnd_3640484 < baseStart_3640484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640507 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 1, 4, 2]
def baseStart_3640507 : Nat := 118140960795 + 3640507 * 2 ^ 59
def prefixEnd_3640507 : Nat := 4983230072969 + 3 ^ 40 * 3640507 * 2
def baseEnd_3640507 : Nat := 1869329917057693233320119

theorem tailTrace_3640507 : CollatzResearch.WordTrace tailWord_3640507 prefixEnd_3640507 1869329917057693233320119 := by
  unfold tailWord_3640507
  simp only [CollatzResearch.WordTrace]
  refine ⟨132780198622072362940735775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88520132414714908627157183 132780198622072362940735775)
  ·
    refine ⟨199170297933108544411103663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132780198622072362940735775 199170297933108544411103663)
    ·
      refine ⟨298755446899662816616655495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199170297933108544411103663 298755446899662816616655495)
      ·
        refine ⟨448133170349494224924983243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298755446899662816616655495 448133170349494224924983243)
        ·
          refine ⟨672199755524241337387474865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448133170349494224924983243 672199755524241337387474865)
          ·
            refine ⟨504149816643181003040606149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 672199755524241337387474865 504149816643181003040606149)
            ·
              refine ⟨94528090620596438070113653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 504149816643181003040606149 94528090620596438070113653)
              ·
                refine ⟨8862008495680916069073155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94528090620596438070113653 8862008495680916069073155)
                ·
                  refine ⟨13293012743521374103609733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8862008495680916069073155 13293012743521374103609733)
                  ·
                    refine ⟨2492439889410257644426825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13293012743521374103609733 2492439889410257644426825)
                    ·
                      refine ⟨1869329917057693233320119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2492439889410257644426825 1869329917057693233320119)
                      ·
                        rfl

theorem cell23_3640507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 4, 2].length) (baseStart_3640507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640507 prefixEnd_3640507 := by exact prefixLift 3640507
  have htrace : WordTrace (prefixWord ++ tailWord_3640507) baseStart_3640507 baseEnd_3640507 := by
    simpa [prefixWord, tailWord_3640507, baseEnd_3640507] using wordTrace_append hprefix tailTrace_3640507
  have hstable : (prefixWord ++ tailWord_3640507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640507).length < 2 ^ (prefixWord ++ tailWord_3640507).sum := by decide
  have hdescent : baseEnd_3640507 < baseStart_3640507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640520 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_3640520 : Nat := 118140960795 + 3640520 * 2 ^ 59
def prefixEnd_3640520 : Nat := 4983230072969 + 3 ^ 40 * 3640520 * 2
def baseEnd_3640520 : Nat := 1869336592306201682457559

theorem tailTrace_3640520 : CollatzResearch.WordTrace tailWord_3640520 prefixEnd_3640520 1869336592306201682457559 := by
  unfold tailWord_3640520
  simp only [CollatzResearch.WordTrace]
  refine ⟨66390336385512633080479507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88520448514016844107306009 66390336385512633080479507)
  ·
    refine ⟨99585504578268949620719261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66390336385512633080479507 99585504578268949620719261)
    ·
      refine ⟨37344564216850856107769723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99585504578268949620719261 37344564216850856107769723)
      ·
        refine ⟨56016846325276284161654585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37344564216850856107769723 56016846325276284161654585)
        ·
          refine ⟨42012634743957213121240939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56016846325276284161654585 42012634743957213121240939)
          ·
            refine ⟨63018952115935819681861409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42012634743957213121240939 63018952115935819681861409)
            ·
              refine ⟨47264214086951864761396057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63018952115935819681861409 47264214086951864761396057)
              ·
                refine ⟨35448160565213898571047043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47264214086951864761396057 35448160565213898571047043)
                ·
                  refine ⟨53172240847820847856570565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35448160565213898571047043 53172240847820847856570565)
                  ·
                    refine ⟨9969795158966408973106981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53172240847820847856570565 9969795158966408973106981)
                    ·
                      refine ⟨1869336592306201682457559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9969795158966408973106981 1869336592306201682457559)
                      ·
                        rfl

theorem cell23_3640520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_3640520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640520 prefixEnd_3640520 := by exact prefixLift 3640520
  have htrace : WordTrace (prefixWord ++ tailWord_3640520) baseStart_3640520 baseEnd_3640520 := by
    simpa [prefixWord, tailWord_3640520, baseEnd_3640520] using wordTrace_append hprefix tailTrace_3640520
  have hstable : (prefixWord ++ tailWord_3640520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640520).length < 2 ^ (prefixWord ++ tailWord_3640520).sum := by decide
  have hdescent : baseEnd_3640520 < baseStart_3640520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640558 : List Nat := [4, 1, 2, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_3640558 : Nat := 118140960795 + 3640558 * 2 ^ 59
def prefixEnd_3640558 : Nat := 4983230072969 + 3 ^ 40 * 3640558 * 2
def baseEnd_3640558 : Nat := 1869356104571072533782385

theorem tailTrace_3640558 : CollatzResearch.WordTrace tailWord_3640558 prefixEnd_3640558 1869356104571072533782385 := by
  unfold tailWord_3640558
  simp only [CollatzResearch.WordTrace]
  refine ⟨16597757343110949831355291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88521372496591732433894885 16597757343110949831355291)
  ·
    refine ⟨24896636014666424747032937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16597757343110949831355291 24896636014666424747032937)
    ·
      refine ⟨18672477010999818560274703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24896636014666424747032937 18672477010999818560274703)
      ·
        refine ⟨28008715516499727840412055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18672477010999818560274703 28008715516499727840412055)
        ·
          refine ⟨42013073274749591760618083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28008715516499727840412055 42013073274749591760618083)
          ·
            refine ⟨63019609912124387640927125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42013073274749591760618083 63019609912124387640927125)
            ·
              refine ⟨2954044214630830670668459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63019609912124387640927125 2954044214630830670668459)
              ·
                refine ⟨4431066321946246006002689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2954044214630830670668459 4431066321946246006002689)
                ·
                  refine ⟨3323299741459684504502017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4431066321946246006002689 3323299741459684504502017)
                  ·
                    refine ⟨2492474806094763378376513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3323299741459684504502017 2492474806094763378376513)
                    ·
                      refine ⟨1869356104571072533782385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2492474806094763378376513 1869356104571072533782385)
                      ·
                        rfl

theorem cell23_3640558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_3640558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640558 prefixEnd_3640558 := by exact prefixLift 3640558
  have htrace : WordTrace (prefixWord ++ tailWord_3640558) baseStart_3640558 baseEnd_3640558 := by
    simpa [prefixWord, tailWord_3640558, baseEnd_3640558] using wordTrace_append hprefix tailTrace_3640558
  have hstable : (prefixWord ++ tailWord_3640558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640558).length < 2 ^ (prefixWord ++ tailWord_3640558).sum := by decide
  have hdescent : baseEnd_3640558 < baseStart_3640558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640567 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 2, 5, 2]
def baseStart_3640567 : Nat := 118140960795 + 3640567 * 2 ^ 59
def prefixEnd_3640567 : Nat := 4983230072969 + 3 ^ 40 * 3640567 * 2
def baseEnd_3640567 : Nat := 1869360725896962998569843

theorem tailTrace_3640567 : CollatzResearch.WordTrace tailWord_3640567 prefixEnd_3640567 1869360725896962998569843 := by
  unfold tailWord_3640567
  simp only [CollatzResearch.WordTrace]
  refine ⟨132782387001854993187919955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88521591334569995458613303 132782387001854993187919955)
  ·
    refine ⟨199173580502782489781879933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132782387001854993187919955 199173580502782489781879933)
    ·
      refine ⟨74690092688543433668204975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199173580502782489781879933 74690092688543433668204975)
      ·
        refine ⟨112035139032815150502307463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74690092688543433668204975 112035139032815150502307463)
        ·
          refine ⟨168052708549222725753461195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112035139032815150502307463 168052708549222725753461195)
          ·
            refine ⟨252079062823834088630191793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168052708549222725753461195 252079062823834088630191793)
            ·
              refine ⟨189059297117875566472643845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252079062823834088630191793 189059297117875566472643845)
              ·
                refine ⟨35448618209601668713620721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189059297117875566472643845 35448618209601668713620721)
                ·
                  refine ⟨26586463657201251535215541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35448618209601668713620721 26586463657201251535215541)
                  ·
                    refine ⟨2492480967862617331426457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26586463657201251535215541 2492480967862617331426457)
                    ·
                      refine ⟨1869360725896962998569843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2492480967862617331426457 1869360725896962998569843)
                      ·
                        rfl

theorem cell23_3640567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 5, 2].length) (baseStart_3640567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640567 prefixEnd_3640567 := by exact prefixLift 3640567
  have htrace : WordTrace (prefixWord ++ tailWord_3640567) baseStart_3640567 baseEnd_3640567 := by
    simpa [prefixWord, tailWord_3640567, baseEnd_3640567] using wordTrace_append hprefix tailTrace_3640567
  have hstable : (prefixWord ++ tailWord_3640567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640567).length < 2 ^ (prefixWord ++ tailWord_3640567).sum := by decide
  have hdescent : baseEnd_3640567 < baseStart_3640567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640570 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_3640570 : Nat := 118140960795 + 3640570 * 2 ^ 59
def prefixEnd_3640570 : Nat := 4983230072969 + 3 ^ 40 * 3640570 * 2
def baseEnd_3640570 : Nat := 1869362266338926486832329

theorem tailTrace_3640570 : CollatzResearch.WordTrace tailWord_3640570 prefixEnd_3640570 1869362266338926486832329 := by
  unfold tailWord_3640570
  simp only [CollatzResearch.WordTrace]
  refine ⟨33195624105211031175069791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88521664280562749800186109 33195624105211031175069791)
  ·
    refine ⟨49793436157816546762604687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33195624105211031175069791 49793436157816546762604687)
    ·
      refine ⟨74690154236724820143907031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49793436157816546762604687 74690154236724820143907031)
      ·
        refine ⟨112035231355087230215860547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74690154236724820143907031 112035231355087230215860547)
        ·
          refine ⟨168052847032630845323790821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112035231355087230215860547 168052847032630845323790821)
          ·
            refine ⟨31509908818618283498210779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168052847032630845323790821 31509908818618283498210779)
            ·
              refine ⟨47264863227927425247316169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31509908818618283498210779 47264863227927425247316169)
              ·
                refine ⟨35448647420945568935487127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47264863227927425247316169 35448647420945568935487127)
                ·
                  refine ⟨53172971131418353403230691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35448647420945568935487127 53172971131418353403230691)
                  ·
                    refine ⟨79759456697127530104846037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53172971131418353403230691 79759456697127530104846037)
                    ·
                      refine ⟨1869362266338926486832329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79759456697127530104846037 1869362266338926486832329)
                      ·
                        rfl

theorem cell23_3640570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_3640570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640570 prefixEnd_3640570 := by exact prefixLift 3640570
  have htrace : WordTrace (prefixWord ++ tailWord_3640570) baseStart_3640570 baseEnd_3640570 := by
    simpa [prefixWord, tailWord_3640570, baseEnd_3640570] using wordTrace_append hprefix tailTrace_3640570
  have hstable : (prefixWord ++ tailWord_3640570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640570).length < 2 ^ (prefixWord ++ tailWord_3640570).sum := by decide
  have hdescent : baseEnd_3640570 < baseStart_3640570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640577 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 2, 5]
def baseStart_3640577 : Nat := 118140960795 + 3640577 * 2 ^ 59
def prefixEnd_3640577 : Nat := 4983230072969 + 3 ^ 40 * 3640577 * 2
def baseEnd_3640577 : Nat := 623121953567835986481599

theorem tailTrace_3640577 : CollatzResearch.WordTrace tailWord_3640577 prefixEnd_3640577 623121953567835986481599 := by
  unfold tailWord_3640577
  simp only [CollatzResearch.WordTrace]
  refine ⟨132782751731818764895783985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88521834487879176597189323 132782751731818764895783985)
  ·
    refine ⟨99587063798864073671837989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132782751731818764895783985 99587063798864073671837989)
    ·
      refine ⟨18672574462287013813469623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99587063798864073671837989 18672574462287013813469623)
      ·
        refine ⟨28008861693430520720204435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18672574462287013813469623 28008861693430520720204435)
        ·
          refine ⟨42013292540145781080306653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28008861693430520720204435 42013292540145781080306653)
          ·
            refine ⟨15754984702554667905114995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42013292540145781080306653 15754984702554667905114995)
            ·
              refine ⟨23632477053832001857672493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15754984702554667905114995 23632477053832001857672493)
              ·
                refine ⟨8862178895187000696627185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23632477053832001857672493 8862178895187000696627185)
                ·
                  refine ⟨6646634171390250522470389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8862178895187000696627185 6646634171390250522470389)
                  ·
                    refine ⟨623121953567835986481599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6646634171390250522470389 623121953567835986481599)
                    ·
                      rfl

theorem cell23_3640577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_3640577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640577 prefixEnd_3640577 := by exact prefixLift 3640577
  have htrace : WordTrace (prefixWord ++ tailWord_3640577) baseStart_3640577 baseEnd_3640577 := by
    simpa [prefixWord, tailWord_3640577, baseEnd_3640577] using wordTrace_append hprefix tailTrace_3640577
  have hstable : (prefixWord ++ tailWord_3640577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640577).length < 2 ^ (prefixWord ++ tailWord_3640577).sum := by decide
  have hdescent : baseEnd_3640577 < baseStart_3640577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640620 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 10]
def baseStart_3640620 : Nat := 118140960795 + 3640620 * 2 ^ 59
def prefixEnd_3640620 : Nat := 4983230072969 + 3 ^ 40 * 3640620 * 2
def baseEnd_3640620 : Nat := 207709771152405699023011

theorem tailTrace_3640620 : CollatzResearch.WordTrace tailWord_3640620 prefixEnd_3640620 207709771152405699023011 := by
  unfold tailWord_3640620
  simp only [CollatzResearch.WordTrace]
  refine ⟨66392160035331491619799657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88522880047108655493066209 66392160035331491619799657)
  ·
    refine ⟨49794120026498618714849743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66392160035331491619799657 49794120026498618714849743)
    ·
      refine ⟨74691180039747928072274615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49794120026498618714849743 74691180039747928072274615)
      ·
        refine ⟨112036770059621892108411923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74691180039747928072274615 112036770059621892108411923)
        ·
          refine ⟨168055155089432838162617885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112036770059621892108411923 168055155089432838162617885)
          ·
            refine ⟨63020683158537314310981707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168055155089432838162617885 63020683158537314310981707)
            ·
              refine ⟨94531024737805971466472561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63020683158537314310981707 94531024737805971466472561)
              ·
                refine ⟨70898268553354478599854421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94531024737805971466472561 70898268553354478599854421)
                ·
                  refine ⟨207709771152405699023011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 70898268553354478599854421 207709771152405699023011)
                  ·
                    rfl

theorem cell23_3640620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_3640620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640620 prefixEnd_3640620 := by exact prefixLift 3640620
  have htrace : WordTrace (prefixWord ++ tailWord_3640620) baseStart_3640620 baseEnd_3640620 := by
    simpa [prefixWord, tailWord_3640620, baseEnd_3640620] using wordTrace_append hprefix tailTrace_3640620
  have hstable : (prefixWord ++ tailWord_3640620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640620).length < 2 ^ (prefixWord ++ tailWord_3640620).sum := by decide
  have hdescent : baseEnd_3640620 < baseStart_3640620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640644 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3640644 : Nat := 118140960795 + 3640644 * 2 ^ 59
def prefixEnd_3640644 : Nat := 4983230072969 + 3 ^ 40 * 3640644 * 2
def baseEnd_3640644 : Nat := 1869400263907359197306989

theorem tailTrace_3640644 : CollatzResearch.WordTrace tailWord_3640644 prefixEnd_3640644 1869400263907359197306989 := by
  unfold tailWord_3640644
  simp only [CollatzResearch.WordTrace]
  refine ⟨66392597711288017669236493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88523463615050690225648657 66392597711288017669236493)
  ·
    refine ⟨24897224141733006625963685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66392597711288017669236493 24897224141733006625963685)
    ·
      refine ⟨4668229526574938742368191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24897224141733006625963685 4668229526574938742368191)
      ·
        refine ⟨7002344289862408113552287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4668229526574938742368191 7002344289862408113552287)
        ·
          refine ⟨10503516434793612170328431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7002344289862408113552287 10503516434793612170328431)
          ·
            refine ⟨15755274652190418255492647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10503516434793612170328431 15755274652190418255492647)
            ·
              refine ⟨23632911978285627383238971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15755274652190418255492647 23632911978285627383238971)
              ·
                refine ⟨35449367967428441074858457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23632911978285627383238971 35449367967428441074858457)
                ·
                  refine ⟨26587025975571330806143843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35449367967428441074858457 26587025975571330806143843)
                  ·
                    refine ⟨39880538963356996209215765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26587025975571330806143843 39880538963356996209215765)
                    ·
                      refine ⟨1869400263907359197306989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39880538963356996209215765 1869400263907359197306989)
                      ·
                        rfl

theorem cell23_3640644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3640644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640644 prefixEnd_3640644 := by exact prefixLift 3640644
  have htrace : WordTrace (prefixWord ++ tailWord_3640644) baseStart_3640644 baseEnd_3640644 := by
    simpa [prefixWord, tailWord_3640644, baseEnd_3640644] using wordTrace_append hprefix tailTrace_3640644
  have hstable : (prefixWord ++ tailWord_3640644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640644).length < 2 ^ (prefixWord ++ tailWord_3640644).sum := by decide
  have hdescent : baseEnd_3640644 < baseStart_3640644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640684 : List Nat := [2, 2, 1, 1, 5, 1, 1, 4, 1, 5]
def baseStart_3640684 : Nat := 118140960795 + 3640684 * 2 ^ 59
def prefixEnd_3640684 : Nat := 4983230072969 + 3 ^ 40 * 3640684 * 2
def baseEnd_3640684 : Nat := 623140267711179680268935

theorem tailTrace_3640684 : CollatzResearch.WordTrace tailWord_3640684 prefixEnd_3640684 623140267711179680268935 := by
  unfold tailWord_3640684
  simp only [CollatzResearch.WordTrace]
  refine ⟨66393327171215561084964553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88524436228287414779952737 66393327171215561084964553)
  ·
    refine ⟨49794995378411670813723415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66393327171215561084964553 49794995378411670813723415)
    ·
      refine ⟨74692493067617506220585123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49794995378411670813723415 74692493067617506220585123)
      ·
        refine ⟨112038739601426259330877685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74692493067617506220585123 112038739601426259330877685)
        ·
          refine ⟨10503631837633711812269783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112038739601426259330877685 10503631837633711812269783)
          ·
            refine ⟨15755447756450567718404675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10503631837633711812269783 15755447756450567718404675)
            ·
              refine ⟨23633171634675851577607013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15755447756450567718404675 23633171634675851577607013)
              ·
                refine ⟨4431219681501722170801315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23633171634675851577607013 4431219681501722170801315)
                ·
                  refine ⟨6646829522252583256201973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431219681501722170801315 6646829522252583256201973)
                  ·
                    refine ⟨623140267711179680268935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6646829522252583256201973 623140267711179680268935)
                    ·
                      rfl

theorem cell23_3640684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_3640684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640684 prefixEnd_3640684 := by exact prefixLift 3640684
  have htrace : WordTrace (prefixWord ++ tailWord_3640684) baseStart_3640684 baseEnd_3640684 := by
    simpa [prefixWord, tailWord_3640684, baseEnd_3640684] using wordTrace_append hprefix tailTrace_3640684
  have hstable : (prefixWord ++ tailWord_3640684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640684).length < 2 ^ (prefixWord ++ tailWord_3640684).sum := by decide
  have hdescent : baseEnd_3640684 < baseStart_3640684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640697 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 1, 6]
def baseStart_3640697 : Nat := 118140960795 + 3640697 * 2 ^ 59
def prefixEnd_3640697 : Nat := 4983230072969 + 3 ^ 40 * 3640697 * 2
def baseEnd_3640697 : Nat := 623142492794015829981415

theorem tailTrace_3640697 : CollatzResearch.WordTrace tailWord_3640697 prefixEnd_3640697 623142492794015829981415 := by
  unfold tailWord_3640697
  simp only [CollatzResearch.WordTrace]
  refine ⟨132787128491384025390152345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88524752327589350260101563 132787128491384025390152345)
  ·
    refine ⟨99590346368538019042614259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132787128491384025390152345 99590346368538019042614259)
    ·
      refine ⟨149385519552807028563921389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99590346368538019042614259 149385519552807028563921389)
      ·
        refine ⟨56019569832302635711470521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149385519552807028563921389 56019569832302635711470521)
        ·
          refine ⟨42014677374226976783602891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56019569832302635711470521 42014677374226976783602891)
          ·
            refine ⟨63022016061340465175404337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42014677374226976783602891 63022016061340465175404337)
            ·
              refine ⟨47266512046005348881553253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63022016061340465175404337 47266512046005348881553253)
              ·
                refine ⟨8862471008626002915291235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47266512046005348881553253 8862471008626002915291235)
                ·
                  refine ⟨13293706512939004372936853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8862471008626002915291235 13293706512939004372936853)
                  ·
                    refine ⟨623142492794015829981415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13293706512939004372936853 623142492794015829981415)
                    ·
                      rfl

theorem cell23_3640697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 6].length) (baseStart_3640697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640697 prefixEnd_3640697 := by exact prefixLift 3640697
  have htrace : WordTrace (prefixWord ++ tailWord_3640697) baseStart_3640697 baseEnd_3640697 := by
    simpa [prefixWord, tailWord_3640697, baseEnd_3640697] using wordTrace_append hprefix tailTrace_3640697
  have hstable : (prefixWord ++ tailWord_3640697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640697).length < 2 ^ (prefixWord ++ tailWord_3640697).sum := by decide
  have hdescent : baseEnd_3640697 < baseStart_3640697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640738 : List Nat := [3, 3, 1, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_3640738 : Nat := 118140960795 + 3640738 * 2 ^ 59
def prefixEnd_3640738 : Nat := 4983230072969 + 3 ^ 40 * 3640738 * 2
def baseEnd_3640738 : Nat := 1869448531088881829531557

theorem tailTrace_3640738 : CollatzResearch.WordTrace tailWord_3640738 prefixEnd_3640738 1869448531088881829531557 := by
  unfold tailWord_3640738
  simp only [CollatzResearch.WordTrace]
  refine ⟨33197155971058872348098717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88525749256156992928263245 33197155971058872348098717)
  ·
    refine ⟨12448933489147077130537019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33197155971058872348098717 12448933489147077130537019)
    ·
      refine ⟨18673400233720615695805529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12448933489147077130537019 18673400233720615695805529)
      ·
        refine ⟨14005050175290461771854147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18673400233720615695805529 14005050175290461771854147)
        ·
          refine ⟨21007575262935692657781221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14005050175290461771854147 21007575262935692657781221)
          ·
            refine ⟨3938920361800442373333979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21007575262935692657781221 3938920361800442373333979)
            ·
              refine ⟨5908380542700663560000969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3938920361800442373333979 5908380542700663560000969)
              ·
                refine ⟨4431285407025497670000727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5908380542700663560000969 4431285407025497670000727)
                ·
                  refine ⟨6646928110538246505001091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431285407025497670000727 6646928110538246505001091)
                  ·
                    refine ⟨9970392165807369757501637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6646928110538246505001091 9970392165807369757501637)
                    ·
                      refine ⟨1869448531088881829531557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9970392165807369757501637 1869448531088881829531557)
                      ·
                        rfl

theorem cell23_3640738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_3640738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640738 prefixEnd_3640738 := by exact prefixLift 3640738
  have htrace : WordTrace (prefixWord ++ tailWord_3640738) baseStart_3640738 baseEnd_3640738 := by
    simpa [prefixWord, tailWord_3640738, baseEnd_3640738] using wordTrace_append hprefix tailTrace_3640738
  have hstable : (prefixWord ++ tailWord_3640738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640738).length < 2 ^ (prefixWord ++ tailWord_3640738).sum := by decide
  have hdescent : baseEnd_3640738 < baseStart_3640738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640767 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 5]
def baseStart_3640767 : Nat := 118140960795 + 3640767 * 2 ^ 59
def prefixEnd_3640767 : Nat := 4983230072969 + 3 ^ 40 * 3640767 * 2
def baseEnd_3640767 : Nat := 1869463422027862216068923

theorem tailTrace_3640767 : CollatzResearch.WordTrace tailWord_3640767 prefixEnd_3640767 1869463422027862216068923 := by
  unfold tailWord_3640767
  simp only [CollatzResearch.WordTrace]
  refine ⟨132789681601130427345200555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88526454400753618230133703 132789681601130427345200555)
  ·
    refine ⟨199184522401695641017800833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132789681601130427345200555 199184522401695641017800833)
    ·
      refine ⟨149388391801271730763350625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199184522401695641017800833 149388391801271730763350625)
      ·
        refine ⟨112041293850953798072512969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149388391801271730763350625 112041293850953798072512969)
        ·
          refine ⟨84030970388215348554384727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112041293850953798072512969 84030970388215348554384727)
          ·
            refine ⟨126046455582323022831577091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84030970388215348554384727 126046455582323022831577091)
            ·
              refine ⟨189069683373484534247365637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126046455582323022831577091 189069683373484534247365637)
              ·
                refine ⟨35450565632528350171381057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189069683373484534247365637 35450565632528350171381057)
                ·
                  refine ⟨26587924224396262628535793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35450565632528350171381057 26587924224396262628535793)
                  ·
                    refine ⟨19940943168297196971401845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26587924224396262628535793 19940943168297196971401845)
                    ·
                      refine ⟨1869463422027862216068923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19940943168297196971401845 1869463422027862216068923)
                      ·
                        rfl

theorem cell23_3640767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_3640767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640767 prefixEnd_3640767 := by exact prefixLift 3640767
  have htrace : WordTrace (prefixWord ++ tailWord_3640767) baseStart_3640767 baseEnd_3640767 := by
    simpa [prefixWord, tailWord_3640767, baseEnd_3640767] using wordTrace_append hprefix tailTrace_3640767
  have hstable : (prefixWord ++ tailWord_3640767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640767).length < 2 ^ (prefixWord ++ tailWord_3640767).sum := by decide
  have hdescent : baseEnd_3640767 < baseStart_3640767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640771 : List Nat := [1, 1, 1, 3, 1, 1, 5, 4, 2, 1, 3]
def baseStart_3640771 : Nat := 118140960795 + 3640771 * 2 ^ 59
def prefixEnd_3640771 : Nat := 4983230072969 + 3 ^ 40 * 3640771 * 2
def baseEnd_3640771 : Nat := 1869465475950480200418905

theorem tailTrace_3640771 : CollatzResearch.WordTrace tailWord_3640771 prefixEnd_3640771 1869465475950480200418905 := by
  unfold tailWord_3640771
  simp only [CollatzResearch.WordTrace]
  refine ⟨132789827493115936028346167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88526551662077290685564111 132789827493115936028346167)
  ·
    refine ⟨199184741239673904042519251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132789827493115936028346167 199184741239673904042519251)
    ·
      refine ⟨298777111859510856063778877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199184741239673904042519251 298777111859510856063778877)
      ·
        refine ⟨112041416947316571023917079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298777111859510856063778877 112041416947316571023917079)
        ·
          refine ⟨168062125420974856535875619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112041416947316571023917079 168062125420974856535875619)
          ·
            refine ⟨252093188131462284803813429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168062125420974856535875619 252093188131462284803813429)
            ·
              refine ⟨23633736387324589200357509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252093188131462284803813429 23633736387324589200357509)
              ·
                refine ⟨4431325572623360475067033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23633736387324589200357509 4431325572623360475067033)
                ·
                  refine ⟨3323494179467520356300275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4431325572623360475067033 3323494179467520356300275)
                  ·
                    refine ⟨4985241269201280534450413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3323494179467520356300275 4985241269201280534450413)
                    ·
                      refine ⟨1869465475950480200418905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4985241269201280534450413 1869465475950480200418905)
                      ·
                        rfl

theorem cell23_3640771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_3640771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640771 prefixEnd_3640771 := by exact prefixLift 3640771
  have htrace : WordTrace (prefixWord ++ tailWord_3640771) baseStart_3640771 baseEnd_3640771 := by
    simpa [prefixWord, tailWord_3640771, baseEnd_3640771] using wordTrace_append hprefix tailTrace_3640771
  have hstable : (prefixWord ++ tailWord_3640771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640771).length < 2 ^ (prefixWord ++ tailWord_3640771).sum := by decide
  have hdescent : baseEnd_3640771 < baseStart_3640771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640772 : List Nat := [2, 3, 3, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_3640772 : Nat := 118140960795 + 3640772 * 2 ^ 59
def prefixEnd_3640772 : Nat := 4983230072969 + 3 ^ 40 * 3640772 * 2
def baseEnd_3640772 : Nat := 1869465989431134696506401

theorem tailTrace_3640772 : CollatzResearch.WordTrace tailWord_3640772 prefixEnd_3640772 1869465989431134696506401 := by
  unfold tailWord_3640772
  simp only [CollatzResearch.WordTrace]
  refine ⟨66394931983056156599566285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88526575977408208799421713 66394931983056156599566285)
  ·
    refine ⟨24898099493646058724837357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66394931983056156599566285 24898099493646058724837357)
    ·
      refine ⟨9336787310117272021814009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24898099493646058724837357 9336787310117272021814009)
      ·
        refine ⟨7002590482587954016360507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9336787310117272021814009 7002590482587954016360507)
        ·
          refine ⟨10503885723881931024540761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7002590482587954016360507 10503885723881931024540761)
          ·
            refine ⟨7877914292911448268405571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10503885723881931024540761 7877914292911448268405571)
            ·
              refine ⟨11816871439367172402608357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7877914292911448268405571 11816871439367172402608357)
              ·
                refine ⟨2215663394881344825489067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11816871439367172402608357 2215663394881344825489067)
                ·
                  refine ⟨3323495092322017238233601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215663394881344825489067 3323495092322017238233601)
                  ·
                    refine ⟨2492621319241512928675201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3323495092322017238233601 2492621319241512928675201)
                    ·
                      refine ⟨1869465989431134696506401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2492621319241512928675201 1869465989431134696506401)
                      ·
                        rfl

theorem cell23_3640772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_3640772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640772 prefixEnd_3640772 := by exact prefixLift 3640772
  have htrace : WordTrace (prefixWord ++ tailWord_3640772) baseStart_3640772 baseEnd_3640772 := by
    simpa [prefixWord, tailWord_3640772, baseEnd_3640772] using wordTrace_append hprefix tailTrace_3640772
  have hstable : (prefixWord ++ tailWord_3640772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640772).length < 2 ^ (prefixWord ++ tailWord_3640772).sum := by decide
  have hdescent : baseEnd_3640772 < baseStart_3640772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640788 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 1, 3, 3]
def baseStart_3640788 : Nat := 118140960795 + 3640788 * 2 ^ 59
def prefixEnd_3640788 : Nat := 4983230072969 + 3 ^ 40 * 3640788 * 2
def baseEnd_3640788 : Nat := 1869474205121606633906327

theorem tailTrace_3640788 : CollatzResearch.WordTrace tailWord_3640788 prefixEnd_3640788 1869474205121606633906327 := by
  unfold tailWord_3640788
  simp only [CollatzResearch.WordTrace]
  refine ⟨66395223767027173965857509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88526965022702898621143345 66395223767027173965857509)
  ·
    refine ⟨12449104456317595118598283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66395223767027173965857509 12449104456317595118598283)
    ·
      refine ⟨18673656684476392677897425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12449104456317595118598283 18673656684476392677897425)
      ·
        refine ⟨14005242513357294508423069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18673656684476392677897425 14005242513357294508423069)
        ·
          refine ⟨5251965942508985440658651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14005242513357294508423069 5251965942508985440658651)
          ·
            refine ⟨7877948913763478160987977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5251965942508985440658651 7877948913763478160987977)
            ·
              refine ⟨5908461685322608620740983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7877948913763478160987977 5908461685322608620740983)
              ·
                refine ⟨8862692527983912931111475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5908461685322608620740983 8862692527983912931111475)
                ·
                  refine ⟨13294038791975869396667213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8862692527983912931111475 13294038791975869396667213)
                  ·
                    refine ⟨4985264546990951023750205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13294038791975869396667213 4985264546990951023750205)
                    ·
                      refine ⟨1869474205121606633906327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4985264546990951023750205 1869474205121606633906327)
                      ·
                        rfl

theorem cell23_3640788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_3640788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640788 prefixEnd_3640788 := by exact prefixLift 3640788
  have htrace : WordTrace (prefixWord ++ tailWord_3640788) baseStart_3640788 baseEnd_3640788 := by
    simpa [prefixWord, tailWord_3640788, baseEnd_3640788] using wordTrace_append hprefix tailTrace_3640788
  have hstable : (prefixWord ++ tailWord_3640788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640788).length < 2 ^ (prefixWord ++ tailWord_3640788).sum := by decide
  have hdescent : baseEnd_3640788 < baseStart_3640788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640814 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_3640814 : Nat := 118140960795 + 3640814 * 2 ^ 59
def prefixEnd_3640814 : Nat := 4983230072969 + 3 ^ 40 * 3640814 * 2
def baseEnd_3640814 : Nat := 1869487555618623532181207

theorem tailTrace_3640814 : CollatzResearch.WordTrace tailWord_3640814 prefixEnd_3640814 1869487555618623532181207 := by
  unfold tailWord_3640814
  simp only [CollatzResearch.WordTrace]
  refine ⟨16598924478995019296520187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88527597221306769581440997 16598924478995019296520187)
  ·
    refine ⟨24898386718492528944780281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16598924478995019296520187 24898386718492528944780281)
    ·
      refine ⟨18673790038869396708585211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24898386718492528944780281 18673790038869396708585211)
      ·
        refine ⟨28010685058304095062877817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18673790038869396708585211 28010685058304095062877817)
        ·
          refine ⟨21008013793728071297158363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28010685058304095062877817 21008013793728071297158363)
          ·
            refine ⟨31512020690592106945737545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21008013793728071297158363 31512020690592106945737545)
            ·
              refine ⟨23634015517944080209303159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31512020690592106945737545 23634015517944080209303159)
              ·
                refine ⟨35451023276916120313954739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23634015517944080209303159 35451023276916120313954739)
                ·
                  refine ⟨53176534915374180470932109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35451023276916120313954739 53176534915374180470932109)
                  ·
                    refine ⟨19941200593265317676599541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53176534915374180470932109 19941200593265317676599541)
                    ·
                      refine ⟨1869487555618623532181207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19941200593265317676599541 1869487555618623532181207)
                      ·
                        rfl

theorem cell23_3640814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_3640814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640814 prefixEnd_3640814 := by exact prefixLift 3640814
  have htrace : WordTrace (prefixWord ++ tailWord_3640814) baseStart_3640814 baseEnd_3640814 := by
    simpa [prefixWord, tailWord_3640814, baseEnd_3640814] using wordTrace_append hprefix tailTrace_3640814
  have hstable : (prefixWord ++ tailWord_3640814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640814).length < 2 ^ (prefixWord ++ tailWord_3640814).sum := by decide
  have hdescent : baseEnd_3640814 < baseStart_3640814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640821 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3640821 : Nat := 118140960795 + 3640821 * 2 ^ 59
def prefixEnd_3640821 : Nat := 4983230072969 + 3 ^ 40 * 3640821 * 2
def baseEnd_3640821 : Nat := 623163716661068334931225

theorem tailTrace_3640821 : CollatzResearch.WordTrace tailWord_3640821 prefixEnd_3640821 623163716661068334931225 := by
  unfold tailWord_3640821
  simp only [CollatzResearch.WordTrace]
  refine ⟨132791651142934794567666317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88527767428623196378444211 132791651142934794567666317)
  ·
    refine ⟨49796869178600547962874869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132791651142934794567666317 49796869178600547962874869)
    ·
      refine ⟨4668456485493801371519519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49796869178600547962874869 4668456485493801371519519)
      ·
        refine ⟨7002684728240702057279279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4668456485493801371519519 7002684728240702057279279)
        ·
          refine ⟨10504027092361053085918919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7002684728240702057279279 10504027092361053085918919)
          ·
            refine ⟨15756040638541579628878379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10504027092361053085918919 15756040638541579628878379)
            ·
              refine ⟨23634060957812369443317569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15756040638541579628878379 23634060957812369443317569)
              ·
                refine ⟨17725545718359277082488177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23634060957812369443317569 17725545718359277082488177)
                ·
                  refine ⟨13294159288769457811866133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17725545718359277082488177 13294159288769457811866133)
                  ·
                    refine ⟨623163716661068334931225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13294159288769457811866133 623163716661068334931225)
                    ·
                      rfl

theorem cell23_3640821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3640821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640821 prefixEnd_3640821 := by exact prefixLift 3640821
  have htrace : WordTrace (prefixWord ++ tailWord_3640821) baseStart_3640821 baseEnd_3640821 := by
    simpa [prefixWord, tailWord_3640821, baseEnd_3640821] using wordTrace_append hprefix tailTrace_3640821
  have hstable : (prefixWord ++ tailWord_3640821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640821).length < 2 ^ (prefixWord ++ tailWord_3640821).sum := by decide
  have hdescent : baseEnd_3640821 < baseStart_3640821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640824 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_3640824 : Nat := 118140960795 + 3640824 * 2 ^ 59
def prefixEnd_3640824 : Nat := 4983230072969 + 3 ^ 40 * 3640824 * 2
def baseEnd_3640824 : Nat := 1869492690425168493056161

theorem tailTrace_3640824 : CollatzResearch.WordTrace tailWord_3640824 prefixEnd_3640824 1869492690425168493056161 := by
  unfold tailWord_3640824
  simp only [CollatzResearch.WordTrace]
  refine ⟨66395880280961963040012763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88527840374615950720017017 66395880280961963040012763)
  ·
    refine ⟨99593820421442944560019145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66395880280961963040012763 99593820421442944560019145)
    ·
      refine ⟨74695365316082208420014359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99593820421442944560019145 74695365316082208420014359)
      ·
        refine ⟨112043047974123312630021539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74695365316082208420014359 112043047974123312630021539)
        ·
          refine ⟨168064571961184968945032309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112043047974123312630021539 168064571961184968945032309)
          ·
            refine ⟨15756053621361090838596779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168064571961184968945032309 15756053621361090838596779)
            ·
              refine ⟨23634080432041636257895169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15756053621361090838596779 23634080432041636257895169)
              ·
                refine ⟨17725560324031227193421377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23634080432041636257895169 17725560324031227193421377)
                ·
                  refine ⟨13294170243023420395066033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17725560324031227193421377 13294170243023420395066033)
                  ·
                    refine ⟨9970627682267565296299525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13294170243023420395066033 9970627682267565296299525)
                    ·
                      refine ⟨1869492690425168493056161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9970627682267565296299525 1869492690425168493056161)
                      ·
                        rfl

theorem cell23_3640824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_3640824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640824 prefixEnd_3640824 := by exact prefixLift 3640824
  have htrace : WordTrace (prefixWord ++ tailWord_3640824) baseStart_3640824 baseEnd_3640824 := by
    simpa [prefixWord, tailWord_3640824, baseEnd_3640824] using wordTrace_append hprefix tailTrace_3640824
  have hstable : (prefixWord ++ tailWord_3640824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640824).length < 2 ^ (prefixWord ++ tailWord_3640824).sum := by decide
  have hdescent : baseEnd_3640824 < baseStart_3640824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640827 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 7]
def baseStart_3640827 : Nat := 118140960795 + 3640827 * 2 ^ 59
def prefixEnd_3640827 : Nat := 4983230072969 + 3 ^ 40 * 3640827 * 2
def baseEnd_3640827 : Nat := 1869494230867131981318647

theorem tailTrace_3640827 : CollatzResearch.WordTrace tailWord_3640827 prefixEnd_3640827 1869494230867131981318647 := by
  unfold tailWord_3640827
  simp only [CollatzResearch.WordTrace]
  refine ⟨132791869980913057592384735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88527913320608705061589823 132791869980913057592384735)
  ·
    refine ⟨199187804971369586388577103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132791869980913057592384735 199187804971369586388577103)
    ·
      refine ⟨298781707457054379582865655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199187804971369586388577103 298781707457054379582865655)
      ·
        refine ⟨448172561185581569374298483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298781707457054379582865655 448172561185581569374298483)
        ·
          refine ⟨672258841778372354061447725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448172561185581569374298483 672258841778372354061447725)
          ·
            refine ⟨252097065666889632773042897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 672258841778372354061447725 252097065666889632773042897)
            ·
              refine ⟨189072799250167224579782173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252097065666889632773042897 189072799250167224579782173)
              ·
                refine ⟨70902299718812709217418315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189072799250167224579782173 70902299718812709217418315)
                ·
                  refine ⟨106353449578219063826127473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70902299718812709217418315 106353449578219063826127473)
                  ·
                    refine ⟨79765087183664297869595605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106353449578219063826127473 79765087183664297869595605)
                    ·
                      refine ⟨1869494230867131981318647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79765087183664297869595605 1869494230867131981318647)
                      ·
                        rfl

theorem cell23_3640827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_3640827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640827 prefixEnd_3640827 := by exact prefixLift 3640827
  have htrace : WordTrace (prefixWord ++ tailWord_3640827) baseStart_3640827 baseEnd_3640827 := by
    simpa [prefixWord, tailWord_3640827, baseEnd_3640827] using wordTrace_append hprefix tailTrace_3640827
  have hstable : (prefixWord ++ tailWord_3640827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640827).length < 2 ^ (prefixWord ++ tailWord_3640827).sum := by decide
  have hdescent : baseEnd_3640827 < baseStart_3640827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640901 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 1, 6, 2]
def baseStart_3640901 : Nat := 118140960795 + 3640901 * 2 ^ 59
def prefixEnd_3640901 : Nat := 4983230072969 + 3 ^ 40 * 3640901 * 2
def baseEnd_3640901 : Nat := 1869532228435564691793307

theorem tailTrace_3640901 : CollatzResearch.WordTrace tailWord_3640901 prefixEnd_3640901 1869532228435564691793307 := by
  unfold tailWord_3640901
  simp only [CollatzResearch.WordTrace]
  refine ⟨132794568982644968230578557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88529712655096645487052371 132794568982644968230578557)
  ·
    refine ⟨49797963368491863086466959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132794568982644968230578557 49797963368491863086466959)
    ·
      refine ⟨74696945052737794629700439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49797963368491863086466959 74696945052737794629700439)
      ·
        refine ⟨112045417579106691944550659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74696945052737794629700439 112045417579106691944550659)
        ·
          refine ⟨168068126368660037916825989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112045417579106691944550659 168068126368660037916825989)
          ·
            refine ⟨31512773694123757109404873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168068126368660037916825989 31512773694123757109404873)
            ·
              refine ⟨23634580270592817832053655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31512773694123757109404873 23634580270592817832053655)
              ·
                refine ⟨35451870405889226748080483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23634580270592817832053655 35451870405889226748080483)
                ·
                  refine ⟨53177805608833840122120725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35451870405889226748080483 53177805608833840122120725)
                  ·
                    refine ⟨2492709637914086255724409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53177805608833840122120725 2492709637914086255724409)
                    ·
                      refine ⟨1869532228435564691793307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2492709637914086255724409 1869532228435564691793307)
                      ·
                        rfl

theorem cell23_3640901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 6, 2].length) (baseStart_3640901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640901 prefixEnd_3640901 := by exact prefixLift 3640901
  have htrace : WordTrace (prefixWord ++ tailWord_3640901) baseStart_3640901 baseEnd_3640901 := by
    simpa [prefixWord, tailWord_3640901, baseEnd_3640901] using wordTrace_append hprefix tailTrace_3640901
  have hstable : (prefixWord ++ tailWord_3640901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640901).length < 2 ^ (prefixWord ++ tailWord_3640901).sum := by decide
  have hdescent : baseEnd_3640901 < baseStart_3640901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640928 : List Nat := [2, 1, 1, 3, 2, 1, 1, 7, 1, 4]
def baseStart_3640928 : Nat := 118140960795 + 3640928 * 2 ^ 59
def prefixEnd_3640928 : Nat := 4983230072969 + 3 ^ 40 * 3640928 * 2
def baseEnd_3640928 : Nat := 623182030804412028718561

theorem tailTrace_3640928 : CollatzResearch.WordTrace tailWord_3640928 prefixEnd_3640928 623182030804412028718561 := by
  unfold tailWord_3640928
  simp only [CollatzResearch.WordTrace]
  refine ⟨66397776876773575920905719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88530369169031434561207625 66397776876773575920905719)
  ·
    refine ⟨99596665315160363881358579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66397776876773575920905719 99596665315160363881358579)
    ·
      refine ⟨149394997972740545822037869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99596665315160363881358579 149394997972740545822037869)
      ·
        refine ⟨56023124239777704683264201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149394997972740545822037869 56023124239777704683264201)
        ·
          refine ⟨42017343179833278512448151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56023124239777704683264201 42017343179833278512448151)
          ·
            refine ⟨63026014769749917768672227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42017343179833278512448151 63026014769749917768672227)
            ·
              refine ⟨94539022154624876653008341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63026014769749917768672227 94539022154624876653008341)
              ·
                refine ⟨2215758331749020546554883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 94539022154624876653008341 2215758331749020546554883)
                ·
                  refine ⟨3323637497623530819832325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215758331749020546554883 3323637497623530819832325)
                  ·
                    refine ⟨623182030804412028718561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3323637497623530819832325 623182030804412028718561)
                    ·
                      rfl

theorem cell23_3640928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 1, 4].length) (baseStart_3640928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640928 prefixEnd_3640928 := by exact prefixLift 3640928
  have htrace : WordTrace (prefixWord ++ tailWord_3640928) baseStart_3640928 baseEnd_3640928 := by
    simpa [prefixWord, tailWord_3640928, baseEnd_3640928] using wordTrace_append hprefix tailTrace_3640928
  have hstable : (prefixWord ++ tailWord_3640928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640928).length < 2 ^ (prefixWord ++ tailWord_3640928).sum := by decide
  have hdescent : baseEnd_3640928 < baseStart_3640928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640938 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_3640938 : Nat := 118140960795 + 3640938 * 2 ^ 59
def prefixEnd_3640938 : Nat := 4983230072969 + 3 ^ 40 * 3640938 * 2
def baseEnd_3640938 : Nat := 1869551227219781047030637

theorem tailTrace_3640938 : CollatzResearch.WordTrace tailWord_3640938 prefixEnd_3640938 1869551227219781047030637 := by
  unfold tailWord_3640938
  simp only [CollatzResearch.WordTrace]
  refine ⟨33198979620877730887418867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88530612322340615699783645 33198979620877730887418867)
  ·
    refine ⟨49798469431316596331128301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33198979620877730887418867 49798469431316596331128301)
    ·
      refine ⟨18674426036743723624173113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49798469431316596331128301 18674426036743723624173113)
      ·
        refine ⟨14005819527557792718129835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18674426036743723624173113 14005819527557792718129835)
        ·
          refine ⟨21008729291336689077194753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14005819527557792718129835 21008729291336689077194753)
          ·
            refine ⟨15756546968502516807896065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21008729291336689077194753 15756546968502516807896065)
            ·
              refine ⟨11817410226376887605922049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15756546968502516807896065 11817410226376887605922049)
              ·
                refine ⟨8863057669782665704441537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11817410226376887605922049 8863057669782665704441537)
                ·
                  refine ⟨6647293252336999278331153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8863057669782665704441537 6647293252336999278331153)
                  ·
                    refine ⟨4985469939252749458748365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6647293252336999278331153 4985469939252749458748365)
                    ·
                      refine ⟨1869551227219781047030637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4985469939252749458748365 1869551227219781047030637)
                      ·
                        rfl

theorem cell23_3640938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_3640938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640938 prefixEnd_3640938 := by exact prefixLift 3640938
  have htrace : WordTrace (prefixWord ++ tailWord_3640938) baseStart_3640938 baseEnd_3640938 := by
    simpa [prefixWord, tailWord_3640938, baseEnd_3640938] using wordTrace_append hprefix tailTrace_3640938
  have hstable : (prefixWord ++ tailWord_3640938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640938).length < 2 ^ (prefixWord ++ tailWord_3640938).sum := by decide
  have hdescent : baseEnd_3640938 < baseStart_3640938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3640971 : List Nat := [1, 1, 1, 1, 4, 1, 4, 4, 1, 5]
def baseStart_3640971 : Nat := 118140960795 + 3640971 * 2 ^ 59
def prefixEnd_3640971 : Nat := 4983230072969 + 3 ^ 40 * 3640971 * 2
def baseEnd_3640971 : Nat := 623189390693793139305995

theorem tailTrace_3640971 : CollatzResearch.WordTrace tailWord_3640971 prefixEnd_3640971 623189390693793139305995 := by
  unfold tailWord_3640971
  simp only [CollatzResearch.WordTrace]
  refine ⟨132797122092391370185626767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88531414728260913457084511 132797122092391370185626767)
  ·
    refine ⟨199195683138587055278440151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132797122092391370185626767 199195683138587055278440151)
    ·
      refine ⟨298793524707880582917660227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199195683138587055278440151 298793524707880582917660227)
      ·
        refine ⟨448190287061820874376490341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298793524707880582917660227 448190287061820874376490341)
        ·
          refine ⟨84035678824091413945591939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 448190287061820874376490341 84035678824091413945591939)
          ·
            refine ⟨126053518236137120918387909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84035678824091413945591939 126053518236137120918387909)
            ·
              refine ⟨23635034669275710172197733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126053518236137120918387909 23635034669275710172197733)
              ·
                refine ⟨4431569000489195657287075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23635034669275710172197733 4431569000489195657287075)
                ·
                  refine ⟨6647353500733793485930613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431569000489195657287075 6647353500733793485930613)
                  ·
                    refine ⟨623189390693793139305995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6647353500733793485930613 623189390693793139305995)
                    ·
                      rfl

theorem cell23_3640971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 5].length) (baseStart_3640971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3640971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3640971 prefixEnd_3640971 := by exact prefixLift 3640971
  have htrace : WordTrace (prefixWord ++ tailWord_3640971) baseStart_3640971 baseEnd_3640971 := by
    simpa [prefixWord, tailWord_3640971, baseEnd_3640971] using wordTrace_append hprefix tailTrace_3640971
  have hstable : (prefixWord ++ tailWord_3640971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3640971).length < 2 ^ (prefixWord ++ tailWord_3640971).sum := by decide
  have hdescent : baseEnd_3640971 < baseStart_3640971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3640971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641011 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 5]
def baseStart_3641011 : Nat := 118140960795 + 3641011 * 2 ^ 59
def prefixEnd_3641011 : Nat := 4983230072969 + 3 ^ 40 * 3641011 * 2
def baseEnd_3641011 : Nat := 1869588711307559261417801

theorem tailTrace_3641011 : CollatzResearch.WordTrace tailWord_3641011 prefixEnd_3641011 1869588711307559261417801 := by
  unfold tailWord_3641011
  simp only [CollatzResearch.WordTrace]
  refine ⟨132798581012246457017082887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88532387341497638011388591 132798581012246457017082887)
  ·
    refine ⟨199197871518369685525624331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132798581012246457017082887 199197871518369685525624331)
    ·
      refine ⟨298796807277554528288436497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199197871518369685525624331 298796807277554528288436497)
      ·
        refine ⟨224097605458165896216327373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298796807277554528288436497 224097605458165896216327373)
        ·
          refine ⟨84036602046812211081122765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224097605458165896216327373 84036602046812211081122765)
          ·
            refine ⟨31513725767554579155421037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84036602046812211081122765 31513725767554579155421037)
            ·
              refine ⟨11817647162832967183282889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31513725767554579155421037 11817647162832967183282889)
              ·
                refine ⟨8863235372124725387462167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11817647162832967183282889 8863235372124725387462167)
                ·
                  refine ⟨13294853058187088081193251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8863235372124725387462167 13294853058187088081193251)
                  ·
                    refine ⟨19942279587280632121789877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13294853058187088081193251 19942279587280632121789877)
                    ·
                      refine ⟨1869588711307559261417801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19942279587280632121789877 1869588711307559261417801)
                      ·
                        rfl

theorem cell23_3641011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_3641011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641011 prefixEnd_3641011 := by exact prefixLift 3641011
  have htrace : WordTrace (prefixWord ++ tailWord_3641011) baseStart_3641011 baseEnd_3641011 := by
    simpa [prefixWord, tailWord_3641011, baseEnd_3641011] using wordTrace_append hprefix tailTrace_3641011
  have hstable : (prefixWord ++ tailWord_3641011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641011).length < 2 ^ (prefixWord ++ tailWord_3641011).sum := by decide
  have hdescent : baseEnd_3641011 < baseStart_3641011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641018 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 1, 6]
def baseStart_3641018 : Nat := 118140960795 + 3641018 * 2 ^ 59
def prefixEnd_3641018 : Nat := 4983230072969 + 3 ^ 40 * 3641018 * 2
def baseEnd_3641018 : Nat := 623197435224046911343423

theorem tailTrace_3641018 : CollatzResearch.WordTrace tailWord_3641018 prefixEnd_3641018 623197435224046911343423 := by
  unfold tailWord_3641018
  simp only [CollatzResearch.WordTrace]
  refine ⟨33199709080805274303146927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88532557548814064808391805 33199709080805274303146927)
  ·
    refine ⟨49799563621207911454720391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33199709080805274303146927 49799563621207911454720391)
    ·
      refine ⟨74699345431811867182080587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49799563621207911454720391 74699345431811867182080587)
      ·
        refine ⟨112049018147717800773120881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74699345431811867182080587 112049018147717800773120881)
        ·
          refine ⟨84036763610788350579840661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112049018147717800773120881 84036763610788350579840661)
          ·
            refine ⟨3939223294255703933430031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84036763610788350579840661 3939223294255703933430031)
            ·
              refine ⟨5908834941383555900145047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939223294255703933430031 5908834941383555900145047)
              ·
                refine ⟨8863252412075333850217571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5908834941383555900145047 8863252412075333850217571)
                ·
                  refine ⟨13294878618113000775326357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8863252412075333850217571 13294878618113000775326357)
                  ·
                    refine ⟨623197435224046911343423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13294878618113000775326357 623197435224046911343423)
                    ·
                      rfl

theorem cell23_3641018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_3641018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641018 prefixEnd_3641018 := by exact prefixLift 3641018
  have htrace : WordTrace (prefixWord ++ tailWord_3641018) baseStart_3641018 baseEnd_3641018 := by
    simpa [prefixWord, tailWord_3641018, baseEnd_3641018] using wordTrace_append hprefix tailTrace_3641018
  have hstable : (prefixWord ++ tailWord_3641018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641018).length < 2 ^ (prefixWord ++ tailWord_3641018).sum := by decide
  have hdescent : baseEnd_3641018 < baseStart_3641018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641021 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3641021 : Nat := 118140960795 + 3641021 * 2 ^ 59
def prefixEnd_3641021 : Nat := 4983230072969 + 3 ^ 40 * 3641021 * 2
def baseEnd_3641021 : Nat := 1869593846114104222292755

theorem tailTrace_3641021 : CollatzResearch.WordTrace tailWord_3641021 prefixEnd_3641021 1869593846114104222292755 := by
  unfold tailWord_3641021
  simp only [CollatzResearch.WordTrace]
  refine ⟨132798945742210228724946917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88532630494806819149964611 132798945742210228724946917)
  ·
    refine ⟨24899802326664417885927547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132798945742210228724946917 24899802326664417885927547)
    ·
      refine ⟨37349703489996626828891321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24899802326664417885927547 37349703489996626828891321)
      ·
        refine ⟨28012277617497470121668491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37349703489996626828891321 28012277617497470121668491)
        ·
          refine ⟨42018416426246205182502737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28012277617497470121668491 42018416426246205182502737)
          ·
            refine ⟨31513812319684653886877053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42018416426246205182502737 31513812319684653886877053)
            ·
              refine ⟨11817679619881745207578895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31513812319684653886877053 11817679619881745207578895)
              ·
                refine ⟨17726519429822617811368343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11817679619881745207578895 17726519429822617811368343)
                ·
                  refine ⟨26589779144733926717052515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17726519429822617811368343 26589779144733926717052515)
                  ·
                    refine ⟨39884668717100890075578773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26589779144733926717052515 39884668717100890075578773)
                    ·
                      refine ⟨1869593846114104222292755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39884668717100890075578773 1869593846114104222292755)
                      ·
                        rfl

theorem cell23_3641021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3641021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641021 prefixEnd_3641021 := by exact prefixLift 3641021
  have htrace : WordTrace (prefixWord ++ tailWord_3641021) baseStart_3641021 baseEnd_3641021 := by
    simpa [prefixWord, tailWord_3641021, baseEnd_3641021] using wordTrace_append hprefix tailTrace_3641021
  have hstable : (prefixWord ++ tailWord_3641021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641021).length < 2 ^ (prefixWord ++ tailWord_3641021).sum := by decide
  have hdescent : baseEnd_3641021 < baseStart_3641021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641036 : List Nat := [2, 2, 1, 5, 3, 1, 1, 3, 1, 1, 3]
def baseStart_3641036 : Nat := 118140960795 + 3641036 * 2 ^ 59
def prefixEnd_3641036 : Nat := 4983230072969 + 3 ^ 40 * 3641036 * 2
def baseEnd_3641036 : Nat := 1869601548323921663605187

theorem tailTrace_3641036 : CollatzResearch.WordTrace tailWord_3641036 prefixEnd_3641036 1869601548323921663605187 := by
  unfold tailWord_3641036
  simp only [CollatzResearch.WordTrace]
  refine ⟨66399746418577943143371481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88532995224770590857828641 66399746418577943143371481)
  ·
    refine ⟨49799809813933457357528611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66399746418577943143371481 49799809813933457357528611)
    ·
      refine ⟨74699714720900186036292917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49799809813933457357528611 74699714720900186036292917)
      ·
        refine ⟨7003098255084392440902461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74699714720900186036292917 7003098255084392440902461)
        ·
          refine ⟨2626161845656647165338423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7003098255084392440902461 2626161845656647165338423)
          ·
            refine ⟨3939242768484970748007635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626161845656647165338423 3939242768484970748007635)
            ·
              refine ⟨5908864152727456122011453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939242768484970748007635 5908864152727456122011453)
              ·
                refine ⟨2215824057272796045754295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5908864152727456122011453 2215824057272796045754295)
                ·
                  refine ⟨3323736085909194068631443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2215824057272796045754295 3323736085909194068631443)
                  ·
                    refine ⟨4985604128863791102947165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3323736085909194068631443 4985604128863791102947165)
                    ·
                      refine ⟨1869601548323921663605187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4985604128863791102947165 1869601548323921663605187)
                      ·
                        rfl

theorem cell23_3641036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_3641036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641036 prefixEnd_3641036 := by exact prefixLift 3641036
  have htrace : WordTrace (prefixWord ++ tailWord_3641036) baseStart_3641036 baseEnd_3641036 := by
    simpa [prefixWord, tailWord_3641036, baseEnd_3641036] using wordTrace_append hprefix tailTrace_3641036
  have hstable : (prefixWord ++ tailWord_3641036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641036).length < 2 ^ (prefixWord ++ tailWord_3641036).sum := by decide
  have hdescent : baseEnd_3641036 < baseStart_3641036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641059 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 3, 2, 2]
def baseStart_3641059 : Nat := 118140960795 + 3641059 * 2 ^ 59
def prefixEnd_3641059 : Nat := 4983230072969 + 3 ^ 40 * 3641059 * 2
def baseEnd_3641059 : Nat := 1869613358378975073617581

theorem tailTrace_3641059 : CollatzResearch.WordTrace tailWord_3641059 prefixEnd_3641059 1869613358378975073617581 := by
  unfold tailWord_3641059
  simp only [CollatzResearch.WordTrace]
  refine ⟨132800331716072561214830231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88533554477381707476553487 132800331716072561214830231)
  ·
    refine ⟨199200497574108841822245347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132800331716072561214830231 199200497574108841822245347)
    ·
      refine ⟨298800746361163262733368021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199200497574108841822245347 298800746361163262733368021)
      ·
        refine ⟨7003142492839763970313313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 298800746361163262733368021 7003142492839763970313313)
        ·
          refine ⟨5252356869629822977734985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7003142492839763970313313 5252356869629822977734985)
          ·
            refine ⟨3939267652222367233301239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5252356869629822977734985 3939267652222367233301239)
            ·
              refine ⟨5908901478333550849951859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939267652222367233301239 5908901478333550849951859)
              ·
                refine ⟨8863352217500326274927789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5908901478333550849951859 8863352217500326274927789)
                ·
                  refine ⟨3323757081562622353097921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8863352217500326274927789 3323757081562622353097921)
                  ·
                    refine ⟨2492817811171966764823441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3323757081562622353097921 2492817811171966764823441)
                    ·
                      refine ⟨1869613358378975073617581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2492817811171966764823441 1869613358378975073617581)
                      ·
                        rfl

theorem cell23_3641059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_3641059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641059 prefixEnd_3641059 := by exact prefixLift 3641059
  have htrace : WordTrace (prefixWord ++ tailWord_3641059) baseStart_3641059 baseEnd_3641059 := by
    simpa [prefixWord, tailWord_3641059, baseEnd_3641059] using wordTrace_append hprefix tailTrace_3641059
  have hstable : (prefixWord ++ tailWord_3641059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641059).length < 2 ^ (prefixWord ++ tailWord_3641059).sum := by decide
  have hdescent : baseEnd_3641059 < baseStart_3641059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641061 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 2, 7]
def baseStart_3641061 : Nat := 118140960795 + 3641061 * 2 ^ 59
def prefixEnd_3641061 : Nat := 4983230072969 + 3 ^ 40 * 3641061 * 2
def baseEnd_3641061 : Nat := 623204795113428021930857

theorem tailTrace_3641061 : CollatzResearch.WordTrace tailWord_3641061 prefixEnd_3641061 623204795113428021930857 := by
  unfold tailWord_3641061
  simp only [CollatzResearch.WordTrace]
  refine ⟨132800404662065315556403037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88533603108043543704268691 132800404662065315556403037)
  ·
    refine ⟨49800151748274493333651139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132800404662065315556403037 49800151748274493333651139)
    ·
      refine ⟨74700227622411740000476709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49800151748274493333651139 74700227622411740000476709)
      ·
        refine ⟨14006292679202201250089383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74700227622411740000476709 14006292679202201250089383)
        ·
          refine ⟨21009439018803301875134075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14006292679202201250089383 21009439018803301875134075)
          ·
            refine ⟨31514158528204952812701113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21009439018803301875134075 31514158528204952812701113)
            ·
              refine ⟨23635618896153714609525835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31514158528204952812701113 23635618896153714609525835)
              ·
                refine ⟨35453428344230571914288753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23635618896153714609525835 35453428344230571914288753)
                ·
                  refine ⟨26590071258172928935716565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35453428344230571914288753 26590071258172928935716565)
                  ·
                    refine ⟨623204795113428021930857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26590071258172928935716565 623204795113428021930857)
                    ·
                      rfl

theorem cell23_3641061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_3641061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641061 prefixEnd_3641061 := by exact prefixLift 3641061
  have htrace : WordTrace (prefixWord ++ tailWord_3641061) baseStart_3641061 baseEnd_3641061 := by
    simpa [prefixWord, tailWord_3641061, baseEnd_3641061] using wordTrace_append hprefix tailTrace_3641061
  have hstable : (prefixWord ++ tailWord_3641061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641061).length < 2 ^ (prefixWord ++ tailWord_3641061).sum := by decide
  have hdescent : baseEnd_3641061 < baseStart_3641061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641085 : List Nat := [1, 4, 1, 1, 1, 1, 2, 6, 1, 3, 2]
def baseStart_3641085 : Nat := 118140960795 + 3641085 * 2 ^ 59
def prefixEnd_3641085 : Nat := 4983230072969 + 3 ^ 40 * 3641085 * 2
def baseEnd_3641085 : Nat := 1869626708875991971892461

theorem tailTrace_3641085 : CollatzResearch.WordTrace tailWord_3641085 prefixEnd_3641085 1869626708875991971892461 := by
  unfold tailWord_3641085
  simp only [CollatzResearch.WordTrace]
  refine ⟨132801280013978367655276709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88534186675985578436851139 132801280013978367655276709)
  ·
    refine ⟨24900240002620943935364383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132801280013978367655276709 24900240002620943935364383)
    ·
      refine ⟨37350360003931415903046575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24900240002620943935364383 37350360003931415903046575)
      ·
        refine ⟨56025540005897123854569863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37350360003931415903046575 56025540005897123854569863)
        ·
          refine ⟨84038310008845685781854795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56025540005897123854569863 84038310008845685781854795)
          ·
            refine ⟨126057465013268528672782193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84038310008845685781854795 126057465013268528672782193)
            ·
              refine ⟨94543098759951396504586645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126057465013268528672782193 94543098759951396504586645)
              ·
                refine ⟨4431707754372721711152499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94543098759951396504586645 4431707754372721711152499)
                ·
                  refine ⟨6647561631559082566728749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4431707754372721711152499 6647561631559082566728749)
                  ·
                    refine ⟨2492835611834655962523281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6647561631559082566728749 2492835611834655962523281)
                    ·
                      refine ⟨1869626708875991971892461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2492835611834655962523281 1869626708875991971892461)
                      ·
                        rfl

theorem cell23_3641085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_3641085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641085 prefixEnd_3641085 := by exact prefixLift 3641085
  have htrace : WordTrace (prefixWord ++ tailWord_3641085) baseStart_3641085 baseEnd_3641085 := by
    simpa [prefixWord, tailWord_3641085, baseEnd_3641085] using wordTrace_append hprefix tailTrace_3641085
  have hstable : (prefixWord ++ tailWord_3641085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641085).length < 2 ^ (prefixWord ++ tailWord_3641085).sum := by decide
  have hdescent : baseEnd_3641085 < baseStart_3641085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641128 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3641128 : Nat := 118140960795 + 3641128 * 2 ^ 59
def prefixEnd_3641128 : Nat := 4983230072969 + 3 ^ 40 * 3641128 * 2
def baseEnd_3641128 : Nat := 1869648788544135303654763

theorem tailTrace_3641128 : CollatzResearch.WordTrace tailWord_3641128 prefixEnd_3641128 1869648788544135303654763 := by
  unfold tailWord_3641128
  simp only [CollatzResearch.WordTrace]
  refine ⟨66401424176411292999546019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88535232235215057332728025 66401424176411292999546019)
  ·
    refine ⟨99602136264616939499319029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66401424176411292999546019 99602136264616939499319029)
    ·
      refine ⟨9337700274807838078061159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99602136264616939499319029 9337700274807838078061159)
      ·
        refine ⟨14006550412211757117091739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9337700274807838078061159 14006550412211757117091739)
        ·
          refine ⟨21009825618317635675637609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14006550412211757117091739 21009825618317635675637609)
          ·
            refine ⟨15757369213738226756728207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21009825618317635675637609 15757369213738226756728207)
            ·
              refine ⟨23636053820607340135092311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15757369213738226756728207 23636053820607340135092311)
              ·
                refine ⟨35454080730911010202638467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23636053820607340135092311 35454080730911010202638467)
                ·
                  refine ⟨53181121096366515303957701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35454080730911010202638467 53181121096366515303957701)
                  ·
                    refine ⟨9971460205568721619492069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53181121096366515303957701 9971460205568721619492069)
                    ·
                      refine ⟨1869648788544135303654763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9971460205568721619492069 1869648788544135303654763)
                      ·
                        rfl

theorem cell23_3641128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3641128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641128 prefixEnd_3641128 := by exact prefixLift 3641128
  have htrace : WordTrace (prefixWord ++ tailWord_3641128) baseStart_3641128 baseEnd_3641128 := by
    simpa [prefixWord, tailWord_3641128, baseEnd_3641128] using wordTrace_append hprefix tailTrace_3641128
  have hstable : (prefixWord ++ tailWord_3641128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641128).length < 2 ^ (prefixWord ++ tailWord_3641128).sum := by decide
  have hdescent : baseEnd_3641128 < baseStart_3641128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641132 : List Nat := [2, 2, 1, 1, 1, 5, 2, 3, 2, 2, 2]
def baseStart_3641132 : Nat := 118140960795 + 3641132 * 2 ^ 59
def prefixEnd_3641132 : Nat := 4983230072969 + 3 ^ 40 * 3641132 * 2
def baseEnd_3641132 : Nat := 1869650842466753288004745

theorem tailTrace_3641132 : CollatzResearch.WordTrace tailWord_3641132 prefixEnd_3641132 1869650842466753288004745 := by
  unfold tailWord_3641132
  simp only [CollatzResearch.WordTrace]
  refine ⟨66401497122404047341118825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88535329496538729788158433 66401497122404047341118825)
  ·
    refine ⟨49801122841803035505839119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66401497122404047341118825 49801122841803035505839119)
    ·
      refine ⟨74701684262704553258758679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49801122841803035505839119 74701684262704553258758679)
      ·
        refine ⟨112052526394056829888138019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74701684262704553258758679 112052526394056829888138019)
        ·
          refine ⟨168078789591085244832207029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112052526394056829888138019 168078789591085244832207029)
          ·
            refine ⟨15757386524164241703019409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168078789591085244832207029 15757386524164241703019409)
            ·
              refine ⟨11818039893123181277264557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15757386524164241703019409 11818039893123181277264557)
              ·
                refine ⟨4431764959921192978974209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11818039893123181277264557 4431764959921192978974209)
                ·
                  refine ⟨3323823719940894734230657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4431764959921192978974209 3323823719940894734230657)
                  ·
                    refine ⟨2492867789955671050672993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3323823719940894734230657 2492867789955671050672993)
                    ·
                      refine ⟨1869650842466753288004745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2492867789955671050672993 1869650842466753288004745)
                      ·
                        rfl

theorem cell23_3641132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 2, 2].length) (baseStart_3641132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641132 prefixEnd_3641132 := by exact prefixLift 3641132
  have htrace : WordTrace (prefixWord ++ tailWord_3641132) baseStart_3641132 baseEnd_3641132 := by
    simpa [prefixWord, tailWord_3641132, baseEnd_3641132] using wordTrace_append hprefix tailTrace_3641132
  have hstable : (prefixWord ++ tailWord_3641132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641132).length < 2 ^ (prefixWord ++ tailWord_3641132).sum := by decide
  have hdescent : baseEnd_3641132 < baseStart_3641132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641138 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 7]
def baseStart_3641138 : Nat := 118140960795 + 3641138 * 2 ^ 59
def prefixEnd_3641138 : Nat := 4983230072969 + 3 ^ 40 * 3641138 * 2
def baseEnd_3641138 : Nat := 207739324816742251614413

theorem tailTrace_3641138 : CollatzResearch.WordTrace tailWord_3641138 prefixEnd_3641138 207739324816742251614413 := by
  unfold tailWord_3641138
  simp only [CollatzResearch.WordTrace]
  refine ⟨33200803270696589426739017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88535475388524238471304045 33200803270696589426739017)
  ·
    refine ⟨24900602453022442070054263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33200803270696589426739017 24900602453022442070054263)
    ·
      refine ⟨37350903679533663105081395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24900602453022442070054263 37350903679533663105081395)
      ·
        refine ⟨56026355519300494657622093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37350903679533663105081395 56026355519300494657622093)
        ·
          refine ⟨21009883319737685496608285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56026355519300494657622093 21009883319737685496608285)
          ·
            refine ⟨7878706244901632061228107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21009883319737685496608285 7878706244901632061228107)
            ·
              refine ⟨11818059367352448091842161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7878706244901632061228107 11818059367352448091842161)
              ·
                refine ⟨8863544525514336068881621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11818059367352448091842161 8863544525514336068881621)
                ·
                  refine ⟨207739324816742251614413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8863544525514336068881621 207739324816742251614413)
                  ·
                    rfl

theorem cell23_3641138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_3641138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641138 prefixEnd_3641138 := by exact prefixLift 3641138
  have htrace : WordTrace (prefixWord ++ tailWord_3641138) baseStart_3641138 baseEnd_3641138 := by
    simpa [prefixWord, tailWord_3641138, baseEnd_3641138] using wordTrace_append hprefix tailTrace_3641138
  have hstable : (prefixWord ++ tailWord_3641138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641138).length < 2 ^ (prefixWord ++ tailWord_3641138).sum := by decide
  have hdescent : baseEnd_3641138 < baseStart_3641138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641155 : List Nat := [1, 1, 1, 3, 1, 6, 2, 3, 5]
def baseStart_3641155 : Nat := 118140960795 + 3641155 * 2 ^ 59
def prefixEnd_3641155 : Nat := 4983230072969 + 3 ^ 40 * 3641155 * 2
def baseEnd_3641155 : Nat := 207740294724645188668571

theorem tailTrace_3641155 : CollatzResearch.WordTrace tailWord_3641155 prefixEnd_3641155 207740294724645188668571 := by
  unfold tailWord_3641155
  simp only [CollatzResearch.WordTrace]
  refine ⟨132803833123724769610324919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88535888749149846406883279 132803833123724769610324919)
  ·
    refine ⟨199205749685587154415487379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132803833123724769610324919 199205749685587154415487379)
    ·
      refine ⟨298808624528380731623231069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199205749685587154415487379 298808624528380731623231069)
      ·
        refine ⟨112053234198142774358711651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298808624528380731623231069 112053234198142774358711651)
        ·
          refine ⟨168079851297214161538067477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112053234198142774358711651 168079851297214161538067477)
          ·
            refine ⟨7878743029556913822096913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168079851297214161538067477 7878743029556913822096913)
            ·
              refine ⟨5909057272167685366572685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7878743029556913822096913 5909057272167685366572685)
              ·
                refine ⟨2215896477062882012464757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5909057272167685366572685 2215896477062882012464757)
                ·
                  refine ⟨207740294724645188668571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2215896477062882012464757 207740294724645188668571)
                  ·
                    rfl

theorem cell23_3641155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 5].length) (baseStart_3641155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641155 prefixEnd_3641155 := by exact prefixLift 3641155
  have htrace : WordTrace (prefixWord ++ tailWord_3641155) baseStart_3641155 baseEnd_3641155 := by
    simpa [prefixWord, tailWord_3641155, baseEnd_3641155] using wordTrace_append hprefix tailTrace_3641155
  have hstable : (prefixWord ++ tailWord_3641155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641155).length < 2 ^ (prefixWord ++ tailWord_3641155).sum := by decide
  have hdescent : baseEnd_3641155 < baseStart_3641155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641205 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3641205 : Nat := 118140960795 + 3641205 * 2 ^ 59
def prefixEnd_3641205 : Nat := 4983230072969 + 3 ^ 40 * 3641205 * 2
def baseEnd_3641205 : Nat := 1869688326554531502391909

theorem tailTrace_3641205 : CollatzResearch.WordTrace tailWord_3641205 prefixEnd_3641205 1869688326554531502391909 := by
  unfold tailWord_3641205
  simp only [CollatzResearch.WordTrace]
  refine ⟨132805656773543628149645069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88537104515695752099763379 132805656773543628149645069)
  ·
    refine ⟨49802121290078860556116901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132805656773543628149645069 49802121290078860556116901)
    ·
      refine ⟨9337897741889786354271919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49802121290078860556116901 9337897741889786354271919)
      ·
        refine ⟨14006846612834679531407879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9337897741889786354271919 14006846612834679531407879)
        ·
          refine ⟨21010269919252019297111819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14006846612834679531407879 21010269919252019297111819)
          ·
            refine ⟨31515404878878028945667729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21010269919252019297111819 31515404878878028945667729)
            ·
              refine ⟨23636553659158521709250797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31515404878878028945667729 23636553659158521709250797)
              ·
                refine ⟨8863707622184445640969049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23636553659158521709250797 8863707622184445640969049)
                ·
                  refine ⟨6647780716638334230726787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8863707622184445640969049 6647780716638334230726787)
                  ·
                    refine ⟨9971671074957501346090181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6647780716638334230726787 9971671074957501346090181)
                    ·
                      refine ⟨1869688326554531502391909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9971671074957501346090181 1869688326554531502391909)
                      ·
                        rfl

theorem cell23_3641205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3641205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641205 prefixEnd_3641205 := by exact prefixLift 3641205
  have htrace : WordTrace (prefixWord ++ tailWord_3641205) baseStart_3641205 baseEnd_3641205 := by
    simpa [prefixWord, tailWord_3641205, baseEnd_3641205] using wordTrace_append hprefix tailTrace_3641205
  have hstable : (prefixWord ++ tailWord_3641205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641205).length < 2 ^ (prefixWord ++ tailWord_3641205).sum := by decide
  have hdescent : baseEnd_3641205 < baseStart_3641205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641206 : List Nat := [5, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_3641206 : Nat := 118140960795 + 3641206 * 2 ^ 59
def prefixEnd_3641206 : Nat := 4983230072969 + 3 ^ 40 * 3641206 * 2
def baseEnd_3641206 : Nat := 207743204448353999831045

theorem tailTrace_3641206 : CollatzResearch.WordTrace tailWord_3641206 prefixEnd_3641206 207743204448353999831045 := by
  unfold tailWord_3641206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8300355827908750332526967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88537128831026670213620981 8300355827908750332526967)
  ·
    refine ⟨12450533741863125498790451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8300355827908750332526967 12450533741863125498790451)
    ·
      refine ⟨18675800612794688248185677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12450533741863125498790451 18675800612794688248185677)
      ·
        refine ⟨7003425229798008093069629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18675800612794688248185677 7003425229798008093069629)
        ·
          refine ⟨2626284461174253034901111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7003425229798008093069629 2626284461174253034901111)
          ·
            refine ⟨3939426691761379552351667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626284461174253034901111 3939426691761379552351667)
            ·
              refine ⟨5909140037642069328527501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939426691761379552351667 5909140037642069328527501)
              ·
                refine ⟨2215927514115775998197813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5909140037642069328527501 2215927514115775998197813)
                ·
                  refine ⟨207743204448353999831045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2215927514115775998197813 207743204448353999831045)
                  ·
                    rfl

theorem cell23_3641206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_3641206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641206 prefixEnd_3641206 := by exact prefixLift 3641206
  have htrace : WordTrace (prefixWord ++ tailWord_3641206) baseStart_3641206 baseEnd_3641206 := by
    simpa [prefixWord, tailWord_3641206, baseEnd_3641206] using wordTrace_append hprefix tailTrace_3641206
  have hstable : (prefixWord ++ tailWord_3641206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641206).length < 2 ^ (prefixWord ++ tailWord_3641206).sum := by decide
  have hdescent : baseEnd_3641206 < baseStart_3641206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641225 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 2, 2, 3]
def baseStart_3641225 : Nat := 118140960795 + 3641225 * 2 ^ 59
def prefixEnd_3641225 : Nat := 4983230072969 + 3 ^ 40 * 3641225 * 2
def baseEnd_3641225 : Nat := 1869698596167621424141817

theorem tailTrace_3641225 : CollatzResearch.WordTrace tailWord_3641225 prefixEnd_3641225 1869698596167621424141817 := by
  unfold tailWord_3641225
  simp only [CollatzResearch.WordTrace]
  refine ⟨132806386233471171565373129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88537590822314114376915419 132806386233471171565373129)
  ·
    refine ⟨99604789675103378674029847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132806386233471171565373129 99604789675103378674029847)
    ·
      refine ⟨149407184512655068011044771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99604789675103378674029847 149407184512655068011044771)
      ·
        refine ⟨224110776768982602016567157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149407184512655068011044771 224110776768982602016567157)
        ·
          refine ⟨21010385322092118939053171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224110776768982602016567157 21010385322092118939053171)
          ·
            refine ⟨31515577983138178408579757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21010385322092118939053171 31515577983138178408579757)
            ·
              refine ⟨11818341743676816903217409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31515577983138178408579757 11818341743676816903217409)
              ·
                refine ⟨8863756307757612677413057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11818341743676816903217409 8863756307757612677413057)
                ·
                  refine ⟨6647817230818209508059793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8863756307757612677413057 6647817230818209508059793)
                  ·
                    refine ⟨4985862923113657131044845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6647817230818209508059793 4985862923113657131044845)
                    ·
                      refine ⟨1869698596167621424141817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4985862923113657131044845 1869698596167621424141817)
                      ·
                        rfl

theorem cell23_3641225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 2, 3].length) (baseStart_3641225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641225 prefixEnd_3641225 := by exact prefixLift 3641225
  have htrace : WordTrace (prefixWord ++ tailWord_3641225) baseStart_3641225 baseEnd_3641225 := by
    simpa [prefixWord, tailWord_3641225, baseEnd_3641225] using wordTrace_append hprefix tailTrace_3641225
  have hstable : (prefixWord ++ tailWord_3641225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641225).length < 2 ^ (prefixWord ++ tailWord_3641225).sum := by decide
  have hdescent : baseEnd_3641225 < baseStart_3641225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641228 : List Nat := [2, 2, 1, 2, 1, 2, 1, 6, 6]
def baseStart_3641228 : Nat := 118140960795 + 3641228 * 2 ^ 59
def prefixEnd_3641228 : Nat := 4983230072969 + 3 ^ 40 * 3641228 * 2
def baseEnd_3641228 : Nat := 207744459623287212489367

theorem tailTrace_3641228 : CollatzResearch.WordTrace tailWord_3641228 prefixEnd_3641228 207744459623287212489367 := by
  unfold tailWord_3641228
  simp only [CollatzResearch.WordTrace]
  refine ⟨66403247826230151538866169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88537663768306868718488225 66403247826230151538866169)
  ·
    refine ⟨49802435869672613654149627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66403247826230151538866169 49802435869672613654149627)
    ·
      refine ⟨74703653804508920481224441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49802435869672613654149627 74703653804508920481224441)
      ·
        refine ⟨56027740353381690360918331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74703653804508920481224441 56027740353381690360918331)
        ·
          refine ⟨84041610530072535541377497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56027740353381690360918331 84041610530072535541377497)
          ·
            refine ⟨63031207897554401656033123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84041610530072535541377497 63031207897554401656033123)
            ·
              refine ⟨94546811846331602484049685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63031207897554401656033123 94546811846331602484049685)
              ·
                refine ⟨4431881805296793866439829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94546811846331602484049685 4431881805296793866439829)
                ·
                  refine ⟨207744459623287212489367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4431881805296793866439829 207744459623287212489367)
                  ·
                    rfl

theorem cell23_3641228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 6].length) (baseStart_3641228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641228 prefixEnd_3641228 := by exact prefixLift 3641228
  have htrace : WordTrace (prefixWord ++ tailWord_3641228) baseStart_3641228 baseEnd_3641228 := by
    simpa [prefixWord, tailWord_3641228, baseEnd_3641228] using wordTrace_append hprefix tailTrace_3641228
  have hstable : (prefixWord ++ tailWord_3641228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641228).length < 2 ^ (prefixWord ++ tailWord_3641228).sum := by decide
  have hdescent : baseEnd_3641228 < baseStart_3641228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641245 : List Nat := [1, 4, 2, 1, 2, 3, 1, 3, 6]
def baseStart_3641245 : Nat := 118140960795 + 3641245 * 2 ^ 59
def prefixEnd_3641245 : Nat := 4983230072969 + 3 ^ 40 * 3641245 * 2
def baseEnd_3641245 : Nat := 207745429531190149543525

theorem tailTrace_3641245 : CollatzResearch.WordTrace tailWord_3641245 prefixEnd_3641245 207745429531190149543525 := by
  unfold tailWord_3641245
  simp only [CollatzResearch.WordTrace]
  refine ⟨132807115693398714981101189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88538077128932476654067459 132807115693398714981101189)
  ·
    refine ⟨24901334192512259058956473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132807115693398714981101189 24901334192512259058956473)
    ·
      refine ⟨18676000644384194294217355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24901334192512259058956473 18676000644384194294217355)
      ·
        refine ⟨28014000966576291441326033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18676000644384194294217355 28014000966576291441326033)
        ·
          refine ⟨21010500724932218580994525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28014000966576291441326033 21010500724932218580994525)
          ·
            refine ⟨7878937771849581967872947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21010500724932218580994525 7878937771849581967872947)
            ·
              refine ⟨11818406657774372951809421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7878937771849581967872947 11818406657774372951809421)
              ·
                refine ⟨4431902496665389856928533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11818406657774372951809421 4431902496665389856928533)
                ·
                  refine ⟨207745429531190149543525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4431902496665389856928533 207745429531190149543525)
                  ·
                    rfl

theorem cell23_3641245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_3641245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641245 prefixEnd_3641245 := by exact prefixLift 3641245
  have htrace : WordTrace (prefixWord ++ tailWord_3641245) baseStart_3641245 baseEnd_3641245 := by
    simpa [prefixWord, tailWord_3641245, baseEnd_3641245] using wordTrace_append hprefix tailTrace_3641245
  have hstable : (prefixWord ++ tailWord_3641245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641245).length < 2 ^ (prefixWord ++ tailWord_3641245).sum := by decide
  have hdescent : baseEnd_3641245 < baseStart_3641245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641338 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_3641338 : Nat := 118140960795 + 3641338 * 2 ^ 59
def prefixEnd_3641338 : Nat := 4983230072969 + 3 ^ 40 * 3641338 * 2
def baseEnd_3641338 : Nat := 1869756619481579482028797

theorem tailTrace_3641338 : CollatzResearch.WordTrace tailWord_3641338 prefixEnd_3641338 1869756619481579482028797 := by
  unfold tailWord_3641338
  simp only [CollatzResearch.WordTrace]
  refine ⟨33202626920515447966059167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88540338454707861242824445 33202626920515447966059167)
  ·
    refine ⟨49803940380773171949088751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33202626920515447966059167 49803940380773171949088751)
    ·
      refine ⟨74705910571159757923633127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49803940380773171949088751 74705910571159757923633127)
      ·
        refine ⟨112058865856739636885449691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74705910571159757923633127 112058865856739636885449691)
        ·
          refine ⟨168088298785109455328174537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112058865856739636885449691 168088298785109455328174537)
          ·
            refine ⟨126066224088832091496130903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168088298785109455328174537 126066224088832091496130903)
            ·
              refine ⟨189099336133248137244196355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126066224088832091496130903 189099336133248137244196355)
              ·
                refine ⟨283649004199872205866294533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189099336133248137244196355 283649004199872205866294533)
                ·
                  refine ⟨53184188287476038599930225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 283649004199872205866294533 53184188287476038599930225)
                  ·
                    refine ⟨39888141215607028949947669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53184188287476038599930225 39888141215607028949947669)
                    ·
                      refine ⟨1869756619481579482028797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39888141215607028949947669 1869756619481579482028797)
                      ·
                        rfl

theorem cell23_3641338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_3641338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641338 prefixEnd_3641338 := by exact prefixLift 3641338
  have htrace : WordTrace (prefixWord ++ tailWord_3641338) baseStart_3641338 baseEnd_3641338 := by
    simpa [prefixWord, tailWord_3641338, baseEnd_3641338] using wordTrace_append hprefix tailTrace_3641338
  have hstable : (prefixWord ++ tailWord_3641338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641338).length < 2 ^ (prefixWord ++ tailWord_3641338).sum := by decide
  have hdescent : baseEnd_3641338 < baseStart_3641338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641380 : List Nat := [2, 3, 1, 4, 2, 2, 1, 3, 1, 2, 2]
def baseStart_3641380 : Nat := 118140960795 + 3641380 * 2 ^ 59
def prefixEnd_3641380 : Nat := 4983230072969 + 3 ^ 40 * 3641380 * 2
def baseEnd_3641380 : Nat := 1869778185669068317703605

theorem tailTrace_3641380 : CollatzResearch.WordTrace tailWord_3641380 prefixEnd_3641380 1869778185669068317703605 := by
  unfold tailWord_3641380
  simp only [CollatzResearch.WordTrace]
  refine ⟨66406019773954816518632797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88541359698606422024843729 66406019773954816518632797)
  ·
    refine ⟨24902257415233056194487299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66406019773954816518632797 24902257415233056194487299)
    ·
      refine ⟨37353386122849584291730949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24902257415233056194487299 37353386122849584291730949)
      ·
        refine ⟨7003759898034297054699553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37353386122849584291730949 7003759898034297054699553)
        ·
          refine ⟨5252819923525722791024665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7003759898034297054699553 5252819923525722791024665)
          ·
            refine ⟨3939614942644292093268499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5252819923525722791024665 3939614942644292093268499)
            ·
              refine ⟨5909422413966438139902749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939614942644292093268499 5909422413966438139902749)
              ·
                refine ⟨2216033405237414302463531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5909422413966438139902749 2216033405237414302463531)
                ·
                  refine ⟨3324050107856121453695297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216033405237414302463531 3324050107856121453695297)
                  ·
                    refine ⟨2493037580892091090271473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3324050107856121453695297 2493037580892091090271473)
                    ·
                      refine ⟨1869778185669068317703605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2493037580892091090271473 1869778185669068317703605)
                      ·
                        rfl

theorem cell23_3641380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_3641380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641380 prefixEnd_3641380 := by exact prefixLift 3641380
  have htrace : WordTrace (prefixWord ++ tailWord_3641380) baseStart_3641380 baseEnd_3641380 := by
    simpa [prefixWord, tailWord_3641380, baseEnd_3641380] using wordTrace_append hprefix tailTrace_3641380
  have hstable : (prefixWord ++ tailWord_3641380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641380).length < 2 ^ (prefixWord ++ tailWord_3641380).sum := by decide
  have hdescent : baseEnd_3641380 < baseStart_3641380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641405 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3641405 : Nat := 118140960795 + 3641405 * 2 ^ 59
def prefixEnd_3641405 : Nat := 4983230072969 + 3 ^ 40 * 3641405 * 2
def baseEnd_3641405 : Nat := 1869791022685430719890989

theorem tailTrace_3641405 : CollatzResearch.WordTrace tailWord_3641405 prefixEnd_3641405 1869791022685430719890989 := by
  unfold tailWord_3641405
  simp only [CollatzResearch.WordTrace]
  refine ⟨132812951372819062306925669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88541967581879374871283779 132812951372819062306925669)
  ·
    refine ⟨24902428382403574182548563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132812951372819062306925669 24902428382403574182548563)
    ·
      refine ⟨37353642573605361273822845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24902428382403574182548563 37353642573605361273822845)
      ·
        refine ⟨14007615965102010477683567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37353642573605361273822845 14007615965102010477683567)
        ·
          refine ⟨21011423947653015716525351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14007615965102010477683567 21011423947653015716525351)
          ·
            refine ⟨31517135921479523574788027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21011423947653015716525351 31517135921479523574788027)
            ·
              refine ⟨47275703882219285362182041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31517135921479523574788027 47275703882219285362182041)
              ·
                refine ⟨35456777911664464021636531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47275703882219285362182041 35456777911664464021636531)
                ·
                  refine ⟨53185166867496696032454797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35456777911664464021636531 53185166867496696032454797)
                  ·
                    refine ⟨19944437575311261012170549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53185166867496696032454797 19944437575311261012170549)
                    ·
                      refine ⟨1869791022685430719890989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19944437575311261012170549 1869791022685430719890989)
                      ·
                        rfl

theorem cell23_3641405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3641405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641405 prefixEnd_3641405 := by exact prefixLift 3641405
  have htrace : WordTrace (prefixWord ++ tailWord_3641405) baseStart_3641405 baseEnd_3641405 := by
    simpa [prefixWord, tailWord_3641405, baseEnd_3641405] using wordTrace_append hprefix tailTrace_3641405
  have hstable : (prefixWord ++ tailWord_3641405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641405).length < 2 ^ (prefixWord ++ tailWord_3641405).sum := by decide
  have hdescent : baseEnd_3641405 < baseStart_3641405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641415 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_3641415 : Nat := 118140960795 + 3641415 * 2 ^ 59
def prefixEnd_3641415 : Nat := 4983230072969 + 3 ^ 40 * 3641415 * 2
def baseEnd_3641415 : Nat := 1869796157491975680765943

theorem tailTrace_3641415 : CollatzResearch.WordTrace tailWord_3641415 prefixEnd_3641415 1869796157491975680765943 := by
  unfold tailWord_3641415
  simp only [CollatzResearch.WordTrace]
  refine ⟨132813316102782834014789699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88542210735188556009859799 132813316102782834014789699)
  ·
    refine ⟨199219974154174251022184549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132813316102782834014789699 199219974154174251022184549)
    ·
      refine ⟨37353745153907672066659603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199219974154174251022184549 37353745153907672066659603)
      ·
        refine ⟨56030617730861508099989405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37353745153907672066659603 56030617730861508099989405)
        ·
          refine ⟨21011481649073065537496027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56030617730861508099989405 21011481649073065537496027)
          ·
            refine ⟨31517222473609598306244041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21011481649073065537496027 31517222473609598306244041)
            ·
              refine ⟨23637916855207198729683031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31517222473609598306244041 23637916855207198729683031)
              ·
                refine ⟨35456875282810798094524547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23637916855207198729683031 35456875282810798094524547)
                ·
                  refine ⟨53185312924216197141786821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35456875282810798094524547 53185312924216197141786821)
                  ·
                    refine ⟨9972246173290536964085029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53185312924216197141786821 9972246173290536964085029)
                    ·
                      refine ⟨1869796157491975680765943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9972246173290536964085029 1869796157491975680765943)
                      ·
                        rfl

theorem cell23_3641415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_3641415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641415 prefixEnd_3641415 := by exact prefixLift 3641415
  have htrace : WordTrace (prefixWord ++ tailWord_3641415) baseStart_3641415 baseEnd_3641415 := by
    simpa [prefixWord, tailWord_3641415, baseEnd_3641415] using wordTrace_append hprefix tailTrace_3641415
  have hstable : (prefixWord ++ tailWord_3641415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641415).length < 2 ^ (prefixWord ++ tailWord_3641415).sum := by decide
  have hdescent : baseEnd_3641415 < baseStart_3641415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641419 : List Nat := [1, 1, 1, 1, 3, 1, 2, 7, 2, 2, 2]
def baseStart_3641419 : Nat := 118140960795 + 3641419 * 2 ^ 59
def prefixEnd_3641419 : Nat := 4983230072969 + 3 ^ 40 * 3641419 * 2
def baseEnd_3641419 : Nat := 1869798211414593665115925

theorem tailTrace_3641419 : CollatzResearch.WordTrace tailWord_3641419 prefixEnd_3641419 1869798211414593665115925 := by
  unfold tailWord_3641419
  simp only [CollatzResearch.WordTrace]
  refine ⟨132813461994768342697935311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88542307996512228465290207 132813461994768342697935311)
  ·
    refine ⟨199220192992152514046902967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132813461994768342697935311 199220192992152514046902967)
    ·
      refine ⟨298830289488228771070354451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199220192992152514046902967 298830289488228771070354451)
      ·
        refine ⟨448245434232343156605531677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298830289488228771070354451 448245434232343156605531677)
        ·
          refine ⟨168092037837128683727074379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448245434232343156605531677 168092037837128683727074379)
          ·
            refine ⟨252138056755693025590611569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168092037837128683727074379 252138056755693025590611569)
            ·
              refine ⟨189103542566769769192958677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252138056755693025590611569 189103542566769769192958677)
              ·
                refine ⟨4432114278908666465459969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 189103542566769769192958677 4432114278908666465459969)
                ·
                  refine ⟨3324085709181499849094977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4432114278908666465459969 3324085709181499849094977)
                  ·
                    refine ⟨2493064281886124886821233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3324085709181499849094977 2493064281886124886821233)
                    ·
                      refine ⟨1869798211414593665115925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2493064281886124886821233 1869798211414593665115925)
                      ·
                        rfl

theorem cell23_3641419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 2, 2].length) (baseStart_3641419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641419 prefixEnd_3641419 := by exact prefixLift 3641419
  have htrace : WordTrace (prefixWord ++ tailWord_3641419) baseStart_3641419 baseEnd_3641419 := by
    simpa [prefixWord, tailWord_3641419, baseEnd_3641419] using wordTrace_append hprefix tailTrace_3641419
  have hstable : (prefixWord ++ tailWord_3641419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641419).length < 2 ^ (prefixWord ++ tailWord_3641419).sum := by decide
  have hdescent : baseEnd_3641419 < baseStart_3641419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641535 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 6]
def baseStart_3641535 : Nat := 118140960795 + 3641535 * 2 ^ 59
def prefixEnd_3641535 : Nat := 4983230072969 + 3 ^ 40 * 3641535 * 2
def baseEnd_3641535 : Nat := 1869857775170515211265391

theorem tailTrace_3641535 : CollatzResearch.WordTrace tailWord_3641535 prefixEnd_3641535 1869857775170515211265391 := by
  unfold tailWord_3641535
  simp only [CollatzResearch.WordTrace]
  refine ⟨132817692862348094509158059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88545128574898729672772039 132817692862348094509158059)
  ·
    refine ⟨199226539293522141763737089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132817692862348094509158059 199226539293522141763737089)
    ·
      refine ⟨149419904470141606322802817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199226539293522141763737089 149419904470141606322802817)
      ·
        refine ⟨112064928352606204742102113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149419904470141606322802817 112064928352606204742102113)
        ·
          refine ⟨84048696264454653556576585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112064928352606204742102113 84048696264454653556576585)
          ·
            refine ⟨63036522198340990167432439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84048696264454653556576585 63036522198340990167432439)
            ·
              refine ⟨94554783297511485251148659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63036522198340990167432439 94554783297511485251148659)
              ·
                refine ⟨141832174946267227876722989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94554783297511485251148659 141832174946267227876722989)
                ·
                  refine ⟨53187065604850210453771121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141832174946267227876722989 53187065604850210453771121)
                  ·
                    refine ⟨39890299203637657840328341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53187065604850210453771121 39890299203637657840328341)
                    ·
                      refine ⟨1869857775170515211265391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39890299203637657840328341 1869857775170515211265391)
                      ·
                        rfl

theorem cell23_3641535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_3641535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641535 prefixEnd_3641535 := by exact prefixLift 3641535
  have htrace : WordTrace (prefixWord ++ tailWord_3641535) baseStart_3641535 baseEnd_3641535 := by
    simpa [prefixWord, tailWord_3641535, baseEnd_3641535] using wordTrace_append hprefix tailTrace_3641535
  have hstable : (prefixWord ++ tailWord_3641535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641535).length < 2 ^ (prefixWord ++ tailWord_3641535).sum := by decide
  have hdescent : baseEnd_3641535 < baseStart_3641535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641555 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 5]
def baseStart_3641555 : Nat := 118140960795 + 3641555 * 2 ^ 59
def prefixEnd_3641555 : Nat := 4983230072969 + 3 ^ 40 * 3641555 * 2
def baseEnd_3641555 : Nat := 1869868044783605133015299

theorem tailTrace_3641555 : CollatzResearch.WordTrace tailWord_3641555 prefixEnd_3641555 1869868044783605133015299 := by
  unfold tailWord_3641555
  simp only [CollatzResearch.WordTrace]
  refine ⟨132818422322275637924886119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88545614881517091949924079 132818422322275637924886119)
  ·
    refine ⟨199227633483413456887329179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132818422322275637924886119 199227633483413456887329179)
    ·
      refine ⟨298841450225120185330993769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199227633483413456887329179 298841450225120185330993769)
      ·
        refine ⟨224131087668840138998245327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298841450225120185330993769 224131087668840138998245327)
        ·
          refine ⟨336196631503260208497367991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224131087668840138998245327 336196631503260208497367991)
          ·
            refine ⟨504294947254890312746051987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336196631503260208497367991 504294947254890312746051987)
            ·
              refine ⟨756442420882335469119077981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504294947254890312746051987 756442420882335469119077981)
              ·
                refine ⟨283665907830875800919654243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 756442420882335469119077981 283665907830875800919654243)
                ·
                  refine ⟨425498861746313701379481365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283665907830875800919654243 425498861746313701379481365)
                  ·
                    refine ⟨19945259144358454752163189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 425498861746313701379481365 19945259144358454752163189)
                    ·
                      refine ⟨1869868044783605133015299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19945259144358454752163189 1869868044783605133015299)
                      ·
                        rfl

theorem cell23_3641555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_3641555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641555 prefixEnd_3641555 := by exact prefixLift 3641555
  have htrace : WordTrace (prefixWord ++ tailWord_3641555) baseStart_3641555 baseEnd_3641555 := by
    simpa [prefixWord, tailWord_3641555, baseEnd_3641555] using wordTrace_append hprefix tailTrace_3641555
  have hstable : (prefixWord ++ tailWord_3641555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641555).length < 2 ^ (prefixWord ++ tailWord_3641555).sum := by decide
  have hdescent : baseEnd_3641555 < baseStart_3641555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641576 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_3641576 : Nat := 118140960795 + 3641576 * 2 ^ 59
def prefixEnd_3641576 : Nat := 4983230072969 + 3 ^ 40 * 3641576 * 2
def baseEnd_3641576 : Nat := 1869878827877349550852703

theorem tailTrace_3641576 : CollatzResearch.WordTrace tailWord_3641576 prefixEnd_3641576 1869878827877349550852703 := by
  unfold tailWord_3641576
  simp only [CollatzResearch.WordTrace]
  refine ⟨66409594127599779255700291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88546125503466372340933721 66409594127599779255700291)
  ·
    refine ⟨99614391191399668883550437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66409594127599779255700291 99614391191399668883550437)
    ·
      refine ⟨18677698348387437915665707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99614391191399668883550437 18677698348387437915665707)
      ·
        refine ⟨28016547522581156873498561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18677698348387437915665707 28016547522581156873498561)
        ·
          refine ⟨21012410641935867655123921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28016547522581156873498561 21012410641935867655123921)
          ·
            refine ⟨15759307981451900741342941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21012410641935867655123921 15759307981451900741342941)
            ·
              refine ⟨5909740493044462778003603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15759307981451900741342941 5909740493044462778003603)
              ·
                refine ⟨8864610739566694167005405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5909740493044462778003603 8864610739566694167005405)
                ·
                  refine ⟨3324229027337510312627027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8864610739566694167005405 3324229027337510312627027)
                  ·
                    refine ⟨4986343541006265468940541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3324229027337510312627027 4986343541006265468940541)
                    ·
                      refine ⟨1869878827877349550852703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4986343541006265468940541 1869878827877349550852703)
                      ·
                        rfl

theorem cell23_3641576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_3641576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641576 prefixEnd_3641576 := by exact prefixLift 3641576
  have htrace : WordTrace (prefixWord ++ tailWord_3641576) baseStart_3641576 baseEnd_3641576 := by
    simpa [prefixWord, tailWord_3641576, baseEnd_3641576] using wordTrace_append hprefix tailTrace_3641576
  have hstable : (prefixWord ++ tailWord_3641576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641576).length < 2 ^ (prefixWord ++ tailWord_3641576).sum := by decide
  have hdescent : baseEnd_3641576 < baseStart_3641576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641582 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_3641582 : Nat := 118140960795 + 3641582 * 2 ^ 59
def prefixEnd_3641582 : Nat := 4983230072969 + 3 ^ 40 * 3641582 * 2
def baseEnd_3641582 : Nat := 1869881908761276527377675

theorem tailTrace_3641582 : CollatzResearch.WordTrace tailWord_3641582 prefixEnd_3641582 1869881908761276527377675 := by
  unfold tailWord_3641582
  simp only [CollatzResearch.WordTrace]
  refine ⟨16602425886647227692014875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88546271395451881024079333 16602425886647227692014875)
  ·
    refine ⟨24903638829970841538022313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16602425886647227692014875 24903638829970841538022313)
    ·
      refine ⟨18677729122478131153516735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24903638829970841538022313 18677729122478131153516735)
      ·
        refine ⟨28016593683717196730275103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18677729122478131153516735 28016593683717196730275103)
        ·
          refine ⟨42024890525575795095412655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28016593683717196730275103 42024890525575795095412655)
          ·
            refine ⟨63037335788363692643118983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42024890525575795095412655 63037335788363692643118983)
            ·
              refine ⟨94556003682545538964678475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63037335788363692643118983 94556003682545538964678475)
              ·
                refine ⟨141834005523818308447017713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94556003682545538964678475 141834005523818308447017713)
                ·
                  refine ⟨106375504142863731335263285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141834005523818308447017713 106375504142863731335263285)
                  ·
                    refine ⟨9972703513393474812680933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106375504142863731335263285 9972703513393474812680933)
                    ·
                      refine ⟨1869881908761276527377675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9972703513393474812680933 1869881908761276527377675)
                      ·
                        rfl

theorem cell23_3641582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_3641582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641582 prefixEnd_3641582 := by exact prefixLift 3641582
  have htrace : WordTrace (prefixWord ++ tailWord_3641582) baseStart_3641582 baseEnd_3641582 := by
    simpa [prefixWord, tailWord_3641582, baseEnd_3641582] using wordTrace_append hprefix tailTrace_3641582
  have hstable : (prefixWord ++ tailWord_3641582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641582).length < 2 ^ (prefixWord ++ tailWord_3641582).sum := by decide
  have hdescent : baseEnd_3641582 < baseStart_3641582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641596 : List Nat := [2, 2, 2, 1, 4, 3, 1, 2, 1, 5]
def baseStart_3641596 : Nat := 118140960795 + 3641596 * 2 ^ 59
def prefixEnd_3641596 : Nat := 4983230072969 + 3 ^ 40 * 3641596 * 2
def baseEnd_3641596 : Nat := 623296365830146490867537

theorem tailTrace_3641596 : CollatzResearch.WordTrace tailWord_3641596 prefixEnd_3641596 623296365830146490867537 := by
  unfold tailWord_3641596
  simp only [CollatzResearch.WordTrace]
  refine ⟨66409958857563550963564321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88546611810084734618085761 66409958857563550963564321)
  ·
    refine ⟨49807469143172663222673241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66409958857563550963564321 49807469143172663222673241)
    ·
      refine ⟨37355601857379497417004931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49807469143172663222673241 37355601857379497417004931)
      ·
        refine ⟨56033402786069246125507397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37355601857379497417004931 56033402786069246125507397)
        ·
          refine ⟨10506263022387983648532637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56033402786069246125507397 10506263022387983648532637)
          ·
            refine ⟨3939848633395493868199739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10506263022387983648532637 3939848633395493868199739)
            ·
              refine ⟨5909772950093240802299609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939848633395493868199739 5909772950093240802299609)
              ·
                refine ⟨4432329712569930601724707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5909772950093240802299609 4432329712569930601724707)
                ·
                  refine ⟨6648494568854895902587061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4432329712569930601724707 6648494568854895902587061)
                  ·
                    refine ⟨623296365830146490867537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6648494568854895902587061 623296365830146490867537)
                    ·
                      rfl

theorem cell23_3641596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_3641596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641596 prefixEnd_3641596 := by exact prefixLift 3641596
  have htrace : WordTrace (prefixWord ++ tailWord_3641596) baseStart_3641596 baseEnd_3641596 := by
    simpa [prefixWord, tailWord_3641596, baseEnd_3641596] using wordTrace_append hprefix tailTrace_3641596
  have hstable : (prefixWord ++ tailWord_3641596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641596).length < 2 ^ (prefixWord ++ tailWord_3641596).sum := by decide
  have hdescent : baseEnd_3641596 < baseStart_3641596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641619 : List Nat := [1, 1, 1, 2, 1, 3, 1, 7, 1, 2, 3]
def baseStart_3641619 : Nat := 118140960795 + 3641619 * 2 ^ 59
def prefixEnd_3641619 : Nat := 4983230072969 + 3 ^ 40 * 3641619 * 2
def baseEnd_3641619 : Nat := 1869900907545492882615005

theorem tailTrace_3641619 : CollatzResearch.WordTrace tailWord_3641619 prefixEnd_3641619 1869900907545492882615005 := by
  unfold tailWord_3641619
  simp only [CollatzResearch.WordTrace]
  refine ⟨132820756594043776855215911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88547171062695851236810607 132820756594043776855215911)
  ·
    refine ⟨199231134891065665282823867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132820756594043776855215911 199231134891065665282823867)
    ·
      refine ⟨298846702336598497924235801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199231134891065665282823867 298846702336598497924235801)
      ·
        refine ⟨224135026752448873443176851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298846702336598497924235801 224135026752448873443176851)
        ·
          refine ⟨336202540128673310164765277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224135026752448873443176851 336202540128673310164765277)
          ·
            refine ⟨126075952548252491311786979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336202540128673310164765277 126075952548252491311786979)
            ·
              refine ⟨189113928822378736967680469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126075952548252491311786979 189113928822378736967680469)
              ·
                refine ⟨4432357706774501647680011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 189113928822378736967680469 4432357706774501647680011)
                ·
                  refine ⟨6648536560161752471520017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4432357706774501647680011 6648536560161752471520017)
                  ·
                    refine ⟨4986402420121314353640013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6648536560161752471520017 4986402420121314353640013)
                    ·
                      refine ⟨1869900907545492882615005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4986402420121314353640013 1869900907545492882615005)
                      ·
                        rfl

theorem cell23_3641619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 2, 3].length) (baseStart_3641619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641619 prefixEnd_3641619 := by exact prefixLift 3641619
  have htrace : WordTrace (prefixWord ++ tailWord_3641619) baseStart_3641619 baseEnd_3641619 := by
    simpa [prefixWord, tailWord_3641619, baseEnd_3641619] using wordTrace_append hprefix tailTrace_3641619
  have hstable : (prefixWord ++ tailWord_3641619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641619).length < 2 ^ (prefixWord ++ tailWord_3641619).sum := by decide
  have hdescent : baseEnd_3641619 < baseStart_3641619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641694 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3641694 : Nat := 118140960795 + 3641694 * 2 ^ 59
def prefixEnd_3641694 : Nat := 4983230072969 + 3 ^ 40 * 3641694 * 2
def baseEnd_3641694 : Nat := 623313139531526696392387

theorem tailTrace_3641694 : CollatzResearch.WordTrace tailWord_3641694 prefixEnd_3641694 623313139531526696392387 := by
  unfold tailWord_3641694
  simp only [CollatzResearch.WordTrace]
  refine ⟨16602936508596508083024517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88548994712514709776130757 16602936508596508083024517)
  ·
    refine ⟨3113050595361845265567097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16602936508596508083024517 3113050595361845265567097)
    ·
      refine ⟨2334787946521383949175323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3113050595361845265567097 2334787946521383949175323)
      ·
        refine ⟨3502181919782075923762985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2334787946521383949175323 3502181919782075923762985)
        ·
          refine ⟨2626636439836556942822239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3502181919782075923762985 2626636439836556942822239)
          ·
            refine ⟨3939954659754835414233359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626636439836556942822239 3939954659754835414233359)
            ·
              refine ⟨5909931989632253121350039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939954659754835414233359 5909931989632253121350039)
              ·
                refine ⟨8864897984448379682025059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5909931989632253121350039 8864897984448379682025059)
                ·
                  refine ⟨13297346976672569523037589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8864897984448379682025059 13297346976672569523037589)
                  ·
                    refine ⟨623313139531526696392387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13297346976672569523037589 623313139531526696392387)
                    ·
                      rfl

theorem cell23_3641694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3641694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641694 prefixEnd_3641694 := by exact prefixLift 3641694
  have htrace : WordTrace (prefixWord ++ tailWord_3641694) baseStart_3641694 baseEnd_3641694 := by
    simpa [prefixWord, tailWord_3641694, baseEnd_3641694] using wordTrace_append hprefix tailTrace_3641694
  have hstable : (prefixWord ++ tailWord_3641694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641694).length < 2 ^ (prefixWord ++ tailWord_3641694).sum := by decide
  have hdescent : baseEnd_3641694 < baseStart_3641694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641709 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_3641709 : Nat := 118140960795 + 3641709 * 2 ^ 59
def prefixEnd_3641709 : Nat := 4983230072969 + 3 ^ 40 * 3641709 * 2
def baseEnd_3641709 : Nat := 1869947120804397530489591

theorem tailTrace_3641709 : CollatzResearch.WordTrace tailWord_3641709 prefixEnd_3641709 1869947120804397530489591 := by
  unfold tailWord_3641709
  simp only [CollatzResearch.WordTrace]
  refine ⟨132824039163717722225992181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88549359442478481483994787 132824039163717722225992181)
  ·
    refine ⟨12452253671598536458686767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132824039163717722225992181 12452253671598536458686767)
    ·
      refine ⟨18678380507397804688030151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12452253671598536458686767 18678380507397804688030151)
      ·
        refine ⟨28017570761096707032045227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18678380507397804688030151 28017570761096707032045227)
        ·
          refine ⟨42026356141645060548067841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28017570761096707032045227 42026356141645060548067841)
          ·
            refine ⟨31519767106233795411050881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42026356141645060548067841 31519767106233795411050881)
            ·
              refine ⟨23639825329675346558288161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31519767106233795411050881 23639825329675346558288161)
              ·
                refine ⟨17729868997256509918716121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23639825329675346558288161 17729868997256509918716121)
                ·
                  refine ⟨13297401747942382439037091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17729868997256509918716121 13297401747942382439037091)
                  ·
                    refine ⟨19946102621913573658555637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13297401747942382439037091 19946102621913573658555637)
                    ·
                      refine ⟨1869947120804397530489591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19946102621913573658555637 1869947120804397530489591)
                      ·
                        rfl

theorem cell23_3641709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_3641709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641709 prefixEnd_3641709 := by exact prefixLift 3641709
  have htrace : WordTrace (prefixWord ++ tailWord_3641709) baseStart_3641709 baseEnd_3641709 := by
    simpa [prefixWord, tailWord_3641709, baseEnd_3641709] using wordTrace_append hprefix tailTrace_3641709
  have hstable : (prefixWord ++ tailWord_3641709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641709).length < 2 ^ (prefixWord ++ tailWord_3641709).sum := by decide
  have hdescent : baseEnd_3641709 < baseStart_3641709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641722 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_3641722 : Nat := 118140960795 + 3641722 * 2 ^ 59
def prefixEnd_3641722 : Nat := 4983230072969 + 3 ^ 40 * 3641722 * 2
def baseEnd_3641722 : Nat := 1869953796052905979627031

theorem tailTrace_3641722 : CollatzResearch.WordTrace tailWord_3641722 prefixEnd_3641722 1869953796052905979627031 := by
  unfold tailWord_3641722
  simp only [CollatzResearch.WordTrace]
  refine ⟨33206128328167656361553855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88549675541780416964143613 33206128328167656361553855)
  ·
    refine ⟨49809192492251484542330783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33206128328167656361553855 49809192492251484542330783)
    ·
      refine ⟨74713788738377226813496175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49809192492251484542330783 74713788738377226813496175)
      ·
        refine ⟨112070683107565840220244263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74713788738377226813496175 112070683107565840220244263)
        ·
          refine ⟨168106024661348760330366395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112070683107565840220244263 168106024661348760330366395)
          ·
            refine ⟨252159036992023140495549593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168106024661348760330366395 252159036992023140495549593)
            ·
              refine ⟨189119277744017355371662195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252159036992023140495549593 189119277744017355371662195)
              ·
                refine ⟨283678916616026033057493293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189119277744017355371662195 283678916616026033057493293)
                ·
                  refine ⟨106379593731009762396559985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 283678916616026033057493293 106379593731009762396559985)
                  ·
                    refine ⟨79784695298257321797419989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106379593731009762396559985 79784695298257321797419989)
                    ·
                      refine ⟨1869953796052905979627031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79784695298257321797419989 1869953796052905979627031)
                      ·
                        rfl

theorem cell23_3641722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_3641722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641722 prefixEnd_3641722 := by exact prefixLift 3641722
  have htrace : WordTrace (prefixWord ++ tailWord_3641722) baseStart_3641722 baseEnd_3641722 := by
    simpa [prefixWord, tailWord_3641722, baseEnd_3641722] using wordTrace_append hprefix tailTrace_3641722
  have hstable : (prefixWord ++ tailWord_3641722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641722).length < 2 ^ (prefixWord ++ tailWord_3641722).sum := by decide
  have hdescent : baseEnd_3641722 < baseStart_3641722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641759 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 4, 5]
def baseStart_3641759 : Nat := 118140960795 + 3641759 * 2 ^ 59
def prefixEnd_3641759 : Nat := 4983230072969 + 3 ^ 40 * 3641759 * 2
def baseEnd_3641759 : Nat := 623324264945707444954787

theorem tailTrace_3641759 : CollatzResearch.WordTrace tailWord_3641759 prefixEnd_3641759 623324264945707444954787 := by
  unfold tailWord_3641759
  simp only [CollatzResearch.WordTrace]
  refine ⟨132825862813536580765312331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88550575209024387176874887 132825862813536580765312331)
  ·
    refine ⟨199238794220304871147968497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132825862813536580765312331 199238794220304871147968497)
    ·
      refine ⟨149429095665228653360976373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199238794220304871147968497 149429095665228653360976373)
      ·
        refine ⟨14008977718615186252591535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149429095665228653360976373 14008977718615186252591535)
        ·
          refine ⟨21013466577922779378887303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14008977718615186252591535 21013466577922779378887303)
          ·
            refine ⟨31520199866884169068330955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21013466577922779378887303 31520199866884169068330955)
            ·
              refine ⟨47280299800326253602496433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31520199866884169068330955 47280299800326253602496433)
              ·
                refine ⟨35460224850244690201872325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47280299800326253602496433 35460224850244690201872325)
                ·
                  refine ⟨6648792159420879412851061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35460224850244690201872325 6648792159420879412851061)
                  ·
                    refine ⟨623324264945707444954787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6648792159420879412851061 623324264945707444954787)
                    ·
                      rfl

theorem cell23_3641759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 5].length) (baseStart_3641759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641759 prefixEnd_3641759 := by exact prefixLift 3641759
  have htrace : WordTrace (prefixWord ++ tailWord_3641759) baseStart_3641759 baseEnd_3641759 := by
    simpa [prefixWord, tailWord_3641759, baseEnd_3641759] using wordTrace_append hprefix tailTrace_3641759
  have hstable : (prefixWord ++ tailWord_3641759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641759).length < 2 ^ (prefixWord ++ tailWord_3641759).sum := by decide
  have hdescent : baseEnd_3641759 < baseStart_3641759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641806 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_3641806 : Nat := 118140960795 + 3641806 * 2 ^ 59
def prefixEnd_3641806 : Nat := 4983230072969 + 3 ^ 40 * 3641806 * 2
def baseEnd_3641806 : Nat := 623332309475961216992215

theorem tailTrace_3641806 : CollatzResearch.WordTrace tailWord_3641806 prefixEnd_3641806 623332309475961216992215 := by
  unfold tailWord_3641806
  simp only [CollatzResearch.WordTrace]
  refine ⟨16603447130545788474034159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88551718029577538528182181 16603447130545788474034159)
  ·
    refine ⟨24905170695818682711051239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16603447130545788474034159 24905170695818682711051239)
    ·
      refine ⟨37357756043728024066576859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24905170695818682711051239 37357756043728024066576859)
      ·
        refine ⟨56036634065592036099865289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37357756043728024066576859 56036634065592036099865289)
        ·
          refine ⟨42027475549194027074898967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56036634065592036099865289 42027475549194027074898967)
          ·
            refine ⟨63041213323791040612348451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42027475549194027074898967 63041213323791040612348451)
            ·
              refine ⟨94561819985686560918522677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63041213323791040612348451 94561819985686560918522677)
              ·
                refine ⟨8865170623658115086111501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94561819985686560918522677 8865170623658115086111501)
                ·
                  refine ⟨3324438983871793157291813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8865170623658115086111501 3324438983871793157291813)
                  ·
                    refine ⟨623332309475961216992215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3324438983871793157291813 623332309475961216992215)
                    ·
                      rfl

theorem cell23_3641806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_3641806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641806 prefixEnd_3641806 := by exact prefixLift 3641806
  have htrace : WordTrace (prefixWord ++ tailWord_3641806) baseStart_3641806 baseEnd_3641806 := by
    simpa [prefixWord, tailWord_3641806, baseEnd_3641806] using wordTrace_append hprefix tailTrace_3641806
  have hstable : (prefixWord ++ tailWord_3641806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641806).length < 2 ^ (prefixWord ++ tailWord_3641806).sum := by decide
  have hdescent : baseEnd_3641806 < baseStart_3641806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641813 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 2, 4, 2]
def baseStart_3641813 : Nat := 118140960795 + 3641813 * 2 ^ 59
def prefixEnd_3641813 : Nat := 4983230072969 + 3 ^ 40 * 3641813 * 2
def baseEnd_3641813 : Nat := 1870000522792465123589113

theorem tailTrace_3641813 : CollatzResearch.WordTrace tailWord_3641813 prefixEnd_3641813 1870000522792465123589113 := by
  unfold tailWord_3641813
  simp only [CollatzResearch.WordTrace]
  refine ⟨132827832355340947987778093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88551888236893965325185395 132827832355340947987778093)
  ·
    refine ⟨49810437133252855495416785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132827832355340947987778093 49810437133252855495416785)
    ·
      refine ⟨37357827849939641621562589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49810437133252855495416785 37357827849939641621562589)
      ·
        refine ⟨14009185443727365608085971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37357827849939641621562589 14009185443727365608085971)
        ·
          refine ⟨21013778165591048412128957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14009185443727365608085971 21013778165591048412128957)
          ·
            refine ⟨7880166812096643154548359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21013778165591048412128957 7880166812096643154548359)
            ·
              refine ⟨11820250218144964731822539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7880166812096643154548359 11820250218144964731822539)
              ·
                refine ⟨17730375327217447097733809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11820250218144964731822539 17730375327217447097733809)
                ·
                  refine ⟨13297781495413085323300357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17730375327217447097733809 13297781495413085323300357)
                  ·
                    refine ⟨2493334030389953498118817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13297781495413085323300357 2493334030389953498118817)
                    ·
                      refine ⟨1870000522792465123589113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2493334030389953498118817 1870000522792465123589113)
                      ·
                        rfl

theorem cell23_3641813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_3641813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641813 prefixEnd_3641813 := by exact prefixLift 3641813
  have htrace : WordTrace (prefixWord ++ tailWord_3641813) baseStart_3641813 baseEnd_3641813 := by
    simpa [prefixWord, tailWord_3641813, baseEnd_3641813] using wordTrace_append hprefix tailTrace_3641813
  have hstable : (prefixWord ++ tailWord_3641813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641813).length < 2 ^ (prefixWord ++ tailWord_3641813).sum := by decide
  have hdescent : baseEnd_3641813 < baseStart_3641813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641906 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_3641906 : Nat := 118140960795 + 3641906 * 2 ^ 59
def prefixEnd_3641906 : Nat := 4983230072969 + 3 ^ 40 * 3641906 * 2
def baseEnd_3641906 : Nat := 1870048276493333259726185

theorem tailTrace_3641906 : CollatzResearch.WordTrace tailWord_3641906 prefixEnd_3641906 1870048276493333259726185 := by
  unfold tailWord_3641906
  simp only [CollatzResearch.WordTrace]
  refine ⟨33207806086001006217728393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88554149562669349913942381 33207806086001006217728393)
  ·
    refine ⟨24905854564500754663296295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33207806086001006217728393 24905854564500754663296295)
    ·
      refine ⟨37358781846751131994944443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24905854564500754663296295 37358781846751131994944443)
      ·
        refine ⟨56038172770126697992416665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37358781846751131994944443 56038172770126697992416665)
        ·
          refine ⟨42028629577595023494312499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56038172770126697992416665 42028629577595023494312499)
          ·
            refine ⟨63042944366392535241468749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42028629577595023494312499 63042944366392535241468749)
            ·
              refine ⟨23641104137397200715550781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63042944366392535241468749 23641104137397200715550781)
              ·
                refine ⟨8865414051523950268331543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23641104137397200715550781 8865414051523950268331543)
                ·
                  refine ⟨13298121077285925402497315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8865414051523950268331543 13298121077285925402497315)
                  ·
                    refine ⟨19947181615928888103745973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13298121077285925402497315 19947181615928888103745973)
                    ·
                      refine ⟨1870048276493333259726185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19947181615928888103745973 1870048276493333259726185)
                      ·
                        rfl

theorem cell23_3641906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_3641906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641906 prefixEnd_3641906 := by exact prefixLift 3641906
  have htrace : WordTrace (prefixWord ++ tailWord_3641906) baseStart_3641906 baseEnd_3641906 := by
    simpa [prefixWord, tailWord_3641906, baseEnd_3641906] using wordTrace_append hprefix tailTrace_3641906
  have hstable : (prefixWord ++ tailWord_3641906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641906).length < 2 ^ (prefixWord ++ tailWord_3641906).sum := by decide
  have hdescent : baseEnd_3641906 < baseStart_3641906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641913 : List Nat := [1, 2, 1, 5, 1, 1, 2, 4, 2, 4]
def baseStart_3641913 : Nat := 118140960795 + 3641913 * 2 ^ 59
def prefixEnd_3641913 : Nat := 4983230072969 + 3 ^ 40 * 3641913 * 2
def baseEnd_3641913 : Nat := 623350623619304910779551

theorem tailTrace_3641913 : CollatzResearch.WordTrace tailWord_3641913 prefixEnd_3641913 623350623619304910779551 := by
  unfold tailWord_3641913
  simp only [CollatzResearch.WordTrace]
  refine ⟨132831479654978665066418393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88554319769985776710945595 132831479654978665066418393)
  ·
    refine ⟨99623609741233998799813795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132831479654978665066418393 99623609741233998799813795)
    ·
      refine ⟨149435414611850998199720693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99623609741233998799813795 149435414611850998199720693)
      ·
        refine ⟨14009570119861031081223815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149435414611850998199720693 14009570119861031081223815)
        ·
          refine ⟨21014355179791546621835723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14009570119861031081223815 21014355179791546621835723)
          ·
            refine ⟨31521532769687319932753585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21014355179791546621835723 31521532769687319932753585)
            ·
              refine ⟨23641149577265489949565189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31521532769687319932753585 23641149577265489949565189)
              ·
                refine ⟨4432715545737279365543473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23641149577265489949565189 4432715545737279365543473)
                ·
                  refine ⟨3324536659302959524157605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4432715545737279365543473 3324536659302959524157605)
                  ·
                    refine ⟨623350623619304910779551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3324536659302959524157605 623350623619304910779551)
                    ·
                      rfl

theorem cell23_3641913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 4].length) (baseStart_3641913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641913 prefixEnd_3641913 := by exact prefixLift 3641913
  have htrace : WordTrace (prefixWord ++ tailWord_3641913) baseStart_3641913 baseEnd_3641913 := by
    simpa [prefixWord, tailWord_3641913, baseEnd_3641913] using wordTrace_append hprefix tailTrace_3641913
  have hstable : (prefixWord ++ tailWord_3641913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641913).length < 2 ^ (prefixWord ++ tailWord_3641913).sum := by decide
  have hdescent : baseEnd_3641913 < baseStart_3641913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641916 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_3641916 : Nat := 118140960795 + 3641916 * 2 ^ 59
def prefixEnd_3641916 : Nat := 4983230072969 + 3 ^ 40 * 3641916 * 2
def baseEnd_3641916 : Nat := 1870053411299878220601139

theorem tailTrace_3641916 : CollatzResearch.WordTrace tailWord_3641916 prefixEnd_3641916 1870053411299878220601139 := by
  unfold tailWord_3641916
  simp only [CollatzResearch.WordTrace]
  refine ⟨66415794536983898289388801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88554392715978531052518401 66415794536983898289388801)
  ·
    refine ⟨49811845902737923717041601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66415794536983898289388801 49811845902737923717041601)
    ·
      refine ⟨37358884427053442787781201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49811845902737923717041601 37358884427053442787781201)
      ·
        refine ⟨28019163320290082090835901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37358884427053442787781201 28019163320290082090835901)
        ·
          refine ⟨10507186245108780784063463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28019163320290082090835901 10507186245108780784063463)
          ·
            refine ⟨15760779367663171176095195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10507186245108780784063463 15760779367663171176095195)
            ·
              refine ⟨23641169051494756764142793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15760779367663171176095195 23641169051494756764142793)
              ·
                refine ⟨17730876788621067573107095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23641169051494756764142793 17730876788621067573107095)
                ·
                  refine ⟨26596315182931601359660643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17730876788621067573107095 26596315182931601359660643)
                  ·
                    refine ⟨39894472774397402039490965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26596315182931601359660643 39894472774397402039490965)
                    ·
                      refine ⟨1870053411299878220601139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39894472774397402039490965 1870053411299878220601139)
                      ·
                        rfl

theorem cell23_3641916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_3641916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641916 prefixEnd_3641916 := by exact prefixLift 3641916
  have htrace : WordTrace (prefixWord ++ tailWord_3641916) baseStart_3641916 baseEnd_3641916 := by
    simpa [prefixWord, tailWord_3641916, baseEnd_3641916] using wordTrace_append hprefix tailTrace_3641916
  have hstable : (prefixWord ++ tailWord_3641916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641916).length < 2 ^ (prefixWord ++ tailWord_3641916).sum := by decide
  have hdescent : baseEnd_3641916 < baseStart_3641916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641920 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 3, 2, 2]
def baseStart_3641920 : Nat := 118140960795 + 3641920 * 2 ^ 59
def prefixEnd_3641920 : Nat := 4983230072969 + 3 ^ 40 * 3641920 * 2
def baseEnd_3641920 : Nat := 1870055465222496204951121

theorem tailTrace_3641920 : CollatzResearch.WordTrace tailWord_3641920 prefixEnd_3641920 1870055465222496204951121 := by
  unfold tailWord_3641920
  simp only [CollatzResearch.WordTrace]
  refine ⟨66415867482976652630961607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88554489977302203507948809 66415867482976652630961607)
  ·
    refine ⟨99623801224464978946442411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66415867482976652630961607 99623801224464978946442411)
    ·
      refine ⟨149435701836697468419663617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99623801224464978946442411 149435701836697468419663617)
      ·
        refine ⟨112076776377523101314747713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149435701836697468419663617 112076776377523101314747713)
        ·
          refine ⟨84057582283142325986060785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112076776377523101314747713 84057582283142325986060785)
          ·
            refine ⟨63043186712356744489545589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84057582283142325986060785 63043186712356744489545589)
            ·
              refine ⟨5910298754283444795894899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63043186712356744489545589 5910298754283444795894899)
              ·
                refine ⟨8865448131425167193842349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5910298754283444795894899 8865448131425167193842349)
                ·
                  refine ⟨3324543049284437697690881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8865448131425167193842349 3324543049284437697690881)
                  ·
                    refine ⟨2493407286963328273268161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3324543049284437697690881 2493407286963328273268161)
                    ·
                      refine ⟨1870055465222496204951121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2493407286963328273268161 1870055465222496204951121)
                      ·
                        rfl

theorem cell23_3641920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 3, 2, 2].length) (baseStart_3641920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641920 prefixEnd_3641920 := by exact prefixLift 3641920
  have htrace : WordTrace (prefixWord ++ tailWord_3641920) baseStart_3641920 baseEnd_3641920 := by
    simpa [prefixWord, tailWord_3641920, baseEnd_3641920] using wordTrace_append hprefix tailTrace_3641920
  have hstable : (prefixWord ++ tailWord_3641920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641920).length < 2 ^ (prefixWord ++ tailWord_3641920).sum := by decide
  have hdescent : baseEnd_3641920 < baseStart_3641920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641930 : List Nat := [3, 1, 2, 1, 1, 4, 4, 1, 2, 4]
def baseStart_3641930 : Nat := 118140960795 + 3641930 * 2 ^ 59
def prefixEnd_3641930 : Nat := 4983230072969 + 3 ^ 40 * 3641930 * 2
def baseEnd_3641930 : Nat := 623353533343013721942025

theorem tailTrace_3641930 : CollatzResearch.WordTrace tailWord_3641930 prefixEnd_3641930 623353533343013721942025 := by
  unfold tailWord_3641930
  simp only [CollatzResearch.WordTrace]
  refine ⟨33208024923979269242446811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88554733130611384646524829 33208024923979269242446811)
  ·
    refine ⟨49812037385968903863670217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33208024923979269242446811 49812037385968903863670217)
    ·
      refine ⟨37359028039476677897752663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49812037385968903863670217 37359028039476677897752663)
      ·
        refine ⟨56038542059215016846628995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37359028039476677897752663 56038542059215016846628995)
        ·
          refine ⟨84057813088822525269943493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56038542059215016846628995 84057813088822525269943493)
          ·
            refine ⟨15760839954154223488114405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84057813088822525269943493 15760839954154223488114405)
            ·
              refine ⟨2955157491403916904021451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15760839954154223488114405 2955157491403916904021451)
              ·
                refine ⟨4432736237105875356032177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955157491403916904021451 4432736237105875356032177)
                ·
                  refine ⟨3324552177829406517024133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4432736237105875356032177 3324552177829406517024133)
                  ·
                    refine ⟨623353533343013721942025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3324552177829406517024133 623353533343013721942025)
                    ·
                      rfl

theorem cell23_3641930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_3641930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641930 prefixEnd_3641930 := by exact prefixLift 3641930
  have htrace : WordTrace (prefixWord ++ tailWord_3641930) baseStart_3641930 baseEnd_3641930 := by
    simpa [prefixWord, tailWord_3641930, baseEnd_3641930] using wordTrace_append hprefix tailTrace_3641930
  have hstable : (prefixWord ++ tailWord_3641930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641930).length < 2 ^ (prefixWord ++ tailWord_3641930).sum := by decide
  have hdescent : baseEnd_3641930 < baseStart_3641930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641933 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3641933 : Nat := 118140960795 + 3641933 * 2 ^ 59
def prefixEnd_3641933 : Nat := 4983230072969 + 3 ^ 40 * 3641933 * 2
def baseEnd_3641933 : Nat := 1870062140471004654088561

theorem tailTrace_3641933 : CollatzResearch.WordTrace tailWord_3641933 prefixEnd_3641933 1870062140471004654088561 := by
  unfold tailWord_3641933
  simp only [CollatzResearch.WordTrace]
  refine ⟨132832209114906208482146453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88554806076604138988097635 132832209114906208482146453)
  ·
    refine ⟨6226509802261228522600615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132832209114906208482146453 6226509802261228522600615)
    ·
      refine ⟨9339764703391842783900923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6226509802261228522600615 9339764703391842783900923)
      ·
        refine ⟨14009647055087764175851385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9339764703391842783900923 14009647055087764175851385)
        ·
          refine ⟨10507235291315823131888539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14009647055087764175851385 10507235291315823131888539)
          ·
            refine ⟨15760852936973734697832809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10507235291315823131888539 15760852936973734697832809)
            ·
              refine ⟨11820639702730301023374607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15760852936973734697832809 11820639702730301023374607)
              ·
                refine ⟨17730959554095451535061911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11820639702730301023374607 17730959554095451535061911)
                ·
                  refine ⟨26596439331143177302592867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17730959554095451535061911 26596439331143177302592867)
                  ·
                    refine ⟨39894658996714765953889301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26596439331143177302592867 39894658996714765953889301)
                    ·
                      refine ⟨1870062140471004654088561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39894658996714765953889301 1870062140471004654088561)
                      ·
                        rfl

theorem cell23_3641933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3641933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641933 prefixEnd_3641933 := by exact prefixLift 3641933
  have htrace : WordTrace (prefixWord ++ tailWord_3641933) baseStart_3641933 baseEnd_3641933 := by
    simpa [prefixWord, tailWord_3641933, baseEnd_3641933] using wordTrace_append hprefix tailTrace_3641933
  have hstable : (prefixWord ++ tailWord_3641933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641933).length < 2 ^ (prefixWord ++ tailWord_3641933).sum := by decide
  have hdescent : baseEnd_3641933 < baseStart_3641933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641940 : List Nat := [2, 4, 1, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_3641940 : Nat := 118140960795 + 3641940 * 2 ^ 59
def prefixEnd_3641940 : Nat := 4983230072969 + 3 ^ 40 * 3641940 * 2
def baseEnd_3641940 : Nat := 1870065734835586126701029

theorem tailTrace_3641940 : CollatzResearch.WordTrace tailWord_3641940 prefixEnd_3641940 1870065734835586126701029 := by
  unfold tailWord_3641940
  simp only [CollatzResearch.WordTrace]
  refine ⟨66416232212940424338825637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88554976283920565785100849 66416232212940424338825637)
  ·
    refine ⟨12453043539926329563529807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66416232212940424338825637 12453043539926329563529807)
    ·
      refine ⟨18679565309889494345294711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12453043539926329563529807 18679565309889494345294711)
      ·
        refine ⟨28019347964834241517942067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18679565309889494345294711 28019347964834241517942067)
        ·
          refine ⟨42029021947251362276913101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28019347964834241517942067 42029021947251362276913101)
          ·
            refine ⟨15760883230219260853842413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42029021947251362276913101 15760883230219260853842413)
            ·
              refine ⟨5910331211332222820190905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15760883230219260853842413 5910331211332222820190905)
              ·
                refine ⟨4432748408499167115143179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5910331211332222820190905 4432748408499167115143179)
                ·
                  refine ⟨6649122612748750672714769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4432748408499167115143179 6649122612748750672714769)
                  ·
                    refine ⟨4986841959561563004536077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6649122612748750672714769 4986841959561563004536077)
                    ·
                      refine ⟨1870065734835586126701029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4986841959561563004536077 1870065734835586126701029)
                      ·
                        rfl

theorem cell23_3641940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_3641940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641940 prefixEnd_3641940 := by exact prefixLift 3641940
  have htrace : WordTrace (prefixWord ++ tailWord_3641940) baseStart_3641940 baseEnd_3641940 := by
    simpa [prefixWord, tailWord_3641940, baseEnd_3641940] using wordTrace_append hprefix tailTrace_3641940
  have hstable : (prefixWord ++ tailWord_3641940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641940).length < 2 ^ (prefixWord ++ tailWord_3641940).sum := by decide
  have hdescent : baseEnd_3641940 < baseStart_3641940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641953 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_3641953 : Nat := 118140960795 + 3641953 * 2 ^ 59
def prefixEnd_3641953 : Nat := 4983230072969 + 3 ^ 40 * 3641953 * 2
def baseEnd_3641953 : Nat := 1870072410084094575838469

theorem tailTrace_3641953 : CollatzResearch.WordTrace tailWord_3641953 prefixEnd_3641953 1870072410084094575838469 := by
  unfold tailWord_3641953
  simp only [CollatzResearch.WordTrace]
  refine ⟨132832938574833751897874513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88555292383222501265249675 132832938574833751897874513)
  ·
    refine ⟨99624703931125313923405885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132832938574833751897874513 99624703931125313923405885)
    ·
      refine ⟨37359263974171992721277207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99624703931125313923405885 37359263974171992721277207)
      ·
        refine ⟨56038895961257989081915811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37359263974171992721277207 56038895961257989081915811)
        ·
          refine ⟨84058343941886983622873717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56038895961257989081915811 84058343941886983622873717)
          ·
            refine ⟨7880469744551904714644411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84058343941886983622873717 7880469744551904714644411)
            ·
              refine ⟨11820704616827857071966617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7880469744551904714644411 11820704616827857071966617)
              ·
                refine ⟨8865528462620892803974963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11820704616827857071966617 8865528462620892803974963)
                ·
                  refine ⟨13298292693931339205962445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8865528462620892803974963 13298292693931339205962445)
                  ·
                    refine ⟨4986859760224252202235917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13298292693931339205962445 4986859760224252202235917)
                    ·
                      refine ⟨1870072410084094575838469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4986859760224252202235917 1870072410084094575838469)
                      ·
                        rfl

theorem cell23_3641953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_3641953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641953 prefixEnd_3641953 := by exact prefixLift 3641953
  have htrace : WordTrace (prefixWord ++ tailWord_3641953) baseStart_3641953 baseEnd_3641953 := by
    simpa [prefixWord, tailWord_3641953, baseEnd_3641953] using wordTrace_append hprefix tailTrace_3641953
  have hstable : (prefixWord ++ tailWord_3641953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641953).length < 2 ^ (prefixWord ++ tailWord_3641953).sum := by decide
  have hdescent : baseEnd_3641953 < baseStart_3641953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641954 : List Nat := [3, 3, 2, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3641954 : Nat := 118140960795 + 3641954 * 2 ^ 59
def prefixEnd_3641954 : Nat := 4983230072969 + 3 ^ 40 * 3641954 * 2
def baseEnd_3641954 : Nat := 1870072923564749071925965

theorem tailTrace_3641954 : CollatzResearch.WordTrace tailWord_3641954 prefixEnd_3641954 1870072923564749071925965 := by
  unfold tailWord_3641954
  simp only [CollatzResearch.WordTrace]
  refine ⟨33208243761957532267165229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88555316698553419379107277 33208243761957532267165229)
  ·
    refine ⟨12453091410734074600186961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33208243761957532267165229 12453091410734074600186961)
    ·
      refine ⟨9339818558050555950140221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12453091410734074600186961 9339818558050555950140221)
      ·
        refine ⟨3502431959268958481302583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9339818558050555950140221 3502431959268958481302583)
        ·
          refine ⟨5253647938903437721953875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3502431959268958481302583 5253647938903437721953875)
          ·
            refine ⟨7880471908355156582930813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5253647938903437721953875 7880471908355156582930813)
            ·
              refine ⟨2955176965633183718599055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7880471908355156582930813 2955176965633183718599055)
              ·
                refine ⟨4432765448449775577898583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955176965633183718599055 4432765448449775577898583)
                ·
                  refine ⟨6649148172674663366847875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4432765448449775577898583 6649148172674663366847875)
                  ·
                    refine ⟨9973722259011995050271813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6649148172674663366847875 9973722259011995050271813)
                    ·
                      refine ⟨1870072923564749071925965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9973722259011995050271813 1870072923564749071925965)
                      ·
                        rfl

theorem cell23_3641954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3641954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641954 prefixEnd_3641954 := by exact prefixLift 3641954
  have htrace : WordTrace (prefixWord ++ tailWord_3641954) baseStart_3641954 baseEnd_3641954 := by
    simpa [prefixWord, tailWord_3641954, baseEnd_3641954] using wordTrace_append hprefix tailTrace_3641954
  have hstable : (prefixWord ++ tailWord_3641954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641954).length < 2 ^ (prefixWord ++ tailWord_3641954).sum := by decide
  have hdescent : baseEnd_3641954 < baseStart_3641954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641957 : List Nat := [1, 3, 1, 3, 4, 1, 3, 1, 1, 2, 3]
def baseStart_3641957 : Nat := 118140960795 + 3641957 * 2 ^ 59
def prefixEnd_3641957 : Nat := 4983230072969 + 3 ^ 40 * 3641957 * 2
def baseEnd_3641957 : Nat := 1870074464006712560188451

theorem tailTrace_3641957 : CollatzResearch.WordTrace tailWord_3641957 prefixEnd_3641957 1870074464006712560188451 := by
  unfold tailWord_3641957
  simp only [CollatzResearch.WordTrace]
  refine ⟨132833084466819260581020125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88555389644546173720680083 132833084466819260581020125)
  ·
    refine ⟨49812406675057222717882547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132833084466819260581020125 49812406675057222717882547)
    ·
      refine ⟨74718610012585834076823821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49812406675057222717882547 74718610012585834076823821)
      ·
        refine ⟨28019478754719687778808933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74718610012585834076823821 28019478754719687778808933)
        ·
          refine ⟨5253652266509941458526675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28019478754719687778808933 5253652266509941458526675)
          ·
            refine ⟨7880478399764912187790013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5253652266509941458526675 7880478399764912187790013)
            ·
              refine ⟨2955179399911842070421255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7880478399764912187790013 2955179399911842070421255)
              ·
                refine ⟨4432769099867763105631883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955179399911842070421255 4432769099867763105631883)
                ·
                  refine ⟨6649153649801644658447825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4432769099867763105631883 6649153649801644658447825)
                  ·
                    refine ⟨4986865237351233493835869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6649153649801644658447825 4986865237351233493835869)
                    ·
                      refine ⟨1870074464006712560188451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4986865237351233493835869 1870074464006712560188451)
                      ·
                        rfl

theorem cell23_3641957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_3641957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641957 prefixEnd_3641957 := by exact prefixLift 3641957
  have htrace : WordTrace (prefixWord ++ tailWord_3641957) baseStart_3641957 baseEnd_3641957 := by
    simpa [prefixWord, tailWord_3641957, baseEnd_3641957] using wordTrace_append hprefix tailTrace_3641957
  have hstable : (prefixWord ++ tailWord_3641957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641957).length < 2 ^ (prefixWord ++ tailWord_3641957).sum := by decide
  have hdescent : baseEnd_3641957 < baseStart_3641957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3641996 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_3641996 : Nat := 118140960795 + 3641996 * 2 ^ 59
def prefixEnd_3641996 : Nat := 4983230072969 + 3 ^ 40 * 3641996 * 2
def baseEnd_3641996 : Nat := 1870094489752237907600771

theorem tailTrace_3641996 : CollatzResearch.WordTrace tailWord_3641996 prefixEnd_3641996 1870094489752237907600771 := by
  unfold tailWord_3641996
  simp only [CollatzResearch.WordTrace]
  refine ⟨66417253456838985120844921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88556337942451980161126561 66417253456838985120844921)
  ·
    refine ⟨49812940092629238840633691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66417253456838985120844921 49812940092629238840633691)
    ·
      refine ⟨74719410138943858260950537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49812940092629238840633691 74719410138943858260950537)
      ·
        refine ⟨56039557604207893695712903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74719410138943858260950537 56039557604207893695712903)
        ·
          refine ⟨84059336406311840543569355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56039557604207893695712903 84059336406311840543569355)
          ·
            refine ⟨126089004609467760815354033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84059336406311840543569355 126089004609467760815354033)
            ·
              refine ⟨94566753457100820611515525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126089004609467760815354033 94566753457100820611515525)
              ·
                refine ⟨17731266273206403864659161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94566753457100820611515525 17731266273206403864659161)
                ·
                  refine ⟨13298449704904802898494371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17731266273206403864659161 13298449704904802898494371)
                  ·
                    refine ⟨19947674557357204347741557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13298449704904802898494371 19947674557357204347741557)
                    ·
                      refine ⟨1870094489752237907600771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19947674557357204347741557 1870094489752237907600771)
                      ·
                        rfl

theorem cell23_3641996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_3641996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3641996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3641996 prefixEnd_3641996 := by exact prefixLift 3641996
  have htrace : WordTrace (prefixWord ++ tailWord_3641996) baseStart_3641996 baseEnd_3641996 := by
    simpa [prefixWord, tailWord_3641996, baseEnd_3641996] using wordTrace_append hprefix tailTrace_3641996
  have hstable : (prefixWord ++ tailWord_3641996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3641996).length < 2 ^ (prefixWord ++ tailWord_3641996).sum := by decide
  have hdescent : baseEnd_3641996 < baseStart_3641996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3641996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642044 : List Nat := [2, 2, 2, 3, 1, 1, 5, 1, 2, 2, 2]
def baseStart_3642044 : Nat := 118140960795 + 3642044 * 2 ^ 59
def prefixEnd_3642044 : Nat := 4983230072969 + 3 ^ 40 * 3642044 * 2
def baseEnd_3642044 : Nat := 1870119136823653719800551

theorem tailTrace_3642044 : CollatzResearch.WordTrace tailWord_3642044 prefixEnd_3642044 1870119136823653719800551 := by
  unfold tailWord_3642044
  simp only [CollatzResearch.WordTrace]
  refine ⟨66418128808752037219718593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88557505078336049626291457 66418128808752037219718593)
  ·
    refine ⟨49813596606564027914788945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66418128808752037219718593 49813596606564027914788945)
    ·
      refine ⟨37360197454923020936091709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49813596606564027914788945 37360197454923020936091709)
      ·
        refine ⟨14010074045596132851034391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37360197454923020936091709 14010074045596132851034391)
        ·
          refine ⟨21015111068394199276551587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14010074045596132851034391 21015111068394199276551587)
          ·
            refine ⟨31522666602591298914827381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21015111068394199276551587 31522666602591298914827381)
            ·
              refine ⟨2955249993992934273265067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31522666602591298914827381 2955249993992934273265067)
              ·
                refine ⟨4432874990989401409897601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955249993992934273265067 4432874990989401409897601)
                ·
                  refine ⟨3324656243242051057423201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4432874990989401409897601 3324656243242051057423201)
                  ·
                    refine ⟨2493492182431538293067401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3324656243242051057423201 2493492182431538293067401)
                    ·
                      refine ⟨1870119136823653719800551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2493492182431538293067401 1870119136823653719800551)
                      ·
                        rfl

theorem cell23_3642044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_3642044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642044 prefixEnd_3642044 := by exact prefixLift 3642044
  have htrace : WordTrace (prefixWord ++ tailWord_3642044) baseStart_3642044 baseEnd_3642044 := by
    simpa [prefixWord, tailWord_3642044, baseEnd_3642044] using wordTrace_append hprefix tailTrace_3642044
  have hstable : (prefixWord ++ tailWord_3642044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642044).length < 2 ^ (prefixWord ++ tailWord_3642044).sum := by decide
  have hdescent : baseEnd_3642044 < baseStart_3642044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642103 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 3]
def baseStart_3642103 : Nat := 118140960795 + 3642103 * 2 ^ 59
def prefixEnd_3642103 : Nat := 4983230072969 + 3 ^ 40 * 3642103 * 2
def baseEnd_3642103 : Nat := 1870149432182268988962779

theorem tailTrace_3642103 : CollatzResearch.WordTrace tailWord_3642103 prefixEnd_3642103 1870149432182268988962779 := by
  unfold tailWord_3642103
  simp only [CollatzResearch.WordTrace]
  refine ⟨132838409524290327515834963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88558939682860218343889975 132838409524290327515834963)
  ·
    refine ⟨199257614286435491273752445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132838409524290327515834963 199257614286435491273752445)
    ·
      refine ⟨74721605357413309227657167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199257614286435491273752445 74721605357413309227657167)
      ·
        refine ⟨112082408036119963841485751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74721605357413309227657167 112082408036119963841485751)
        ·
          refine ⟨168123612054179945762228627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112082408036119963841485751 168123612054179945762228627)
          ·
            refine ⟨252185418081269918643342941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168123612054179945762228627 252185418081269918643342941)
            ·
              refine ⟨94569531780476219491253603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252185418081269918643342941 94569531780476219491253603)
              ·
                refine ⟨141854297670714329236880405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94569531780476219491253603 141854297670714329236880405)
                ·
                  refine ⟨6649420203314734182978769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141854297670714329236880405 6649420203314734182978769)
                  ·
                    refine ⟨4987065152486050637234077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6649420203314734182978769 4987065152486050637234077)
                    ·
                      refine ⟨1870149432182268988962779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4987065152486050637234077 1870149432182268988962779)
                      ·
                        rfl

theorem cell23_3642103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_3642103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642103 prefixEnd_3642103 := by exact prefixLift 3642103
  have htrace : WordTrace (prefixWord ++ tailWord_3642103) baseStart_3642103 baseEnd_3642103 := by
    simpa [prefixWord, tailWord_3642103, baseEnd_3642103] using wordTrace_append hprefix tailTrace_3642103
  have hstable : (prefixWord ++ tailWord_3642103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642103).length < 2 ^ (prefixWord ++ tailWord_3642103).sum := by decide
  have hdescent : baseEnd_3642103 < baseStart_3642103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642120 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_3642120 : Nat := 118140960795 + 3642120 * 2 ^ 59
def prefixEnd_3642120 : Nat := 4983230072969 + 3 ^ 40 * 3642120 * 2
def baseEnd_3642120 : Nat := 1870158161353395422450201

theorem tailTrace_3642120 : CollatzResearch.WordTrace tailWord_3642120 prefixEnd_3642120 1870158161353395422450201 := by
  unfold tailWord_3642120
  simp only [CollatzResearch.WordTrace]
  refine ⟨66419514782614369709601907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88559353043485826279469209 66419514782614369709601907)
  ·
    refine ⟨99629272173921554564402861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66419514782614369709601907 99629272173921554564402861)
    ·
      refine ⟨37360977065220582961651073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99629272173921554564402861 37360977065220582961651073)
      ·
        refine ⟨28020732798915437221238305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37360977065220582961651073 28020732798915437221238305)
        ·
          refine ⟨21015549599186577915928729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28020732798915437221238305 21015549599186577915928729)
          ·
            refine ⟨15761662199389933436946547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21015549599186577915928729 15761662199389933436946547)
            ·
              refine ⟨23642493299084900155419821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15761662199389933436946547 23642493299084900155419821)
              ·
                refine ⟨8865934987156837558282433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23642493299084900155419821 8865934987156837558282433)
                ·
                  refine ⟨6649451240367628168711825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8865934987156837558282433 6649451240367628168711825)
                  ·
                    refine ⟨4987088430275721126533869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6649451240367628168711825 4987088430275721126533869)
                    ·
                      refine ⟨1870158161353395422450201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4987088430275721126533869 1870158161353395422450201)
                      ·
                        rfl

theorem cell23_3642120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_3642120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642120 prefixEnd_3642120 := by exact prefixLift 3642120
  have htrace : WordTrace (prefixWord ++ tailWord_3642120) baseStart_3642120 baseEnd_3642120 := by
    simpa [prefixWord, tailWord_3642120, baseEnd_3642120] using wordTrace_append hprefix tailTrace_3642120
  have hstable : (prefixWord ++ tailWord_3642120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642120).length < 2 ^ (prefixWord ++ tailWord_3642120).sum := by decide
  have hdescent : baseEnd_3642120 < baseStart_3642120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642140 : List Nat := [2, 2, 3, 1, 1, 4, 2, 2, 6]
def baseStart_3642140 : Nat := 118140960795 + 3642140 * 2 ^ 59
def prefixEnd_3642140 : Nat := 4983230072969 + 3 ^ 40 * 3642140 * 2
def baseEnd_3642140 : Nat := 207796492329609482688901

theorem tailTrace_3642140 : CollatzResearch.WordTrace tailWord_3642140 prefixEnd_3642140 207796492329609482688901 := by
  unfold tailWord_3642140
  simp only [CollatzResearch.WordTrace]
  refine ⟨66419879512578141417465937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88559839350104188556621249 66419879512578141417465937)
  ·
    refine ⟨49814909634433606063099453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66419879512578141417465937 49814909634433606063099453)
    ·
      refine ⟨18680591112912602273662295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49814909634433606063099453 18680591112912602273662295)
      ·
        refine ⟨28020886669368903410493443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18680591112912602273662295 28020886669368903410493443)
        ·
          refine ⟨42031330004053355115740165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28020886669368903410493443 42031330004053355115740165)
          ·
            refine ⟨7880874375760004084201281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42031330004053355115740165 7880874375760004084201281)
            ·
              refine ⟨5910655781820003063150961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7880874375760004084201281 5910655781820003063150961)
              ·
                refine ⟨4432991836365002297363221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5910655781820003063150961 4432991836365002297363221)
                ·
                  refine ⟨207796492329609482688901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4432991836365002297363221 207796492329609482688901)
                  ·
                    rfl

theorem cell23_3642140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 6].length) (baseStart_3642140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642140 prefixEnd_3642140 := by exact prefixLift 3642140
  have htrace : WordTrace (prefixWord ++ tailWord_3642140) baseStart_3642140 baseEnd_3642140 := by
    simpa [prefixWord, tailWord_3642140, baseEnd_3642140] using wordTrace_append hprefix tailTrace_3642140
  have hstable : (prefixWord ++ tailWord_3642140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642140).length < 2 ^ (prefixWord ++ tailWord_3642140).sum := by decide
  have hdescent : baseEnd_3642140 < baseStart_3642140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642144 : List Nat := [2, 1, 1, 5, 1, 2, 4, 2, 1, 4]
def baseStart_3642144 : Nat := 118140960795 + 3642144 * 2 ^ 59
def prefixEnd_3642144 : Nat := 4983230072969 + 3 ^ 40 * 3642144 * 2
def baseEnd_3642144 : Nat := 623390161629701109516697

theorem tailTrace_3642144 : CollatzResearch.WordTrace tailWord_3642144 prefixEnd_3642144 623390161629701109516697 := by
  unfold tailWord_3642144
  simp only [CollatzResearch.WordTrace]
  refine ⟨66419952458570895759038743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88559936611427861012051657 66419952458570895759038743)
  ·
    refine ⟨99629928687856343638558115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66419952458570895759038743 99629928687856343638558115)
    ·
      refine ⟨149444893031784515457837173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99629928687856343638558115 149444893031784515457837173)
      ·
        refine ⟨14010458721729798324172235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149444893031784515457837173 14010458721729798324172235)
        ·
          refine ⟨21015688082594697486258353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14010458721729798324172235 21015688082594697486258353)
          ·
            refine ⟨15761766061946023114693765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21015688082594697486258353 15761766061946023114693765)
            ·
              refine ⟨2955331136614879334005081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15761766061946023114693765 2955331136614879334005081)
              ·
                refine ⟨2216498352461159500503811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2955331136614879334005081 2216498352461159500503811)
                ·
                  refine ⟨3324747528691739250755717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216498352461159500503811 3324747528691739250755717)
                  ·
                    refine ⟨623390161629701109516697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3324747528691739250755717 623390161629701109516697)
                    ·
                      rfl

theorem cell23_3642144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 1, 4].length) (baseStart_3642144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642144 prefixEnd_3642144 := by exact prefixLift 3642144
  have htrace : WordTrace (prefixWord ++ tailWord_3642144) baseStart_3642144 baseEnd_3642144 := by
    simpa [prefixWord, tailWord_3642144, baseEnd_3642144] using wordTrace_append hprefix tailTrace_3642144
  have hstable : (prefixWord ++ tailWord_3642144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642144).length < 2 ^ (prefixWord ++ tailWord_3642144).sum := by decide
  have hdescent : baseEnd_3642144 < baseStart_3642144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642160 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 4, 3, 2]
def baseStart_3642160 : Nat := 118140960795 + 3642160 * 2 ^ 59
def prefixEnd_3642160 : Nat := 4983230072969 + 3 ^ 40 * 3642160 * 2
def baseEnd_3642160 : Nat := 1870178700579575265950017

theorem tailTrace_3642160 : CollatzResearch.WordTrace tailWord_3642160 prefixEnd_3642160 1870178700579575265950017 := by
  unfold tailWord_3642160
  simp only [CollatzResearch.WordTrace]
  refine ⟨66420244242541913125329967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88560325656722550833773289 66420244242541913125329967)
  ·
    refine ⟨99630366363812869687994951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66420244242541913125329967 99630366363812869687994951)
    ·
      refine ⟨149445549545719304531992427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99630366363812869687994951 149445549545719304531992427)
      ·
        refine ⟨224168324318578956797988641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149445549545719304531992427 224168324318578956797988641)
        ·
          refine ⟨168126243238934217598491481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224168324318578956797988641 168126243238934217598491481)
          ·
            refine ⟨126094682429200663198868611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168126243238934217598491481 126094682429200663198868611)
            ·
              refine ⟨189142023643800994798302917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126094682429200663198868611 189142023643800994798302917)
              ·
                refine ⟨35464129433212686524681797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189142023643800994798302917 35464129433212686524681797)
                ·
                  refine ⟨6649524268727378723377837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35464129433212686524681797 6649524268727378723377837)
                  ·
                    refine ⟨2493571600772767021266689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6649524268727378723377837 2493571600772767021266689)
                    ·
                      refine ⟨1870178700579575265950017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2493571600772767021266689 1870178700579575265950017)
                      ·
                        rfl

theorem cell23_3642160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4, 3, 2].length) (baseStart_3642160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642160 prefixEnd_3642160 := by exact prefixLift 3642160
  have htrace : WordTrace (prefixWord ++ tailWord_3642160) baseStart_3642160 baseEnd_3642160 := by
    simpa [prefixWord, tailWord_3642160, baseEnd_3642160] using wordTrace_append hprefix tailTrace_3642160
  have hstable : (prefixWord ++ tailWord_3642160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642160).length < 2 ^ (prefixWord ++ tailWord_3642160).sum := by decide
  have hdescent : baseEnd_3642160 < baseStart_3642160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642184 : List Nat := [2, 1, 3, 1, 1, 3, 4, 3, 1, 1, 3]
def baseStart_3642184 : Nat := 118140960795 + 3642184 * 2 ^ 59
def prefixEnd_3642184 : Nat := 4983230072969 + 3 ^ 40 * 3642184 * 2
def baseEnd_3642184 : Nat := 1870191024115283172049907

theorem tailTrace_3642184 : CollatzResearch.WordTrace tailWord_3642184 prefixEnd_3642184 1870191024115283172049907 := by
  unfold tailWord_3642184
  simp only [CollatzResearch.WordTrace]
  refine ⟨66420681918498439174766803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88560909224664585566355737 66420681918498439174766803)
  ·
    refine ⟨99631022877747658762150205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66420681918498439174766803 99631022877747658762150205)
    ·
      refine ⟨37361633579155372035806327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99631022877747658762150205 37361633579155372035806327)
      ·
        refine ⟨56042450368733058053709491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37361633579155372035806327 56042450368733058053709491)
        ·
          refine ⟨84063675553099587080564237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56042450368733058053709491 84063675553099587080564237)
          ·
            refine ⟨31523878332412345155211589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84063675553099587080564237 31523878332412345155211589)
            ·
              refine ⟨5910727187327314716602173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31523878332412345155211589 5910727187327314716602173)
              ·
                refine ⟨2216522695247743018725815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5910727187327314716602173 2216522695247743018725815)
                ·
                  refine ⟨3324784042871614528088723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216522695247743018725815 3324784042871614528088723)
                  ·
                    refine ⟨4987176064307421792133085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3324784042871614528088723 4987176064307421792133085)
                    ·
                      refine ⟨1870191024115283172049907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4987176064307421792133085 1870191024115283172049907)
                      ·
                        rfl

theorem cell23_3642184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_3642184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642184 prefixEnd_3642184 := by exact prefixLift 3642184
  have htrace : WordTrace (prefixWord ++ tailWord_3642184) baseStart_3642184 baseEnd_3642184 := by
    simpa [prefixWord, tailWord_3642184, baseEnd_3642184] using wordTrace_append hprefix tailTrace_3642184
  have hstable : (prefixWord ++ tailWord_3642184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642184).length < 2 ^ (prefixWord ++ tailWord_3642184).sum := by decide
  have hdescent : baseEnd_3642184 < baseStart_3642184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642190 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2]
def baseStart_3642190 : Nat := 118140960795 + 3642190 * 2 ^ 59
def prefixEnd_3642190 : Nat := 4983230072969 + 3 ^ 40 * 3642190 * 2
def baseEnd_3642190 : Nat := 1870194104999210148574879

theorem tailTrace_3642190 : CollatzResearch.WordTrace tailWord_3642190 prefixEnd_3642190 1870194104999210148574879 := by
  unfold tailWord_3642190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16605197834371892671781503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88561055116650094249501349 16605197834371892671781503)
  ·
    refine ⟨24907796751557839007672255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16605197834371892671781503 24907796751557839007672255)
    ·
      refine ⟨37361695127336758511508383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24907796751557839007672255 37361695127336758511508383)
      ·
        refine ⟨56042542691005137767262575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37361695127336758511508383 56042542691005137767262575)
        ·
          refine ⟨84063814036507706650893863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56042542691005137767262575 84063814036507706650893863)
          ·
            refine ⟨126095721054761559976340795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84063814036507706650893863 126095721054761559976340795)
            ·
              refine ⟨189143581582142339964511193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126095721054761559976340795 189143581582142339964511193)
              ·
                refine ⟨141857686186606754973383395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189143581582142339964511193 141857686186606754973383395)
                ·
                  refine ⟨212786529279910132460075093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141857686186606754973383395 212786529279910132460075093)
                  ·
                    refine ⟨2493592139998946864766505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 212786529279910132460075093 2493592139998946864766505)
                    ·
                      refine ⟨1870194104999210148574879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2493592139998946864766505 1870194104999210148574879)
                      ·
                        rfl

theorem cell23_3642190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_3642190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642190 prefixEnd_3642190 := by exact prefixLift 3642190
  have htrace : WordTrace (prefixWord ++ tailWord_3642190) baseStart_3642190 baseEnd_3642190 := by
    simpa [prefixWord, tailWord_3642190, baseEnd_3642190] using wordTrace_append hprefix tailTrace_3642190
  have hstable : (prefixWord ++ tailWord_3642190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642190).length < 2 ^ (prefixWord ++ tailWord_3642190).sum := by decide
  have hdescent : baseEnd_3642190 < baseStart_3642190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642257 : List Nat := [1, 2, 2, 1, 1, 1, 3, 6, 2, 1, 3]
def baseStart_3642257 : Nat := 118140960795 + 3642257 * 2 ^ 59
def prefixEnd_3642257 : Nat := 4983230072969 + 3 ^ 40 * 3642257 * 2
def baseEnd_3642257 : Nat := 1870228508203061386437071

theorem tailTrace_3642257 : CollatzResearch.WordTrace tailWord_3642257 prefixEnd_3642257 1870228508203061386437071 := by
  unfold tailWord_3642257
  simp only [CollatzResearch.WordTrace]
  refine ⟨132844026365732411816941025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88562684243821607877960683 132844026365732411816941025)
  ·
    refine ⟨99633019774299308862705769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132844026365732411816941025 99633019774299308862705769)
    ·
      refine ⟨74724764830724481647029327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99633019774299308862705769 74724764830724481647029327)
      ·
        refine ⟨112087147246086722470543991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74724764830724481647029327 112087147246086722470543991)
        ·
          refine ⟨168130720869130083705815987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112087147246086722470543991 168130720869130083705815987)
          ·
            refine ⟨252196081303695125558723981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168130720869130083705815987 252196081303695125558723981)
            ·
              refine ⟨94573530488885672084521493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252196081303695125558723981 94573530488885672084521493)
              ·
                refine ⟨4433134241666515878961945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94573530488885672084521493 4433134241666515878961945)
                ·
                  refine ⟨3324850681249886909221459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4433134241666515878961945 3324850681249886909221459)
                  ·
                    refine ⟨4987276021874830363832189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3324850681249886909221459 4987276021874830363832189)
                    ·
                      refine ⟨1870228508203061386437071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4987276021874830363832189 1870228508203061386437071)
                      ·
                        rfl

theorem cell23_3642257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_3642257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642257 prefixEnd_3642257 := by exact prefixLift 3642257
  have htrace : WordTrace (prefixWord ++ tailWord_3642257) baseStart_3642257 baseEnd_3642257 := by
    simpa [prefixWord, tailWord_3642257, baseEnd_3642257] using wordTrace_append hprefix tailTrace_3642257
  have hstable : (prefixWord ++ tailWord_3642257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642257).length < 2 ^ (prefixWord ++ tailWord_3642257).sum := by decide
  have hdescent : baseEnd_3642257 < baseStart_3642257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642258 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_3642258 : Nat := 118140960795 + 3642258 * 2 ^ 59
def prefixEnd_3642258 : Nat := 4983230072969 + 3 ^ 40 * 3642258 * 2
def baseEnd_3642258 : Nat := 1870229021683715882524567

theorem tailTrace_3642258 : CollatzResearch.WordTrace tailWord_3642258 prefixEnd_3642258 1870229021683715882524567 := by
  unfold tailWord_3642258
  simp only [CollatzResearch.WordTrace]
  refine ⟨33211015709682197246931857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88562708559152525991818285 33211015709682197246931857)
  ·
    refine ⟨24908261782261647935198893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33211015709682197246931857 24908261782261647935198893)
    ·
      refine ⟨9340598168348117975699585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24908261782261647935198893 9340598168348117975699585)
      ·
        refine ⟨7005448626261088481774689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9340598168348117975699585 7005448626261088481774689)
        ·
          refine ⟨5254086469695816361331017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7005448626261088481774689 5254086469695816361331017)
          ·
            refine ⟨3940564852271862270998263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5254086469695816361331017 3940564852271862270998263)
            ·
              refine ⟨5910847278407793406497395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3940564852271862270998263 5910847278407793406497395)
              ·
                refine ⟨8866270917611690109746093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5910847278407793406497395 8866270917611690109746093)
                ·
                  refine ⟨3324851594104383791154785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8866270917611690109746093 3324851594104383791154785)
                  ·
                    refine ⟨2493638695578287843366089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3324851594104383791154785 2493638695578287843366089)
                    ·
                      refine ⟨1870229021683715882524567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2493638695578287843366089 1870229021683715882524567)
                      ·
                        rfl

theorem cell23_3642258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_3642258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642258 prefixEnd_3642258 := by exact prefixLift 3642258
  have htrace : WordTrace (prefixWord ++ tailWord_3642258) baseStart_3642258 baseEnd_3642258 := by
    simpa [prefixWord, tailWord_3642258, baseEnd_3642258] using wordTrace_append hprefix tailTrace_3642258
  have hstable : (prefixWord ++ tailWord_3642258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642258).length < 2 ^ (prefixWord ++ tailWord_3642258).sum := by decide
  have hdescent : baseEnd_3642258 < baseStart_3642258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642260 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_3642260 : Nat := 118140960795 + 3642260 * 2 ^ 59
def prefixEnd_3642260 : Nat := 4983230072969 + 3 ^ 40 * 3642260 * 2
def baseEnd_3642260 : Nat := 623410016215008291566519

theorem tailTrace_3642260 : CollatzResearch.WordTrace tailWord_3642260 prefixEnd_3642260 623410016215008291566519 := by
  unfold tailWord_3642260
  simp only [CollatzResearch.WordTrace]
  refine ⟨66422067892360771664650117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88562757189814362219533489 66422067892360771664650117)
  ·
    refine ⟨12454137729817644687121897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66422067892360771664650117 12454137729817644687121897)
    ·
      refine ⟨9340603297363233515341423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12454137729817644687121897 9340603297363233515341423)
      ·
        refine ⟨14010904946044850273012135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9340603297363233515341423 14010904946044850273012135)
        ·
          refine ⟨21016357419067275409518203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14010904946044850273012135 21016357419067275409518203)
          ·
            refine ⟨31524536128600913114277305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21016357419067275409518203 31524536128600913114277305)
            ·
              refine ⟨23643402096450684835707979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31524536128600913114277305 23643402096450684835707979)
              ·
                refine ⟨35465103144676027253561969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23643402096450684835707979 35465103144676027253561969)
                ·
                  refine ⟨26598827358507020440171477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35465103144676027253561969 26598827358507020440171477)
                  ·
                    refine ⟨623410016215008291566519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26598827358507020440171477 623410016215008291566519)
                    ·
                      rfl

theorem cell23_3642260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_3642260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642260 prefixEnd_3642260 := by exact prefixLift 3642260
  have htrace : WordTrace (prefixWord ++ tailWord_3642260) baseStart_3642260 baseEnd_3642260 := by
    simpa [prefixWord, tailWord_3642260, baseEnd_3642260] using wordTrace_append hprefix tailTrace_3642260
  have hstable : (prefixWord ++ tailWord_3642260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642260).length < 2 ^ (prefixWord ++ tailWord_3642260).sum := by decide
  have hdescent : baseEnd_3642260 < baseStart_3642260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642268 : List Nat := [2, 2, 3, 3, 3, 1, 2, 1, 2, 4]
def baseStart_3642268 : Nat := 118140960795 + 3642268 * 2 ^ 59
def prefixEnd_3642268 : Nat := 4983230072969 + 3 ^ 40 * 3642268 * 2
def baseEnd_3642268 : Nat := 623411385496753614466507

theorem tailTrace_3642268 : CollatzResearch.WordTrace tailWord_3642268 prefixEnd_3642268 623411385496753614466507 := by
  unfold tailWord_3642268
  simp only [CollatzResearch.WordTrace]
  refine ⟨66422213784346280347795729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88562951712461707130394305 66422213784346280347795729)
  ·
    refine ⟨49816660338259710260846797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66422213784346280347795729 49816660338259710260846797)
    ·
      refine ⟨18681247626847391347817549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49816660338259710260846797 18681247626847391347817549)
      ·
        refine ⟨7005467860067771755431581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18681247626847391347817549 7005467860067771755431581)
        ·
          refine ⟨2627050447525414408286843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7005467860067771755431581 2627050447525414408286843)
          ·
            refine ⟨3940575671288121612430265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2627050447525414408286843 3940575671288121612430265)
            ·
              refine ⟨2955431753466091209322699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3940575671288121612430265 2955431753466091209322699)
              ·
                refine ⟨4433147630199136813984049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955431753466091209322699 4433147630199136813984049)
                ·
                  refine ⟨3324860722649352610488037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4433147630199136813984049 3324860722649352610488037)
                  ·
                    refine ⟨623411385496753614466507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3324860722649352610488037 623411385496753614466507)
                    ·
                      rfl

theorem cell23_3642268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_3642268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642268 prefixEnd_3642268 := by exact prefixLift 3642268
  have htrace : WordTrace (prefixWord ++ tailWord_3642268) baseStart_3642268 baseEnd_3642268 := by
    simpa [prefixWord, tailWord_3642268, baseEnd_3642268] using wordTrace_append hprefix tailTrace_3642268
  have hstable : (prefixWord ++ tailWord_3642268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642268).length < 2 ^ (prefixWord ++ tailWord_3642268).sum := by decide
  have hdescent : baseEnd_3642268 < baseStart_3642268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642283 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 5]
def baseStart_3642283 : Nat := 118140960795 + 3642283 * 2 ^ 59
def prefixEnd_3642283 : Nat := 4983230072969 + 3 ^ 40 * 3642283 * 2
def baseEnd_3642283 : Nat := 1870241858700078284711951

theorem tailTrace_3642283 : CollatzResearch.WordTrace tailWord_3642283 prefixEnd_3642283 1870241858700078284711951 := by
  unfold tailWord_3642283
  simp only [CollatzResearch.WordTrace]
  refine ⟨132844974663638218257387503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88563316442425478838258335 132844974663638218257387503)
  ·
    refine ⟨199267461995457327386081255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132844974663638218257387503 199267461995457327386081255)
    ·
      refine ⟨298901192993185991079121883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199267461995457327386081255 298901192993185991079121883)
      ·
        refine ⟨448351789489778986618682825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298901192993185991079121883 448351789489778986618682825)
        ·
          refine ⟨336263842117334239964012119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448351789489778986618682825 336263842117334239964012119)
          ·
            refine ⟨504395763176001359946018179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336263842117334239964012119 504395763176001359946018179)
            ·
              refine ⟨756593644764002039919027269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504395763176001359946018179 756593644764002039919027269)
              ·
                refine ⟨141861308393250382484817613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 756593644764002039919027269 141861308393250382484817613)
                ·
                  refine ⟨53197990647468893431806605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141861308393250382484817613 53197990647468893431806605)
                  ·
                    refine ⟨19949246492800835036927477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53197990647468893431806605 19949246492800835036927477)
                    ·
                      refine ⟨1870241858700078284711951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19949246492800835036927477 1870241858700078284711951)
                      ·
                        rfl

theorem cell23_3642283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 5].length) (baseStart_3642283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642283 prefixEnd_3642283 := by exact prefixLift 3642283
  have htrace : WordTrace (prefixWord ++ tailWord_3642283) baseStart_3642283 baseEnd_3642283 := by
    simpa [prefixWord, tailWord_3642283, baseEnd_3642283] using wordTrace_append hprefix tailTrace_3642283
  have hstable : (prefixWord ++ tailWord_3642283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642283).length < 2 ^ (prefixWord ++ tailWord_3642283).sum := by decide
  have hdescent : baseEnd_3642283 < baseStart_3642283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642297 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 3, 4, 2]
def baseStart_3642297 : Nat := 118140960795 + 3642297 * 2 ^ 59
def prefixEnd_3642297 : Nat := 4983230072969 + 3 ^ 40 * 3642297 * 2
def baseEnd_3642297 : Nat := 1870249047429241229936887

theorem tailTrace_3642297 : CollatzResearch.WordTrace tailWord_3642297 prefixEnd_3642297 1870249047429241229936887 := by
  unfold tailWord_3642297
  simp only [CollatzResearch.WordTrace]
  refine ⟨132845485285587498648397145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88563656857058332432264763 132845485285587498648397145)
  ·
    refine ⟨99634113964190623986297859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132845485285587498648397145 99634113964190623986297859)
    ·
      refine ⟨149451170946285935979446789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99634113964190623986297859 149451170946285935979446789)
      ·
        refine ⟨28022094552428612996146273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149451170946285935979446789 28022094552428612996146273)
        ·
          refine ⟨21016570914321459747109705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28022094552428612996146273 21016570914321459747109705)
          ·
            refine ⟨15762428185741094810332279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21016570914321459747109705 15762428185741094810332279)
            ·
              refine ⟨23643642278611642215498419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15762428185741094810332279 23643642278611642215498419)
              ·
                refine ⟨35465463417917463323247629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23643642278611642215498419 35465463417917463323247629)
                ·
                  refine ⟨13299548781719048746217861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35465463417917463323247629 13299548781719048746217861)
                  ·
                    refine ⟨2493665396572321639915849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13299548781719048746217861 2493665396572321639915849)
                    ·
                      refine ⟨1870249047429241229936887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2493665396572321639915849 1870249047429241229936887)
                      ·
                        rfl

theorem cell23_3642297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_3642297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642297 prefixEnd_3642297 := by exact prefixLift 3642297
  have htrace : WordTrace (prefixWord ++ tailWord_3642297) baseStart_3642297 baseEnd_3642297 := by
    simpa [prefixWord, tailWord_3642297, baseEnd_3642297] using wordTrace_append hprefix tailTrace_3642297
  have hstable : (prefixWord ++ tailWord_3642297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642297).length < 2 ^ (prefixWord ++ tailWord_3642297).sum := by decide
  have hdescent : baseEnd_3642297 < baseStart_3642297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642303 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 11]
def baseStart_3642303 : Nat := 118140960795 + 3642303 * 2 ^ 59
def prefixEnd_3642303 : Nat := 4983230072969 + 3 ^ 40 * 3642303 * 2
def baseEnd_3642303 : Nat := 207805792034796467384651

theorem tailTrace_3642303 : CollatzResearch.WordTrace tailWord_3642303 prefixEnd_3642303 207805792034796467384651 := by
  unfold tailWord_3642303
  simp only [CollatzResearch.WordTrace]
  refine ⟨132845704123565761673115563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88563802749043841115410375 132845704123565761673115563)
  ·
    refine ⟨199268556185348642509673345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132845704123565761673115563 199268556185348642509673345)
    ·
      refine ⟨149451417139011481882255009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199268556185348642509673345 149451417139011481882255009)
      ·
        refine ⟨112088562854258611411691257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149451417139011481882255009 112088562854258611411691257)
        ·
          refine ⟨84066422140693958558768443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112088562854258611411691257 84066422140693958558768443)
          ·
            refine ⟨126099633211040937838152665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84066422140693958558768443 126099633211040937838152665)
            ·
              refine ⟨94574724908280703378614499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126099633211040937838152665 94574724908280703378614499)
              ·
                refine ⟨141862087362421055067921749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94574724908280703378614499 141862087362421055067921749)
                ·
                  refine ⟨207805792034796467384651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 141862087362421055067921749 207805792034796467384651)
                  ·
                    rfl

theorem cell23_3642303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 11].length) (baseStart_3642303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642303 prefixEnd_3642303 := by exact prefixLift 3642303
  have htrace : WordTrace (prefixWord ++ tailWord_3642303) baseStart_3642303 baseEnd_3642303 := by
    simpa [prefixWord, tailWord_3642303, baseEnd_3642303] using wordTrace_append hprefix tailTrace_3642303
  have hstable : (prefixWord ++ tailWord_3642303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642303).length < 2 ^ (prefixWord ++ tailWord_3642303).sum := by decide
  have hdescent : baseEnd_3642303 < baseStart_3642303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642308 : List Nat := [2, 3, 3, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3642308 : Nat := 118140960795 + 3642308 * 2 ^ 59
def prefixEnd_3642308 : Nat := 4983230072969 + 3 ^ 40 * 3642308 * 2
def baseEnd_3642308 : Nat := 1870254695716440686899337

theorem tailTrace_3642308 : CollatzResearch.WordTrace tailWord_3642308 prefixEnd_3642308 1870254695716440686899337 := by
  unfold tailWord_3642308
  simp only [CollatzResearch.WordTrace]
  refine ⟨66422943244273823763523789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88563924325698431684698385 66422943244273823763523789)
  ·
    refine ⟨24908603716602683911321421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66422943244273823763523789 24908603716602683911321421)
    ·
      refine ⟨9340726393726006466745533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24908603716602683911321421 9340726393726006466745533)
      ·
        refine ⟨3502772397647252425029575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9340726393726006466745533 3502772397647252425029575)
        ·
          refine ⟨5254158596470878637544363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3502772397647252425029575 5254158596470878637544363)
          ·
            refine ⟨7881237894706317956316545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5254158596470878637544363 7881237894706317956316545)
            ·
              refine ⟨5910928421029738467237409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7881237894706317956316545 5910928421029738467237409)
              ·
                refine ⟨4433196315772303850428057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5910928421029738467237409 4433196315772303850428057)
                ·
                  refine ⟨3324897236829227887821043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4433196315772303850428057 3324897236829227887821043)
                  ·
                    refine ⟨4987345855243841831731565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3324897236829227887821043 4987345855243841831731565)
                    ·
                      refine ⟨1870254695716440686899337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4987345855243841831731565 1870254695716440686899337)
                      ·
                        rfl

theorem cell23_3642308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3642308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642308 prefixEnd_3642308 := by exact prefixLift 3642308
  have htrace : WordTrace (prefixWord ++ tailWord_3642308) baseStart_3642308 baseEnd_3642308 := by
    simpa [prefixWord, tailWord_3642308, baseEnd_3642308] using wordTrace_append hprefix tailTrace_3642308
  have hstable : (prefixWord ++ tailWord_3642308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642308).length < 2 ^ (prefixWord ++ tailWord_3642308).sum := by decide
  have hdescent : baseEnd_3642308 < baseStart_3642308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642424 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 2, 2, 3]
def baseStart_3642424 : Nat := 118140960795 + 3642424 * 2 ^ 59
def prefixEnd_3642424 : Nat := 4983230072969 + 3 ^ 40 * 3642424 * 2
def baseEnd_3642424 : Nat := 1870314259472362233048803

theorem tailTrace_3642424 : CollatzResearch.WordTrace tailWord_3642424 prefixEnd_3642424 1870314259472362233048803 := by
  unfold tailWord_3642424
  simp only [CollatzResearch.WordTrace]
  refine ⟨66425058678063699669135163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88566744904084932892180217 66425058678063699669135163)
  ·
    refine ⟨99637588017095549503702745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66425058678063699669135163 99637588017095549503702745)
    ·
      refine ⟨74728191012821662127777059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99637588017095549503702745 74728191012821662127777059)
      ·
        refine ⟨112092286519232493191665589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74728191012821662127777059 112092286519232493191665589)
        ·
          refine ⟨10508651861178046236718649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112092286519232493191665589 10508651861178046236718649)
          ·
            refine ⟨7881488895883534677538987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10508651861178046236718649 7881488895883534677538987)
            ·
              refine ⟨11822233343825302016308481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7881488895883534677538987 11822233343825302016308481)
              ·
                refine ⟨8866675007868976512231361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11822233343825302016308481 8866675007868976512231361)
                ·
                  refine ⟨6650006255901732384173521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8866675007868976512231361 6650006255901732384173521)
                  ·
                    refine ⟨4987504691926299288130141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6650006255901732384173521 4987504691926299288130141)
                    ·
                      refine ⟨1870314259472362233048803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4987504691926299288130141 1870314259472362233048803)
                      ·
                        rfl

theorem cell23_3642424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_3642424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642424 prefixEnd_3642424 := by exact prefixLift 3642424
  have htrace : WordTrace (prefixWord ++ tailWord_3642424) baseStart_3642424 baseEnd_3642424 := by
    simpa [prefixWord, tailWord_3642424, baseEnd_3642424] using wordTrace_append hprefix tailTrace_3642424
  have hstable : (prefixWord ++ tailWord_3642424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642424).length < 2 ^ (prefixWord ++ tailWord_3642424).sum := by decide
  have hdescent : baseEnd_3642424 < baseStart_3642424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642457 : List Nat := [1, 2, 1, 2, 2, 1, 2, 6, 1, 5]
def baseStart_3642457 : Nat := 118140960795 + 3642457 * 2 ^ 59
def prefixEnd_3642457 : Nat := 4983230072969 + 3 ^ 40 * 3642457 * 2
def baseEnd_3642457 : Nat := 623443734777986867978717

theorem tailTrace_3642457 : CollatzResearch.WordTrace tailWord_3642457 prefixEnd_3642457 623443734777986867978717 := by
  unfold tailWord_3642457
  simp only [CollatzResearch.WordTrace]
  refine ⟨132851320965007845974221625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88567547310005230649481083 132851320965007845974221625)
  ·
    refine ⟨99638490723755884480666219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132851320965007845974221625 99638490723755884480666219)
    ·
      refine ⟨149457736085633826720999329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99638490723755884480666219 149457736085633826720999329)
      ·
        refine ⟨112093302064225370040749497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149457736085633826720999329 112093302064225370040749497)
        ·
          refine ⟨84069976548169027530562123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112093302064225370040749497 84069976548169027530562123)
          ·
            refine ⟨126104964822253541295843185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84069976548169027530562123 126104964822253541295843185)
            ·
              refine ⟨94578723616690155971882389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126104964822253541295843185 94578723616690155971882389)
              ·
                refine ⟨4433377669532351061181987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94578723616690155971882389 4433377669532351061181987)
                ·
                  refine ⟨6650066504298526591772981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4433377669532351061181987 6650066504298526591772981)
                  ·
                    refine ⟨623443734777986867978717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6650066504298526591772981 623443734777986867978717)
                    ·
                      rfl

theorem cell23_3642457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 5].length) (baseStart_3642457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642457 prefixEnd_3642457 := by exact prefixLift 3642457
  have htrace : WordTrace (prefixWord ++ tailWord_3642457) baseStart_3642457 baseEnd_3642457 := by
    simpa [prefixWord, tailWord_3642457, baseEnd_3642457] using wordTrace_append hprefix tailTrace_3642457
  have hstable : (prefixWord ++ tailWord_3642457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642457).length < 2 ^ (prefixWord ++ tailWord_3642457).sum := by decide
  have hdescent : baseEnd_3642457 < baseStart_3642457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642488 : List Nat := [2, 1, 2, 1, 1, 1, 8, 2, 1, 1, 3]
def baseStart_3642488 : Nat := 118140960795 + 3642488 * 2 ^ 59
def prefixEnd_3642488 : Nat := 4983230072969 + 3 ^ 40 * 3642488 * 2
def baseEnd_3642488 : Nat := 1870347122234249982648509

theorem tailTrace_3642488 : CollatzResearch.WordTrace tailWord_3642488 prefixEnd_3642488 1870347122234249982648509 := by
  unfold tailWord_3642488
  simp only [CollatzResearch.WordTrace]
  refine ⟨66426225813947769134300059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88568301085263692179066745 66426225813947769134300059)
  ·
    refine ⟨99639338720921653701450089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66426225813947769134300059 99639338720921653701450089)
    ·
      refine ⟨74729504040691240276087567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99639338720921653701450089 74729504040691240276087567)
      ·
        refine ⟨112094256061036860414131351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74729504040691240276087567 112094256061036860414131351)
        ·
          refine ⟨168141384091555290621197027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112094256061036860414131351 168141384091555290621197027)
          ·
            refine ⟨252212076137332935931795541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168141384091555290621197027 252212076137332935931795541)
            ·
              refine ⟨2955610267234370342950729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 252212076137332935931795541 2955610267234370342950729)
              ·
                refine ⟨2216707700425777757213047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2955610267234370342950729 2216707700425777757213047)
                ·
                  refine ⟨3325061550638666635819571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216707700425777757213047 3325061550638666635819571)
                  ·
                    refine ⟨4987592325957999953729357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3325061550638666635819571 4987592325957999953729357)
                    ·
                      refine ⟨1870347122234249982648509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4987592325957999953729357 1870347122234249982648509)
                      ·
                        rfl

theorem cell23_3642488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 1, 1, 3].length) (baseStart_3642488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642488 prefixEnd_3642488 := by exact prefixLift 3642488
  have htrace : WordTrace (prefixWord ++ tailWord_3642488) baseStart_3642488 baseEnd_3642488 := by
    simpa [prefixWord, tailWord_3642488, baseEnd_3642488] using wordTrace_append hprefix tailTrace_3642488
  have hstable : (prefixWord ++ tailWord_3642488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642488).length < 2 ^ (prefixWord ++ tailWord_3642488).sum := by decide
  have hdescent : baseEnd_3642488 < baseStart_3642488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642524 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_3642524 : Nat := 118140960795 + 3642524 * 2 ^ 59
def prefixEnd_3642524 : Nat := 4983230072969 + 3 ^ 40 * 3642524 * 2
def baseEnd_3642524 : Nat := 1870365607537811841798343

theorem tailTrace_3642524 : CollatzResearch.WordTrace tailWord_3642524 prefixEnd_3642524 1870365607537811841798343 := by
  unfold tailWord_3642524
  simp only [CollatzResearch.WordTrace]
  refine ⟨66426882327882558208455313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88569176437176744277940417 66426882327882558208455313)
  ·
    refine ⟨49820161745911918656341485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66426882327882558208455313 49820161745911918656341485)
    ·
      refine ⟨18682560654716969496128057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49820161745911918656341485 18682560654716969496128057)
      ·
        refine ⟨14011920491037727122096043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18682560654716969496128057 14011920491037727122096043)
        ·
          refine ⟨21017880736556590683144065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14011920491037727122096043 21017880736556590683144065)
          ·
            refine ⟨15763410552417443012358049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21017880736556590683144065 15763410552417443012358049)
            ·
              refine ⟨11822557914313082259268537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15763410552417443012358049 11822557914313082259268537)
              ·
                refine ⟨8866918435734811694451403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11822557914313082259268537 8866918435734811694451403)
                ·
                  refine ⟨13300377653602217541677105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8866918435734811694451403 13300377653602217541677105)
                  ·
                    refine ⟨9975283240201663156257829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13300377653602217541677105 9975283240201663156257829)
                    ·
                      refine ⟨1870365607537811841798343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9975283240201663156257829 1870365607537811841798343)
                      ·
                        rfl

theorem cell23_3642524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_3642524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642524 prefixEnd_3642524 := by exact prefixLift 3642524
  have htrace : WordTrace (prefixWord ++ tailWord_3642524) baseStart_3642524 baseEnd_3642524 := by
    simpa [prefixWord, tailWord_3642524, baseEnd_3642524] using wordTrace_append hprefix tailTrace_3642524
  have hstable : (prefixWord ++ tailWord_3642524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642524).length < 2 ^ (prefixWord ++ tailWord_3642524).sum := by decide
  have hdescent : baseEnd_3642524 < baseStart_3642524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642538 : List Nat := [3, 1, 5, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3642538 : Nat := 118140960795 + 3642538 * 2 ^ 59
def prefixEnd_3642538 : Nat := 4983230072969 + 3 ^ 40 * 3642538 * 2
def baseEnd_3642538 : Nat := 623457598755658262341093

theorem tailTrace_3642538 : CollatzResearch.WordTrace tailWord_3642538 prefixEnd_3642538 623457598755658262341093 := by
  unfold tailWord_3642538
  simp only [CollatzResearch.WordTrace]
  refine ⟨33213568819428599201980067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88569516851809597871946845 33213568819428599201980067)
  ·
    refine ⟨49820353229142898802970101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33213568819428599201980067 49820353229142898802970101)
    ·
      refine ⟨4670658115232146762778447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49820353229142898802970101 4670658115232146762778447)
      ·
        refine ⟨7005987172848220144167671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4670658115232146762778447 7005987172848220144167671)
        ·
          refine ⟨10508980759272330216251507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7005987172848220144167671 10508980759272330216251507)
          ·
            refine ⟨15763471138908495324377261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10508980759272330216251507 15763471138908495324377261)
            ·
              refine ⟨5911301677090685746641473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15763471138908495324377261 5911301677090685746641473)
              ·
                refine ⟨4433476257818014309981105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5911301677090685746641473 4433476257818014309981105)
                ·
                  refine ⟨3325107193363510732485829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4433476257818014309981105 3325107193363510732485829)
                  ·
                    refine ⟨623457598755658262341093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3325107193363510732485829 623457598755658262341093)
                    ·
                      rfl

theorem cell23_3642538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3642538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642538 prefixEnd_3642538 := by exact prefixLift 3642538
  have htrace : WordTrace (prefixWord ++ tailWord_3642538) baseStart_3642538 baseEnd_3642538 := by
    simpa [prefixWord, tailWord_3642538, baseEnd_3642538] using wordTrace_append hprefix tailTrace_3642538
  have hstable : (prefixWord ++ tailWord_3642538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642538).length < 2 ^ (prefixWord ++ tailWord_3642538).sum := by decide
  have hdescent : baseEnd_3642538 < baseStart_3642538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642544 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 4, 1, 3]
def baseStart_3642544 : Nat := 118140960795 + 3642544 * 2 ^ 59
def prefixEnd_3642544 : Nat := 4983230072969 + 3 ^ 40 * 3642544 * 2
def baseEnd_3642544 : Nat := 1870375877150901763548251

theorem tailTrace_3642544 : CollatzResearch.WordTrace tailWord_3642544 prefixEnd_3642544 1870375877150901763548251 := by
  unfold tailWord_3642544
  simp only [CollatzResearch.WordTrace]
  refine ⟨66427247057846329916319343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88569662743795106555092457 66427247057846329916319343)
  ·
    refine ⟨99640870586769494874479015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66427247057846329916319343 99640870586769494874479015)
    ·
      refine ⟨149461305880154242311718523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99640870586769494874479015 149461305880154242311718523)
      ·
        refine ⟨224191958820231363467577785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149461305880154242311718523 224191958820231363467577785)
        ·
          refine ⟨168143969115173522600683339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224191958820231363467577785 168143969115173522600683339)
          ·
            refine ⟨252215953672760283901025009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168143969115173522600683339 252215953672760283901025009)
            ·
              refine ⟨189161965254570212925768757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252215953672760283901025009 189161965254570212925768757)
              ·
                refine ⟨17733934242615957461790821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189161965254570212925768757 17733934242615957461790821)
                ·
                  refine ⟨3325112670490492024085779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17733934242615957461790821 3325112670490492024085779)
                  ·
                    refine ⟨4987669005735738036128669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3325112670490492024085779 4987669005735738036128669)
                    ·
                      refine ⟨1870375877150901763548251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4987669005735738036128669 1870375877150901763548251)
                      ·
                        rfl

theorem cell23_3642544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 4, 1, 3].length) (baseStart_3642544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642544 prefixEnd_3642544 := by exact prefixLift 3642544
  have htrace : WordTrace (prefixWord ++ tailWord_3642544) baseStart_3642544 baseEnd_3642544 := by
    simpa [prefixWord, tailWord_3642544, baseEnd_3642544] using wordTrace_append hprefix tailTrace_3642544
  have hstable : (prefixWord ++ tailWord_3642544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642544).length < 2 ^ (prefixWord ++ tailWord_3642544).sum := by decide
  have hdescent : baseEnd_3642544 < baseStart_3642544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642545 : List Nat := [1, 2, 2, 5, 1, 1, 2, 4, 1, 2, 2]
def baseStart_3642545 : Nat := 118140960795 + 3642545 * 2 ^ 59
def prefixEnd_3642545 : Nat := 4983230072969 + 3 ^ 40 * 3642545 * 2
def baseEnd_3642545 : Nat := 1870376390631556259635747

theorem tailTrace_3642545 : CollatzResearch.WordTrace tailWord_3642545 prefixEnd_3642545 1870376390631556259635747 := by
  unfold tailWord_3642545
  simp only [CollatzResearch.WordTrace]
  refine ⟨132854530588689037003425089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88569687059126024668950059 132854530588689037003425089)
  ·
    refine ⟨99640897941516777752568817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132854530588689037003425089 99640897941516777752568817)
    ·
      refine ⟨74730673456137583314426613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99640897941516777752568817 74730673456137583314426613)
      ·
        refine ⟨7006000636512898435727495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74730673456137583314426613 7006000636512898435727495)
        ·
          refine ⟨10509000954769347653591243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7006000636512898435727495 10509000954769347653591243)
          ·
            refine ⟨15763501432154021480386865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10509000954769347653591243 15763501432154021480386865)
            ·
              refine ⟨11822626074115516110290149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15763501432154021480386865 11822626074115516110290149)
              ·
                refine ⟨2216742388896659270679403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11822626074115516110290149 2216742388896659270679403)
                ·
                  refine ⟨3325113583344988906019105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2216742388896659270679403 3325113583344988906019105)
                  ·
                    refine ⟨2493835187508741679514329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3325113583344988906019105 2493835187508741679514329)
                    ·
                      refine ⟨1870376390631556259635747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2493835187508741679514329 1870376390631556259635747)
                      ·
                        rfl

theorem cell23_3642545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_3642545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642545 prefixEnd_3642545 := by exact prefixLift 3642545
  have htrace : WordTrace (prefixWord ++ tailWord_3642545) baseStart_3642545 baseEnd_3642545 := by
    simpa [prefixWord, tailWord_3642545, baseEnd_3642545] using wordTrace_append hprefix tailTrace_3642545
  have hstable : (prefixWord ++ tailWord_3642545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642545).length < 2 ^ (prefixWord ++ tailWord_3642545).sum := by decide
  have hdescent : baseEnd_3642545 < baseStart_3642545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642567 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_3642567 : Nat := 118140960795 + 3642567 * 2 ^ 59
def prefixEnd_3642567 : Nat := 4983230072969 + 3 ^ 40 * 3642567 * 2
def baseEnd_3642567 : Nat := 1870387687205955173560645

theorem tailTrace_3642567 : CollatzResearch.WordTrace tailWord_3642567 prefixEnd_3642567 1870387687205955173560645 := by
  unfold tailWord_3642567
  simp only [CollatzResearch.WordTrace]
  refine ⟨132855332994609334760725955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88570221996406223173817303 132855332994609334760725955)
  ·
    refine ⟨199282999491914002141088933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132855332994609334760725955 199282999491914002141088933)
    ·
      refine ⟨37365562404733875401454175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199282999491914002141088933 37365562404733875401454175)
      ·
        refine ⟨56048343607100813102181263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37365562404733875401454175 56048343607100813102181263)
        ·
          refine ⟨84072515410651219653271895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56048343607100813102181263 84072515410651219653271895)
          ·
            refine ⟨126108773115976829479907843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84072515410651219653271895 126108773115976829479907843)
            ·
              refine ⟨189163159673965244219861765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126108773115976829479907843 189163159673965244219861765)
              ·
                refine ⟨35468092438868483291224081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189163159673965244219861765 35468092438868483291224081)
                ·
                  refine ⟨26601069329151362468418061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35468092438868483291224081 26601069329151362468418061)
                  ·
                    refine ⟨9975400998431760925656773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26601069329151362468418061 9975400998431760925656773)
                    ·
                      refine ⟨1870387687205955173560645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9975400998431760925656773 1870387687205955173560645)
                      ·
                        rfl

theorem cell23_3642567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_3642567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642567 prefixEnd_3642567 := by exact prefixLift 3642567
  have htrace : WordTrace (prefixWord ++ tailWord_3642567) baseStart_3642567 baseEnd_3642567 := by
    simpa [prefixWord, tailWord_3642567, baseEnd_3642567] using wordTrace_append hprefix tailTrace_3642567
  have hstable : (prefixWord ++ tailWord_3642567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642567).length < 2 ^ (prefixWord ++ tailWord_3642567).sum := by decide
  have hdescent : baseEnd_3642567 < baseStart_3642567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642614 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3642614 : Nat := 118140960795 + 3642614 * 2 ^ 59
def prefixEnd_3642614 : Nat := 4983230072969 + 3 ^ 40 * 3642614 * 2
def baseEnd_3642614 : Nat := 1870411820796716489672929

theorem tailTrace_3642614 : CollatzResearch.WordTrace tailWord_3642614 prefixEnd_3642614 1870411820796716489672929 := by
  unfold tailWord_3642614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8303565451589941361730431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88571364816959374525124597 8303565451589941361730431)
  ·
    refine ⟨12455348177384912042595647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8303565451589941361730431 12455348177384912042595647)
    ·
      refine ⟨18683022266077368063893471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12455348177384912042595647 18683022266077368063893471)
      ·
        refine ⟨28024533399116052095840207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18683022266077368063893471 28024533399116052095840207)
        ·
          refine ⟨42036800098674078143760311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28024533399116052095840207 42036800098674078143760311)
          ·
            refine ⟨63055200148011117215640467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42036800098674078143760311 63055200148011117215640467)
            ·
              refine ⟨94582800222016675823460701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63055200148011117215640467 94582800222016675823460701)
              ·
                refine ⟨35468550083256253433797763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94582800222016675823460701 35468550083256253433797763)
                ·
                  refine ⟨53202825124884380150696645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35468550083256253433797763 53202825124884380150696645)
                  ·
                    refine ⟨9975529710915821278255621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53202825124884380150696645 9975529710915821278255621)
                    ·
                      refine ⟨1870411820796716489672929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9975529710915821278255621 1870411820796716489672929)
                      ·
                        rfl

theorem cell23_3642614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3642614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642614 prefixEnd_3642614 := by exact prefixLift 3642614
  have htrace : WordTrace (prefixWord ++ tailWord_3642614) baseStart_3642614 baseEnd_3642614 := by
    simpa [prefixWord, tailWord_3642614, baseEnd_3642614] using wordTrace_append hprefix tailTrace_3642614
  have hstable : (prefixWord ++ tailWord_3642614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642614).length < 2 ^ (prefixWord ++ tailWord_3642614).sum := by decide
  have hdescent : baseEnd_3642614 < baseStart_3642614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642618 : List Nat := [3, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2]
def baseStart_3642618 : Nat := 118140960795 + 3642618 * 2 ^ 59
def prefixEnd_3642618 : Nat := 4983230072969 + 3 ^ 40 * 3642618 * 2
def baseEnd_3642618 : Nat := 1870413874719334474022911

theorem tailTrace_3642618 : CollatzResearch.WordTrace tailWord_3642618 prefixEnd_3642618 1870413874719334474022911 := by
  unfold tailWord_3642618
  simp only [CollatzResearch.WordTrace]
  refine ⟨33214298279356142617708127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88571462078283046980555005 33214298279356142617708127)
  ·
    refine ⟨49821447419034213926562191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33214298279356142617708127 49821447419034213926562191)
    ·
      refine ⟨74732171128551320889843287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49821447419034213926562191 74732171128551320889843287)
      ·
        refine ⟨112098256692826981334764931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74732171128551320889843287 112098256692826981334764931)
        ·
          refine ⟨168147385039240472002147397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112098256692826981334764931 168147385039240472002147397)
          ·
            refine ⟨31527634694857588500402637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168147385039240472002147397 31527634694857588500402637)
            ·
              refine ⟨11822863010571595687650989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31527634694857588500402637 11822863010571595687650989)
              ·
                refine ⟨4433573628964348382869121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11822863010571595687650989 4433573628964348382869121)
                ·
                  refine ⟨3325180221723261287151841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4433573628964348382869121 3325180221723261287151841)
                  ·
                    refine ⟨2493885166292445965363881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3325180221723261287151841 2493885166292445965363881)
                    ·
                      refine ⟨1870413874719334474022911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2493885166292445965363881 1870413874719334474022911)
                      ·
                        rfl

theorem cell23_3642618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2].length) (baseStart_3642618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642618 prefixEnd_3642618 := by exact prefixLift 3642618
  have htrace : WordTrace (prefixWord ++ tailWord_3642618) baseStart_3642618 baseEnd_3642618 := by
    simpa [prefixWord, tailWord_3642618, baseEnd_3642618] using wordTrace_append hprefix tailTrace_3642618
  have hstable : (prefixWord ++ tailWord_3642618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642618).length < 2 ^ (prefixWord ++ tailWord_3642618).sum := by decide
  have hdescent : baseEnd_3642618 < baseStart_3642618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642634 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_3642634 : Nat := 118140960795 + 3642634 * 2 ^ 59
def prefixEnd_3642634 : Nat := 4983230072969 + 3 ^ 40 * 3642634 * 2
def baseEnd_3642634 : Nat := 1870422090409806411422837

theorem tailTrace_3642634 : CollatzResearch.WordTrace tailWord_3642634 prefixEnd_3642634 1870422090409806411422837 := by
  unfold tailWord_3642634
  simp only [CollatzResearch.WordTrace]
  refine ⟨33214444171341651300853739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88571851123577736802276637 33214444171341651300853739)
  ·
    refine ⟨49821666257012476951280609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33214444171341651300853739 49821666257012476951280609)
    ·
      refine ⟨37366249692759357713460457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49821666257012476951280609 37366249692759357713460457)
      ·
        refine ⟨28024687269569518285095343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37366249692759357713460457 28024687269569518285095343)
        ·
          refine ⟨42037030904354277427643015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28024687269569518285095343 42037030904354277427643015)
          ·
            refine ⟨63055546356531416141464523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42037030904354277427643015 63055546356531416141464523)
            ·
              refine ⟨94583319534797124212196785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63055546356531416141464523 94583319534797124212196785)
              ·
                refine ⟨70937489651097843159147589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94583319534797124212196785 70937489651097843159147589)
                ·
                  refine ⟨13300779309580845592340173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70937489651097843159147589 13300779309580845592340173)
                  ·
                    refine ⟨4987792241092817097127565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13300779309580845592340173 4987792241092817097127565)
                    ·
                      refine ⟨1870422090409806411422837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4987792241092817097127565 1870422090409806411422837)
                      ·
                        rfl

theorem cell23_3642634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_3642634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642634 prefixEnd_3642634 := by exact prefixLift 3642634
  have htrace : WordTrace (prefixWord ++ tailWord_3642634) baseStart_3642634 baseEnd_3642634 := by
    simpa [prefixWord, tailWord_3642634, baseEnd_3642634] using wordTrace_append hprefix tailTrace_3642634
  have hstable : (prefixWord ++ tailWord_3642634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642634).length < 2 ^ (prefixWord ++ tailWord_3642634).sum := by decide
  have hdescent : baseEnd_3642634 < baseStart_3642634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642658 : List Nat := [3, 3, 1, 1, 4, 1, 1, 4, 5]
def baseStart_3642658 : Nat := 118140960795 + 3642658 * 2 ^ 59
def prefixEnd_3642658 : Nat := 4983230072969 + 3 ^ 40 * 3642658 * 2
def baseEnd_3642658 : Nat := 207826045993946035280303

theorem tailTrace_3642658 : CollatzResearch.WordTrace tailWord_3642658 prefixEnd_3642658 207826045993946035280303 := by
  unfold tailWord_3642658
  simp only [CollatzResearch.WordTrace]
  refine ⟨33214663009319914325572157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88572434691519771534859085 33214663009319914325572157)
  ·
    refine ⟨12455498628494967872089559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33214663009319914325572157 12455498628494967872089559)
    ·
      refine ⟨18683247942742451808134339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12455498628494967872089559 18683247942742451808134339)
      ·
        refine ⟨28024871914113677712201509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18683247942742451808134339 28024871914113677712201509)
        ·
          refine ⟨5254663483896314571037783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28024871914113677712201509 5254663483896314571037783)
          ·
            refine ⟨7881995225844471856556675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5254663483896314571037783 7881995225844471856556675)
            ·
              refine ⟨11822992838766707784835013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7881995225844471856556675 11822992838766707784835013)
              ·
                refine ⟨2216811157268757709656565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11822992838766707784835013 2216811157268757709656565)
                ·
                  refine ⟨207826045993946035280303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2216811157268757709656565 207826045993946035280303)
                  ·
                    rfl

theorem cell23_3642658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_3642658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642658 prefixEnd_3642658 := by exact prefixLift 3642658
  have htrace : WordTrace (prefixWord ++ tailWord_3642658) baseStart_3642658 baseEnd_3642658 := by
    simpa [prefixWord, tailWord_3642658, baseEnd_3642658] using wordTrace_append hprefix tailTrace_3642658
  have hstable : (prefixWord ++ tailWord_3642658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642658).length < 2 ^ (prefixWord ++ tailWord_3642658).sum := by decide
  have hdescent : baseEnd_3642658 < baseStart_3642658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642661 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 2, 5, 2]
def baseStart_3642661 : Nat := 118140960795 + 3642661 * 2 ^ 59
def prefixEnd_3642661 : Nat := 4983230072969 + 3 ^ 40 * 3642661 * 2
def baseEnd_3642661 : Nat := 1870435954387477805785213

theorem tailTrace_3642661 : CollatzResearch.WordTrace tailWord_3642661 prefixEnd_3642661 1870435954387477805785213 := by
  unfold tailWord_3642661
  simp only [CollatzResearch.WordTrace]
  refine ⟨132858761456268788814647837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88572507637512525876431891 132858761456268788814647837)
  ·
    refine ⟨49822035546100795805492939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132858761456268788814647837 49822035546100795805492939)
    ·
      refine ⟨74733053319151193708239409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49822035546100795805492939 74733053319151193708239409)
      ·
        refine ⟨56049789989363395281179557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74733053319151193708239409 56049789989363395281179557)
        ·
          refine ⟨10509335623005636615221167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56049789989363395281179557 10509335623005636615221167)
          ·
            refine ⟨15764003434508454922831751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10509335623005636615221167 15764003434508454922831751)
            ·
              refine ⟨23646005151762682384247627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15764003434508454922831751 23646005151762682384247627)
              ·
                refine ⟨35469007727644023576371441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23646005151762682384247627 35469007727644023576371441)
                ·
                  refine ⟨26601755795733017682278581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35469007727644023576371441 26601755795733017682278581)
                  ·
                    refine ⟨2493914605849970407713617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26601755795733017682278581 2493914605849970407713617)
                    ·
                      refine ⟨1870435954387477805785213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2493914605849970407713617 1870435954387477805785213)
                      ·
                        rfl

theorem cell23_3642661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_3642661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642661 prefixEnd_3642661 := by exact prefixLift 3642661
  have htrace : WordTrace (prefixWord ++ tailWord_3642661) baseStart_3642661 baseEnd_3642661 := by
    simpa [prefixWord, tailWord_3642661, baseEnd_3642661] using wordTrace_append hprefix tailTrace_3642661
  have hstable : (prefixWord ++ tailWord_3642661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642661).length < 2 ^ (prefixWord ++ tailWord_3642661).sum := by decide
  have hdescent : baseEnd_3642661 < baseStart_3642661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642782 : List Nat := [4, 3, 1, 2, 2, 2, 2, 1, 6]
def baseStart_3642782 : Nat := 118140960795 + 3642782 * 2 ^ 59
def prefixEnd_3642782 : Nat := 4983230072969 + 3 ^ 40 * 3642782 * 2
def baseEnd_3642782 : Nat := 207833120616296870263573

theorem tailTrace_3642782 : CollatzResearch.WordTrace tailWord_3642782 prefixEnd_3642782 207833120616296870263573 := by
  unfold tailWord_3642782
  simp only [CollatzResearch.WordTrace]
  refine ⟨16607896836103803309975325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88575449792553617653201733 16607896836103803309975325)
  ·
    refine ⟨6227961313538926241240747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16607896836103803309975325 6227961313538926241240747)
    ·
      refine ⟨9341941970308389361861121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6227961313538926241240747 9341941970308389361861121)
      ·
        refine ⟨7006456477731292021395841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9341941970308389361861121 7006456477731292021395841)
        ·
          refine ⟨5254842358298469016046881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7006456477731292021395841 5254842358298469016046881)
          ·
            refine ⟨3941131768723851762035161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5254842358298469016046881 3941131768723851762035161)
            ·
              refine ⟨2955848826542888821526371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3941131768723851762035161 2955848826542888821526371)
              ·
                refine ⟨4433773239814333232289557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955848826542888821526371 4433773239814333232289557)
                ·
                  refine ⟨207833120616296870263573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4433773239814333232289557 207833120616296870263573)
                  ·
                    rfl

theorem cell23_3642782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_3642782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642782 prefixEnd_3642782 := by exact prefixLift 3642782
  have htrace : WordTrace (prefixWord ++ tailWord_3642782) baseStart_3642782 baseEnd_3642782 := by
    simpa [prefixWord, tailWord_3642782, baseEnd_3642782] using wordTrace_append hprefix tailTrace_3642782
  have hstable : (prefixWord ++ tailWord_3642782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642782).length < 2 ^ (prefixWord ++ tailWord_3642782).sum := by decide
  have hdescent : baseEnd_3642782 < baseStart_3642782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642791 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 1, 6]
def baseStart_3642791 : Nat := 118140960795 + 3642791 * 2 ^ 59
def prefixEnd_3642791 : Nat := 4983230072969 + 3 ^ 40 * 3642791 * 2
def baseEnd_3642791 : Nat := 623500902290854099053205

theorem tailTrace_3642791 : CollatzResearch.WordTrace tailWord_3642791 prefixEnd_3642791 623500902290854099053205 := by
  unfold tailWord_3642791
  simp only [CollatzResearch.WordTrace]
  refine ⟨132863502945797821016880227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88575668630531880677920151 132863502945797821016880227)
  ·
    refine ⟨199295254418696731525320341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132863502945797821016880227 199295254418696731525320341)
    ·
      refine ⟨9341965050876409290249391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 199295254418696731525320341 9341965050876409290249391)
      ·
        refine ⟨14012947576314613935374087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9341965050876409290249391 14012947576314613935374087)
        ·
          refine ⟨21019421364471920903061131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14012947576314613935374087 21019421364471920903061131)
          ·
            refine ⟨31529132046707881354591697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21019421364471920903061131 31529132046707881354591697)
            ·
              refine ⟨23646849035030911015943773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31529132046707881354591697 23646849035030911015943773)
              ·
                refine ⟨8867568388136591630978915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23646849035030911015943773 8867568388136591630978915)
                ·
                  refine ⟨13301352582204887446468373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8867568388136591630978915 13301352582204887446468373)
                  ·
                    refine ⟨623500902290854099053205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13301352582204887446468373 623500902290854099053205)
                    ·
                      rfl

theorem cell23_3642791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_3642791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642791 prefixEnd_3642791 := by exact prefixLift 3642791
  have htrace : WordTrace (prefixWord ++ tailWord_3642791) baseStart_3642791 baseEnd_3642791 := by
    simpa [prefixWord, tailWord_3642791, baseEnd_3642791] using wordTrace_append hprefix tailTrace_3642791
  have hstable : (prefixWord ++ tailWord_3642791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642791).length < 2 ^ (prefixWord ++ tailWord_3642791).sum := by decide
  have hdescent : baseEnd_3642791 < baseStart_3642791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642838 : List Nat := [5, 2, 1, 1, 1, 2, 3, 8]
def baseStart_3642838 : Nat := 118140960795 + 3642838 * 2 ^ 59
def prefixEnd_3642838 : Nat := 4983230072969 + 3 ^ 40 * 3642838 * 2
def baseEnd_3642838 : Nat := 69278771869011985676737

theorem tailTrace_3642838 : CollatzResearch.WordTrace tailWord_3642838 prefixEnd_3642838 69278771869011985676737 := by
  unfold tailWord_3642838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8304076073539221752740073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88576811451085032029227445 8304076073539221752740073)
  ·
    refine ⟨6228057055154416314555055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8304076073539221752740073 6228057055154416314555055)
    ·
      refine ⟨9342085582731624471832583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6228057055154416314555055 9342085582731624471832583)
      ·
        refine ⟨14013128374097436707748875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9342085582731624471832583 14013128374097436707748875)
        ·
          refine ⟨21019692561146155061623313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14013128374097436707748875 21019692561146155061623313)
          ·
            refine ⟨15764769420859616296217485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21019692561146155061623313 15764769420859616296217485)
            ·
              refine ⟨5911788532822356111081557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15764769420859616296217485 5911788532822356111081557)
              ·
                refine ⟨69278771869011985676737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5911788532822356111081557 69278771869011985676737)
                ·
                  rfl

theorem cell23_3642838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_3642838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642838 prefixEnd_3642838 := by exact prefixLift 3642838
  have htrace : WordTrace (prefixWord ++ tailWord_3642838) baseStart_3642838 baseEnd_3642838 := by
    simpa [prefixWord, tailWord_3642838, baseEnd_3642838] using wordTrace_append hprefix tailTrace_3642838
  have hstable : (prefixWord ++ tailWord_3642838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642838).length < 2 ^ (prefixWord ++ tailWord_3642838).sum := by decide
  have hdescent : baseEnd_3642838 < baseStart_3642838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642869 : List Nat := [1, 3, 5, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_3642869 : Nat := 118140960795 + 3642869 * 2 ^ 59
def prefixEnd_3642869 : Nat := 4983230072969 + 3 ^ 40 * 3642869 * 2
def baseEnd_3642869 : Nat := 1870542758363612991984257

theorem tailTrace_3642869 : CollatzResearch.WordTrace tailWord_3642869 prefixEnd_3642869 1870542758363612991984257 := by
  unfold tailWord_3642869
  simp only [CollatzResearch.WordTrace]
  refine ⟨132866347839515240338219661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88577565226343493558813107 132866347839515240338219661)
  ·
    refine ⟨49824880439818215126832373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132866347839515240338219661 49824880439818215126832373)
    ·
      refine ⟨4671082541232957668140535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49824880439818215126832373 4671082541232957668140535)
      ·
        refine ⟨7006623811849436502210803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4671082541232957668140535 7006623811849436502210803)
        ·
          refine ⟨10509935717774154753316205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7006623811849436502210803 10509935717774154753316205)
          ·
            refine ⟨3941225894165308032493577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10509935717774154753316205 3941225894165308032493577)
            ·
              refine ⟨2955919420623981024370183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3941225894165308032493577 2955919420623981024370183)
              ·
                refine ⟨4433879130935971536555275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955919420623981024370183 4433879130935971536555275)
                ·
                  refine ⟨6650818696403957304832913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4433879130935971536555275 6650818696403957304832913)
                  ·
                    refine ⟨4988114022302967978624685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6650818696403957304832913 4988114022302967978624685)
                    ·
                      refine ⟨1870542758363612991984257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4988114022302967978624685 1870542758363612991984257)
                      ·
                        rfl

theorem cell23_3642869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_3642869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642869 prefixEnd_3642869 := by exact prefixLift 3642869
  have htrace : WordTrace (prefixWord ++ tailWord_3642869) baseStart_3642869 baseEnd_3642869 := by
    simpa [prefixWord, tailWord_3642869, baseEnd_3642869] using wordTrace_append hprefix tailTrace_3642869
  have hstable : (prefixWord ++ tailWord_3642869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642869).length < 2 ^ (prefixWord ++ tailWord_3642869).sum := by decide
  have hdescent : baseEnd_3642869 < baseStart_3642869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642882 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3642882 : Nat := 118140960795 + 3642882 * 2 ^ 59
def prefixEnd_3642882 : Nat := 4983230072969 + 3 ^ 40 * 3642882 * 2
def baseEnd_3642882 : Nat := 1870549433612121441121697

theorem tailTrace_3642882 : CollatzResearch.WordTrace tailWord_3642882 prefixEnd_3642882 1870549433612121441121697 := by
  unfold tailWord_3642882
  simp only [CollatzResearch.WordTrace]
  refine ⟨33216705497117035889610725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88577881325645429038961933 33216705497117035889610725)
  ·
    refine ⟨6228132280709444229302011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33216705497117035889610725 6228132280709444229302011)
    ·
      refine ⟨9342198421064166343953017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6228132280709444229302011 9342198421064166343953017)
      ·
        refine ⟨7006648815798124757964763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9342198421064166343953017 7006648815798124757964763)
        ·
          refine ⟨10509973223697187136947145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7006648815798124757964763 10509973223697187136947145)
          ·
            refine ⟨7882479917772890352710359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10509973223697187136947145 7882479917772890352710359)
            ·
              refine ⟨11823719876659335529065539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7882479917772890352710359 11823719876659335529065539)
              ·
                refine ⟨17735579814989003293598309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11823719876659335529065539 17735579814989003293598309)
                ·
                  refine ⟨3325421215310438117549683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17735579814989003293598309 3325421215310438117549683)
                  ·
                    refine ⟨4988131822965657176324525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3325421215310438117549683 4988131822965657176324525)
                    ·
                      refine ⟨1870549433612121441121697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4988131822965657176324525 1870549433612121441121697)
                      ·
                        rfl

theorem cell23_3642882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3642882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642882 prefixEnd_3642882 := by exact prefixLift 3642882
  have htrace : WordTrace (prefixWord ++ tailWord_3642882) baseStart_3642882 baseEnd_3642882 := by
    simpa [prefixWord, tailWord_3642882, baseEnd_3642882] using wordTrace_append hprefix tailTrace_3642882
  have hstable : (prefixWord ++ tailWord_3642882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642882).length < 2 ^ (prefixWord ++ tailWord_3642882).sum := by decide
  have hdescent : baseEnd_3642882 < baseStart_3642882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642888 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 3, 4, 2]
def baseStart_3642888 : Nat := 118140960795 + 3642888 * 2 ^ 59
def prefixEnd_3642888 : Nat := 4983230072969 + 3 ^ 40 * 3642888 * 2
def baseEnd_3642888 : Nat := 1870552514496048417646669

theorem tailTrace_3642888 : CollatzResearch.WordTrace tailWord_3642888 prefixEnd_3642888 1870552514496048417646669 := by
  unfold tailWord_3642888
  simp only [CollatzResearch.WordTrace]
  refine ⟨66433520413223203291580659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88578027217630937722107545 66433520413223203291580659)
  ·
    refine ⟨99650280619834804937370989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66433520413223203291580659 99650280619834804937370989)
    ·
      refine ⟨37368855232438051851514121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99650280619834804937370989 37368855232438051851514121)
      ·
        refine ⟨28026641424328538888635591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37368855232438051851514121 28026641424328538888635591)
        ·
          refine ⟨42039962136492808332953387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28026641424328538888635591 42039962136492808332953387)
          ·
            refine ⟨63059943204739212499430081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42039962136492808332953387 63059943204739212499430081)
            ·
              refine ⟨47294957403554409374572561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63059943204739212499430081 47294957403554409374572561)
              ·
                refine ⟨35471218052665807030929421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47294957403554409374572561 35471218052665807030929421)
                ·
                  refine ⟨13301706769749677636598533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35471218052665807030929421 13301706769749677636598533)
                  ·
                    refine ⟨2494070019328064556862225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13301706769749677636598533 2494070019328064556862225)
                    ·
                      refine ⟨1870552514496048417646669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494070019328064556862225 1870552514496048417646669)
                      ·
                        rfl

theorem cell23_3642888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_3642888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642888 prefixEnd_3642888 := by exact prefixLift 3642888
  have htrace : WordTrace (prefixWord ++ tailWord_3642888) baseStart_3642888 baseEnd_3642888 := by
    simpa [prefixWord, tailWord_3642888, baseEnd_3642888] using wordTrace_append hprefix tailTrace_3642888
  have hstable : (prefixWord ++ tailWord_3642888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642888).length < 2 ^ (prefixWord ++ tailWord_3642888).sum := by decide
  have hdescent : baseEnd_3642888 < baseStart_3642888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642911 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 7]
def baseStart_3642911 : Nat := 118140960795 + 3642911 * 2 ^ 59
def prefixEnd_3642911 : Nat := 4983230072969 + 3 ^ 40 * 3642911 * 2
def baseEnd_3642911 : Nat := 207840480505677980851007

theorem tailTrace_3642911 : CollatzResearch.WordTrace tailWord_3642911 prefixEnd_3642911 207840480505677980851007 := by
  unfold tailWord_3642911
  simp only [CollatzResearch.WordTrace]
  refine ⟨132867879705363081511248587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88578586470242054340832391 132867879705363081511248587)
  ·
    refine ⟨199301819558044622266872881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132867879705363081511248587 199301819558044622266872881)
    ·
      refine ⟨149476364668533466700154661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199301819558044622266872881 149476364668533466700154661)
      ·
        refine ⟨28026818375350025006278999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149476364668533466700154661 28026818375350025006278999)
        ·
          refine ⟨42040227563025037509418499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28026818375350025006278999 42040227563025037509418499)
          ·
            refine ⟨63060341344537556264127749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42040227563025037509418499 63060341344537556264127749)
            ·
              refine ⟨11823814002100791799523953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63060341344537556264127749 11823814002100791799523953)
              ·
                refine ⟨8867860501575593849642965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11823814002100791799523953 8867860501575593849642965)
                ·
                  refine ⟨207840480505677980851007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8867860501575593849642965 207840480505677980851007)
                  ·
                    rfl

theorem cell23_3642911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 7].length) (baseStart_3642911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642911 prefixEnd_3642911 := by exact prefixLift 3642911
  have htrace : WordTrace (prefixWord ++ tailWord_3642911) baseStart_3642911 baseEnd_3642911 := by
    simpa [prefixWord, tailWord_3642911, baseEnd_3642911] using wordTrace_append hprefix tailTrace_3642911
  have hstable : (prefixWord ++ tailWord_3642911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642911).length < 2 ^ (prefixWord ++ tailWord_3642911).sum := by decide
  have hdescent : baseEnd_3642911 < baseStart_3642911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3642991 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 6]
def baseStart_3642991 : Nat := 118140960795 + 3642991 * 2 ^ 59
def prefixEnd_3642991 : Nat := 4983230072969 + 3 ^ 40 * 3642991 * 2
def baseEnd_3642991 : Nat := 1870605403003461514658695

theorem tailTrace_3642991 : CollatzResearch.WordTrace tailWord_3642991 prefixEnd_3642991 1870605403003461514658695 := by
  unfold tailWord_3642991
  simp only [CollatzResearch.WordTrace]
  refine ⟨132870797545073255174160827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88580531696715503449440551 132870797545073255174160827)
  ·
    refine ⟨199306196317609882761241241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132870797545073255174160827 199306196317609882761241241)
    ·
      refine ⟨149479647238207412070930931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199306196317609882761241241 149479647238207412070930931)
      ·
        refine ⟨224219470857311118106396397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149479647238207412070930931 224219470857311118106396397)
        ·
          refine ⟨84082301571491669289898649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224219470857311118106396397 84082301571491669289898649)
          ·
            refine ⟨63061726178618751967423987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84082301571491669289898649 63061726178618751967423987)
            ·
              refine ⟨94592589267928127951135981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63061726178618751967423987 94592589267928127951135981)
              ·
                refine ⟨35472220975473047981675993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94592589267928127951135981 35472220975473047981675993)
                ·
                  refine ⟨26604165731604785986256995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35472220975473047981675993 26604165731604785986256995)
                  ·
                    refine ⟨39906248597407178979385493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26604165731604785986256995 39906248597407178979385493)
                    ·
                      refine ⟨1870605403003461514658695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39906248597407178979385493 1870605403003461514658695)
                      ·
                        rfl

theorem cell23_3642991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_3642991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3642991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3642991 prefixEnd_3642991 := by exact prefixLift 3642991
  have htrace : WordTrace (prefixWord ++ tailWord_3642991) baseStart_3642991 baseEnd_3642991 := by
    simpa [prefixWord, tailWord_3642991, baseEnd_3642991] using wordTrace_append hprefix tailTrace_3642991
  have hstable : (prefixWord ++ tailWord_3642991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3642991).length < 2 ^ (prefixWord ++ tailWord_3642991).sum := by decide
  have hdescent : baseEnd_3642991 < baseStart_3642991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3642991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
