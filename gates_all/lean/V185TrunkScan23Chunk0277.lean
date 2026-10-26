import V185TrunkScan23Chunk0276

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1638367 : List Nat := [1, 1, 2, 3, 4, 1, 11]
def baseStart_1638367 : Nat := 118140960795 + 1638367 * 2 ^ 59
def prefixEnd_1638367 : Nat := 4983230072969 + 3 ^ 40 * 1638367 * 2
def baseEnd_1638367 : Nat := 10386046413146871793553

theorem tailTrace_1638367 : CollatzResearch.WordTrace tailWord_1638367 prefixEnd_1638367 10386046413146871793553 := by
  unfold tailWord_1638367
  simp only [CollatzResearch.WordTrace]
  refine ⟨59756153655483644651833355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39837435770322429767888903 59756153655483644651833355)
  ·
    refine ⟨89634230483225466977750033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59756153655483644651833355 89634230483225466977750033)
    ·
      refine ⟨67225672862419100233312525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89634230483225466977750033 67225672862419100233312525)
      ·
        refine ⟨25209627323407162587492197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67225672862419100233312525 25209627323407162587492197)
        ·
          refine ⟨4726805123138842985154787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25209627323407162587492197 4726805123138842985154787)
          ·
            refine ⟨7090207684708264477732181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4726805123138842985154787 7090207684708264477732181)
            ·
              refine ⟨10386046413146871793553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7090207684708264477732181 10386046413146871793553)
              ·
                rfl

theorem cell23_1638367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 11].length) (baseStart_1638367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638367 prefixEnd_1638367 := by exact prefixLift 1638367
  have htrace : WordTrace (prefixWord ++ tailWord_1638367) baseStart_1638367 baseEnd_1638367 := by
    simpa [prefixWord, tailWord_1638367, baseEnd_1638367] using wordTrace_append hprefix tailTrace_1638367
  have hstable : (prefixWord ++ tailWord_1638367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638367).length < 2 ^ (prefixWord ++ tailWord_1638367).sum := by decide
  have hdescent : baseEnd_1638367 < baseStart_1638367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638398 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1638398 : Nat := 118140960795 + 1638398 * 2 ^ 59
def prefixEnd_1638398 : Nat := 4983230072969 + 3 ^ 40 * 1638398 * 2
def baseEnd_1638398 : Nat := 841285677365185993990151

theorem tailTrace_1638398 : CollatzResearch.WordTrace tailWord_1638398 prefixEnd_1638398 841285677365185993990151 := by
  unfold tailWord_1638398
  simp only [CollatzResearch.WordTrace]
  refine ⟨7469660539796417118276481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39838189545580891297474565 7469660539796417118276481)
  ·
    refine ⟨5602245404847312838707361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7469660539796417118276481 5602245404847312838707361)
    ·
      refine ⟨4201684053635484629030521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5602245404847312838707361 4201684053635484629030521)
      ·
        refine ⟨3151263040226613471772891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4201684053635484629030521 3151263040226613471772891)
        ·
          refine ⟨4726894560339920207659337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3151263040226613471772891 4726894560339920207659337)
          ·
            refine ⟨3545170920254940155744503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4726894560339920207659337 3545170920254940155744503)
            ·
              refine ⟨5317756380382410233616755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3545170920254940155744503 5317756380382410233616755)
              ·
                refine ⟨7976634570573615350425133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5317756380382410233616755 7976634570573615350425133)
                ·
                  refine ⟨2991237963965105756409425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7976634570573615350425133 2991237963965105756409425)
                  ·
                    refine ⟨2243428472973829317307069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2991237963965105756409425 2243428472973829317307069)
                    ·
                      refine ⟨841285677365185993990151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2243428472973829317307069 841285677365185993990151)
                      ·
                        rfl

theorem cell23_1638398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1638398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638398 prefixEnd_1638398 := by exact prefixLift 1638398
  have htrace : WordTrace (prefixWord ++ tailWord_1638398) baseStart_1638398 baseEnd_1638398 := by
    simpa [prefixWord, tailWord_1638398, baseEnd_1638398] using wordTrace_append hprefix tailTrace_1638398
  have hstable : (prefixWord ++ tailWord_1638398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638398).length < 2 ^ (prefixWord ++ tailWord_1638398).sum := by decide
  have hdescent : baseEnd_1638398 < baseStart_1638398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638428 : List Nat := [2, 2, 3, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_1638428 : Nat := 118140960795 + 1638428 * 2 ^ 59
def prefixEnd_1638428 : Nat := 4983230072969 + 3 ^ 40 * 1638428 * 2
def baseEnd_1638428 : Nat := 841301081784820876615013

theorem tailTrace_1638428 : CollatzResearch.WordTrace tailWord_1638428 prefixEnd_1638428 841301081784820876615013 := by
  unfold tailWord_1638428
  simp only [CollatzResearch.WordTrace]
  refine ⟨29879189254131326034901969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39838919005508434713202625 29879189254131326034901969)
  ·
    refine ⟨22409391940598494526176477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29879189254131326034901969 22409391940598494526176477)
    ·
      refine ⟨8403521977724435447316179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22409391940598494526176477 8403521977724435447316179)
      ·
        refine ⟨12605282966586653170974269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8403521977724435447316179 12605282966586653170974269)
        ·
          refine ⟨4726981112469994939115351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12605282966586653170974269 4726981112469994939115351)
          ·
            refine ⟨7090471668704992408673027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4726981112469994939115351 7090471668704992408673027)
            ·
              refine ⟨10635707503057488613009541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7090471668704992408673027 10635707503057488613009541)
              ·
                refine ⟨1994195156823279114939289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10635707503057488613009541 1994195156823279114939289)
                ·
                  refine ⟨1495646367617459336204467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1994195156823279114939289 1495646367617459336204467)
                  ·
                    refine ⟨2243469551426189004306701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1495646367617459336204467 2243469551426189004306701)
                    ·
                      refine ⟨841301081784820876615013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2243469551426189004306701 841301081784820876615013)
                      ·
                        rfl

theorem cell23_1638428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_1638428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638428 prefixEnd_1638428 := by exact prefixLift 1638428
  have htrace : WordTrace (prefixWord ++ tailWord_1638428) baseStart_1638428 baseEnd_1638428 := by
    simpa [prefixWord, tailWord_1638428, baseEnd_1638428] using wordTrace_append hprefix tailTrace_1638428
  have hstable : (prefixWord ++ tailWord_1638428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638428).length < 2 ^ (prefixWord ++ tailWord_1638428).sum := by decide
  have hdescent : baseEnd_1638428 < baseStart_1638428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638429 : List Nat := [1, 4, 2, 2, 2, 3, 2, 2, 1, 2, 2]
def baseStart_1638429 : Nat := 118140960795 + 1638429 * 2 ^ 59
def prefixEnd_1638429 : Nat := 4983230072969 + 3 ^ 40 * 1638429 * 2
def baseEnd_1638429 : Nat := 841301595265475372702509

theorem tailTrace_1638429 : CollatzResearch.WordTrace tailWord_1638429 prefixEnd_1638429 841301595265475372702509 := by
  unfold tailWord_1638429
  simp only [CollatzResearch.WordTrace]
  refine ⟨59758414981259029240590341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39838943320839352827060227 59758414981259029240590341)
  ·
    refine ⟨11204702808986067982610689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59758414981259029240590341 11204702808986067982610689)
    ·
      refine ⟨8403527106739550986958017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11204702808986067982610689 8403527106739550986958017)
      ·
        refine ⟨6302645330054663240218513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8403527106739550986958017 6302645330054663240218513)
        ·
          refine ⟨4726983997540997430163885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6302645330054663240218513 4726983997540997430163885)
          ·
            refine ⟨1772618999077874036311457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4726983997540997430163885 1772618999077874036311457)
            ·
              refine ⟨1329464249308405527233593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1772618999077874036311457 1329464249308405527233593)
              ·
                refine ⟨997098186981304145425195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1329464249308405527233593 997098186981304145425195)
                ·
                  refine ⟨1495647280471956218137793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997098186981304145425195 1495647280471956218137793)
                  ·
                    refine ⟨1121735460353967163603345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1495647280471956218137793 1121735460353967163603345)
                    ·
                      refine ⟨841301595265475372702509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121735460353967163603345 841301595265475372702509)
                      ·
                        rfl

theorem cell23_1638429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_1638429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638429 prefixEnd_1638429 := by exact prefixLift 1638429
  have htrace : WordTrace (prefixWord ++ tailWord_1638429) baseStart_1638429 baseEnd_1638429 := by
    simpa [prefixWord, tailWord_1638429, baseEnd_1638429] using wordTrace_append hprefix tailTrace_1638429
  have hstable : (prefixWord ++ tailWord_1638429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638429).length < 2 ^ (prefixWord ++ tailWord_1638429).sum := by decide
  have hdescent : baseEnd_1638429 < baseStart_1638429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638434 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_1638434 : Nat := 118140960795 + 1638434 * 2 ^ 59
def prefixEnd_1638434 : Nat := 4983230072969 + 3 ^ 40 * 1638434 * 2
def baseEnd_1638434 : Nat := 841304162668747853139985

theorem tailTrace_1638434 : CollatzResearch.WordTrace tailWord_1638434 prefixEnd_1638434 841304162668747853139985 := by
  unfold tailWord_1638434
  simp only [CollatzResearch.WordTrace]
  refine ⟨14939649336560228773630589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39839064897493943396348237 14939649336560228773630589)
  ·
    refine ⟨5602368501210085790111471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14939649336560228773630589 5602368501210085790111471)
    ·
      refine ⟨8403552751815128685167207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5602368501210085790111471 8403552751815128685167207)
      ·
        refine ⟨12605329127722693027750811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8403552751815128685167207 12605329127722693027750811)
        ·
          refine ⟨18907993691584039541626217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12605329127722693027750811 18907993691584039541626217)
          ·
            refine ⟨14180995268688029656219663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18907993691584039541626217 14180995268688029656219663)
            ·
              refine ⟨21271492903032044484329495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14180995268688029656219663 21271492903032044484329495)
              ·
                refine ⟨31907239354548066726494243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21271492903032044484329495 31907239354548066726494243)
                ·
                  refine ⟨47860859031822100089741365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31907239354548066726494243 47860859031822100089741365)
                  ·
                    refine ⟨4486955534233321883413253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47860859031822100089741365 4486955534233321883413253)
                    ·
                      refine ⟨841304162668747853139985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4486955534233321883413253 841304162668747853139985)
                      ·
                        rfl

theorem cell23_1638434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_1638434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638434 prefixEnd_1638434 := by exact prefixLift 1638434
  have htrace : WordTrace (prefixWord ++ tailWord_1638434) baseStart_1638434 baseEnd_1638434 := by
    simpa [prefixWord, tailWord_1638434, baseEnd_1638434] using wordTrace_append hprefix tailTrace_1638434
  have hstable : (prefixWord ++ tailWord_1638434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638434).length < 2 ^ (prefixWord ++ tailWord_1638434).sum := by decide
  have hdescent : baseEnd_1638434 < baseStart_1638434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638451 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 1, 4, 2]
def baseStart_1638451 : Nat := 118140960795 + 1638451 * 2 ^ 59
def prefixEnd_1638451 : Nat := 4983230072969 + 3 ^ 40 * 1638451 * 2
def baseEnd_1638451 : Nat := 841312891839874286627407

theorem tailTrace_1638451 : CollatzResearch.WordTrace tailWord_1638451 prefixEnd_1638451 841312891839874286627407 := by
  unfold tailWord_1638451
  simp only [CollatzResearch.WordTrace]
  refine ⟨59759217387179326997891207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39839478258119551331927471 59759217387179326997891207)
  ·
    refine ⟨89638826080768990496836811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59759217387179326997891207 89638826080768990496836811)
    ·
      refine ⟨134458239121153485745255217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89638826080768990496836811 134458239121153485745255217)
      ·
        refine ⟨100843679340865114308941413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134458239121153485745255217 100843679340865114308941413)
        ·
          refine ⟨18908189876412208932926515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100843679340865114308941413 18908189876412208932926515)
          ·
            refine ⟨28362284814618313399389773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18908189876412208932926515 28362284814618313399389773)
            ·
              refine ⟨10635856805481867524771165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28362284814618313399389773 10635856805481867524771165)
              ·
                refine ⟨3988446302055700321789187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10635856805481867524771165 3988446302055700321789187)
                ·
                  refine ⟨5982669453083550482683781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988446302055700321789187 5982669453083550482683781)
                  ·
                    refine ⟨1121750522453165715503209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5982669453083550482683781 1121750522453165715503209)
                    ·
                      refine ⟨841312891839874286627407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121750522453165715503209 841312891839874286627407)
                      ·
                        rfl

theorem cell23_1638451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 4, 2].length) (baseStart_1638451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638451 prefixEnd_1638451 := by exact prefixLift 1638451
  have htrace : WordTrace (prefixWord ++ tailWord_1638451) baseStart_1638451 baseEnd_1638451 := by
    simpa [prefixWord, tailWord_1638451, baseEnd_1638451] using wordTrace_append hprefix tailTrace_1638451
  have hstable : (prefixWord ++ tailWord_1638451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638451).length < 2 ^ (prefixWord ++ tailWord_1638451).sum := by decide
  have hdescent : baseEnd_1638451 < baseStart_1638451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638485 : List Nat := [1, 3, 2, 2, 1, 3, 3, 2, 2, 2, 2]
def baseStart_1638485 : Nat := 118140960795 + 1638485 * 2 ^ 59
def prefixEnd_1638485 : Nat := 4983230072969 + 3 ^ 40 * 1638485 * 2
def baseEnd_1638485 : Nat := 841330350182127153602251

theorem tailTrace_1638485 : CollatzResearch.WordTrace tailWord_1638485 prefixEnd_1638485 841330350182127153602251 := by
  unfold tailWord_1638485
  simp only [CollatzResearch.WordTrace]
  refine ⟨59760457469056150804628909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39840304979370767203085939 59760457469056150804628909)
  ·
    refine ⟨22410171550896056551735841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59760457469056150804628909 22410171550896056551735841)
    ·
      refine ⟨16807628663172042413801881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22410171550896056551735841 16807628663172042413801881)
      ·
        refine ⟨12605721497379031810351411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16807628663172042413801881 12605721497379031810351411)
        ·
          refine ⟨18908582246068547715527117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12605721497379031810351411 18908582246068547715527117)
          ·
            refine ⟨7090718342275705393322669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18908582246068547715527117 7090718342275705393322669)
            ·
              refine ⟨2659019378353389522496001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7090718342275705393322669 2659019378353389522496001)
              ·
                refine ⟨1994264533765042141872001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2659019378353389522496001 1994264533765042141872001)
                ·
                  refine ⟨1495698400323781606404001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1994264533765042141872001 1495698400323781606404001)
                  ·
                    refine ⟨1121773800242836204803001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1495698400323781606404001 1121773800242836204803001)
                    ·
                      refine ⟨841330350182127153602251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121773800242836204803001 841330350182127153602251)
                      ·
                        rfl

theorem cell23_1638485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_1638485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638485 prefixEnd_1638485 := by exact prefixLift 1638485
  have htrace : WordTrace (prefixWord ++ tailWord_1638485) baseStart_1638485 baseEnd_1638485 := by
    simpa [prefixWord, tailWord_1638485, baseEnd_1638485] using wordTrace_append hprefix tailTrace_1638485
  have hstable : (prefixWord ++ tailWord_1638485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638485).length < 2 ^ (prefixWord ++ tailWord_1638485).sum := by decide
  have hdescent : baseEnd_1638485 < baseStart_1638485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638501 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 2, 3, 3]
def baseStart_1638501 : Nat := 118140960795 + 1638501 * 2 ^ 59
def prefixEnd_1638501 : Nat := 4983230072969 + 3 ^ 40 * 1638501 * 2
def baseEnd_1638501 : Nat := 841338565872599091002177

theorem tailTrace_1638501 : CollatzResearch.WordTrace tailWord_1638501 prefixEnd_1638501 841338565872599091002177 := by
  unfold tailWord_1638501
  simp only [CollatzResearch.WordTrace]
  refine ⟨59761041036998185537211357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39840694024665457024807571 59761041036998185537211357)
  ·
    refine ⟨22410390388874319576454259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59761041036998185537211357 22410390388874319576454259)
    ·
      refine ⟨33615585583311479364681389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22410390388874319576454259 33615585583311479364681389)
      ·
        refine ⟨12605844593741804761755521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33615585583311479364681389 12605844593741804761755521)
        ·
          refine ⟨9454383445306353571316641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12605844593741804761755521 9454383445306353571316641)
          ·
            refine ⟨7090787583979765178487481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9454383445306353571316641 7090787583979765178487481)
            ·
              refine ⟨5318090687984823883865611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7090787583979765178487481 5318090687984823883865611)
              ·
                refine ⟨7977136031977235825798417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5318090687984823883865611 7977136031977235825798417)
                ·
                  refine ⟨5982852023982926869348813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7977136031977235825798417 5982852023982926869348813)
                  ·
                    refine ⟨2243569508993597576005805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5982852023982926869348813 2243569508993597576005805)
                    ·
                      refine ⟨841338565872599091002177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2243569508993597576005805 841338565872599091002177)
                      ·
                        rfl

theorem cell23_1638501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_1638501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638501 prefixEnd_1638501 := by exact prefixLift 1638501
  have htrace : WordTrace (prefixWord ++ tailWord_1638501) baseStart_1638501 baseEnd_1638501 := by
    simpa [prefixWord, tailWord_1638501, baseEnd_1638501] using wordTrace_append hprefix tailTrace_1638501
  have hstable : (prefixWord ++ tailWord_1638501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638501).length < 2 ^ (prefixWord ++ tailWord_1638501).sum := by decide
  have hdescent : baseEnd_1638501 < baseStart_1638501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638578 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_1638578 : Nat := 118140960795 + 1638578 * 2 ^ 59
def prefixEnd_1638578 : Nat := 4983230072969 + 3 ^ 40 * 1638578 * 2
def baseEnd_1638578 : Nat := 841378103882995289739323

theorem tailTrace_1638578 : CollatzResearch.WordTrace tailWord_1638578 prefixEnd_1638578 841378103882995289739323 := by
  unfold tailWord_1638578
  simp only [CollatzResearch.WordTrace]
  refine ⟨14940962364429806921941097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39842566305146151791842925 14940962364429806921941097)
  ·
    refine ⟨11205721773322355191455823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14940962364429806921941097 11205721773322355191455823)
    ·
      refine ⟨16808582659983532787183735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11205721773322355191455823 16808582659983532787183735)
      ·
        refine ⟨25212873989975299180775603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16808582659983532787183735 25212873989975299180775603)
        ·
          refine ⟨37819310984962948771163405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25212873989975299180775603 37819310984962948771163405)
          ·
            refine ⟨14182241619361105789186277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37819310984962948771163405 14182241619361105789186277)
            ·
              refine ⟨2659170303630207335472427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14182241619361105789186277 2659170303630207335472427)
              ·
                refine ⟨3988755455445311003208641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659170303630207335472427 3988755455445311003208641)
                ·
                  refine ⟨2991566591583983252406481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3988755455445311003208641 2991566591583983252406481)
                  ·
                    refine ⟨2243674943687987439304861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2991566591583983252406481 2243674943687987439304861)
                    ·
                      refine ⟨841378103882995289739323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2243674943687987439304861 841378103882995289739323)
                      ·
                        rfl

theorem cell23_1638578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_1638578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638578 prefixEnd_1638578 := by exact prefixLift 1638578
  have htrace : WordTrace (prefixWord ++ tailWord_1638578) baseStart_1638578 baseEnd_1638578 := by
    simpa [prefixWord, tailWord_1638578, baseEnd_1638578] using wordTrace_append hprefix tailTrace_1638578
  have hstable : (prefixWord ++ tailWord_1638578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638578).length < 2 ^ (prefixWord ++ tailWord_1638578).sum := by decide
  have hdescent : baseEnd_1638578 < baseStart_1638578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638618 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2]
def baseStart_1638618 : Nat := 118140960795 + 1638618 * 2 ^ 59
def prefixEnd_1638618 : Nat := 4983230072969 + 3 ^ 40 * 1638618 * 2
def baseEnd_1638618 : Nat := 841398643109175133239139

theorem tailTrace_1638618 : CollatzResearch.WordTrace tailWord_1638618 prefixEnd_1638618 841398643109175133239139 := by
  unfold tailWord_1638618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14941327094393578629805127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39843538918382876346147005 14941327094393578629805127)
  ·
    refine ⟨22411990641590367944707691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14941327094393578629805127 22411990641590367944707691)
    ·
      refine ⟨33617985962385551917061537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22411990641590367944707691 33617985962385551917061537)
      ·
        refine ⟨25213489471789163937796153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33617985962385551917061537 25213489471789163937796153)
        ·
          refine ⟨18910117103841872953347115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25213489471789163937796153 18910117103841872953347115)
          ·
            refine ⟨28365175655762809430020673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18910117103841872953347115 28365175655762809430020673)
            ·
              refine ⟨21273881741822107072515505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28365175655762809430020673 21273881741822107072515505)
              ·
                refine ⟨15955411306366580304386629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21273881741822107072515505 15955411306366580304386629)
                ·
                  refine ⟨2991639619943733807072493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15955411306366580304386629 2991639619943733807072493)
                  ·
                    refine ⟨1121864857478900177652185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2991639619943733807072493 1121864857478900177652185)
                    ·
                      refine ⟨841398643109175133239139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121864857478900177652185 841398643109175133239139)
                      ·
                        rfl

theorem cell23_1638618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_1638618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638618 prefixEnd_1638618 := by exact prefixLift 1638618
  have htrace : WordTrace (prefixWord ++ tailWord_1638618) baseStart_1638618 baseEnd_1638618 := by
    simpa [prefixWord, tailWord_1638618, baseEnd_1638618] using wordTrace_append hprefix tailTrace_1638618
  have hstable : (prefixWord ++ tailWord_1638618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638618).length < 2 ^ (prefixWord ++ tailWord_1638618).sum := by decide
  have hdescent : baseEnd_1638618 < baseStart_1638618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638626 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_1638626 : Nat := 118140960795 + 1638626 * 2 ^ 59
def prefixEnd_1638626 : Nat := 4983230072969 + 3 ^ 40 * 1638626 * 2
def baseEnd_1638626 : Nat := 841402750954411101939103

theorem tailTrace_1638626 : CollatzResearch.WordTrace tailWord_1638626 prefixEnd_1638626 841402750954411101939103 := by
  unfold tailWord_1638626
  simp only [CollatzResearch.WordTrace]
  refine ⟨14941400040386332971377933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39843733441030221257007821 14941400040386332971377933)
  ·
    refine ⟨5603025015144874864266725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14941400040386332971377933 5603025015144874864266725)
    ·
      refine ⟨1050567190339664037050011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5603025015144874864266725 1050567190339664037050011)
      ·
        refine ⟨1575850785509496055575017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050567190339664037050011 1575850785509496055575017)
        ·
          refine ⟨1181888089132122041681263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1575850785509496055575017 1181888089132122041681263)
          ·
            refine ⟨1772832133698183062521895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1181888089132122041681263 1772832133698183062521895)
            ·
              refine ⟨2659248200547274593782843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772832133698183062521895 2659248200547274593782843)
              ·
                refine ⟨3988872300820911890674265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659248200547274593782843 3988872300820911890674265)
                ·
                  refine ⟨2991654225615683918005699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3988872300820911890674265 2991654225615683918005699)
                  ·
                    refine ⟨4487481338423525877008549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2991654225615683918005699 4487481338423525877008549)
                    ·
                      refine ⟨841402750954411101939103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4487481338423525877008549 841402750954411101939103)
                      ·
                        rfl

theorem cell23_1638626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_1638626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638626 prefixEnd_1638626 := by exact prefixLift 1638626
  have htrace : WordTrace (prefixWord ++ tailWord_1638626) baseStart_1638626 baseEnd_1638626 := by
    simpa [prefixWord, tailWord_1638626, baseEnd_1638626] using wordTrace_append hprefix tailTrace_1638626
  have hstable : (prefixWord ++ tailWord_1638626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638626).length < 2 ^ (prefixWord ++ tailWord_1638626).sum := by decide
  have hdescent : baseEnd_1638626 < baseStart_1638626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638641 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 1, 6]
def baseStart_1638641 : Nat := 118140960795 + 1638641 * 2 ^ 59
def prefixEnd_1638641 : Nat := 4983230072969 + 3 ^ 40 * 1638641 * 2
def baseEnd_1638641 : Nat := 280470151054742847750511

theorem tailTrace_1638641 : CollatzResearch.WordTrace tailWord_1638641 prefixEnd_1638641 280470151054742847750511 := by
  unfold tailWord_1638641
  simp only [CollatzResearch.WordTrace]
  refine ⟨59766147256490989447307777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39844098170993992964871851 59766147256490989447307777)
  ·
    refine ⟨44824610442368242085480833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59766147256490989447307777 44824610442368242085480833)
    ·
      refine ⟨33618457831776181564110625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44824610442368242085480833 33618457831776181564110625)
      ·
        refine ⟨25213843373832136173082969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33618457831776181564110625 25213843373832136173082969)
        ·
          refine ⟨18910382530374102129812227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25213843373832136173082969 18910382530374102129812227)
          ·
            refine ⟨28365573795561153194718341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18910382530374102129812227 28365573795561153194718341)
            ·
              refine ⟨5318545086667716224009689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28365573795561153194718341 5318545086667716224009689)
              ·
                refine ⟨3988908815000787168007267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5318545086667716224009689 3988908815000787168007267)
                ·
                  refine ⟨5983363222501180752010901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988908815000787168007267 5983363222501180752010901)
                  ·
                    refine ⟨280470151054742847750511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5983363222501180752010901 280470151054742847750511)
                    ·
                      rfl

theorem cell23_1638641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_1638641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638641 prefixEnd_1638641 := by exact prefixLift 1638641
  have htrace : WordTrace (prefixWord ++ tailWord_1638641) baseStart_1638641 baseEnd_1638641 := by
    simpa [prefixWord, tailWord_1638641, baseEnd_1638641] using wordTrace_append hprefix tailTrace_1638641
  have hstable : (prefixWord ++ tailWord_1638641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638641).length < 2 ^ (prefixWord ++ tailWord_1638641).sum := by decide
  have hdescent : baseEnd_1638641 < baseStart_1638641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638642 : List Nat := [3, 2, 1, 3, 2, 1, 1, 5, 1, 1, 3]
def baseStart_1638642 : Nat := 118140960795 + 1638642 * 2 ^ 59
def prefixEnd_1638642 : Nat := 4983230072969 + 3 ^ 40 * 1638642 * 2
def baseEnd_1638642 : Nat := 841410966644883039339029

theorem tailTrace_1638642 : CollatzResearch.WordTrace tailWord_1638642 prefixEnd_1638642 841410966644883039339029 := by
  unfold tailWord_1638642
  simp only [CollatzResearch.WordTrace]
  refine ⟨14941545932371841654523545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39844122486324911078729453 14941545932371841654523545)
  ·
    refine ⟨11206159449278881240892659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14941545932371841654523545 11206159449278881240892659)
    ·
      refine ⟨16809239173918321861338989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11206159449278881240892659 16809239173918321861338989)
      ·
        refine ⟨6303464690219370698002121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16809239173918321861338989 6303464690219370698002121)
        ·
          refine ⟨4727598517664528023501591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6303464690219370698002121 4727598517664528023501591)
          ·
            refine ⟨7091397776496792035252387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4727598517664528023501591 7091397776496792035252387)
            ·
              refine ⟨10637096664745188052878581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7091397776496792035252387 10637096664745188052878581)
              ·
                refine ⟨997227812319861379957367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10637096664745188052878581 997227812319861379957367)
                ·
                  refine ⟨1495841718479792069936051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997227812319861379957367 1495841718479792069936051)
                  ·
                    refine ⟨2243762577719688104904077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1495841718479792069936051 2243762577719688104904077)
                    ·
                      refine ⟨841410966644883039339029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2243762577719688104904077 841410966644883039339029)
                      ·
                        rfl

theorem cell23_1638642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_1638642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638642 prefixEnd_1638642 := by exact prefixLift 1638642
  have htrace : WordTrace (prefixWord ++ tailWord_1638642) baseStart_1638642 baseEnd_1638642 := by
    simpa [prefixWord, tailWord_1638642, baseEnd_1638642] using wordTrace_append hprefix tailTrace_1638642
  have hstable : (prefixWord ++ tailWord_1638642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638642).length < 2 ^ (prefixWord ++ tailWord_1638642).sum := by decide
  have hdescent : baseEnd_1638642 < baseStart_1638642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638665 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 3, 2, 2]
def baseStart_1638665 : Nat := 118140960795 + 1638665 * 2 ^ 59
def prefixEnd_1638665 : Nat := 4983230072969 + 3 ^ 40 * 1638665 * 2
def baseEnd_1638665 : Nat := 841422776699936449351423

theorem tailTrace_1638665 : CollatzResearch.WordTrace tailWord_1638665 prefixEnd_1638665 841422776699936449351423 := by
  unfold tailWord_1638665
  simp only [CollatzResearch.WordTrace]
  refine ⟨59767022608404041546181449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39844681738936027697454299 59767022608404041546181449)
  ·
    refine ⟨44825266956303031159636087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59767022608404041546181449 44825266956303031159636087)
    ·
      refine ⟨67237900434454546739454131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44825266956303031159636087 67237900434454546739454131)
      ·
        refine ⟨100856850651681820109181197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67237900434454546739454131 100856850651681820109181197)
        ·
          refine ⟨37821318994380682540942949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100856850651681820109181197 37821318994380682540942949)
          ·
            refine ⟨7091497311446377976426803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37821318994380682540942949 7091497311446377976426803)
            ·
              refine ⟨10637245967169566964640205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7091497311446377976426803 10637245967169566964640205)
              ·
                refine ⟨3988967237688587611740077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10637245967169566964640205 3988967237688587611740077)
                ·
                  refine ⟨1495862714133220354402529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3988967237688587611740077 1495862714133220354402529)
                  ·
                    refine ⟨1121897035599915265801897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1495862714133220354402529 1121897035599915265801897)
                    ·
                      refine ⟨841422776699936449351423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121897035599915265801897 841422776699936449351423)
                      ·
                        rfl

theorem cell23_1638665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 2, 2].length) (baseStart_1638665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638665 prefixEnd_1638665 := by exact prefixLift 1638665
  have htrace : WordTrace (prefixWord ++ tailWord_1638665) baseStart_1638665 baseEnd_1638665 := by
    simpa [prefixWord, tailWord_1638665, baseEnd_1638665] using wordTrace_append hprefix tailTrace_1638665
  have hstable : (prefixWord ++ tailWord_1638665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638665).length < 2 ^ (prefixWord ++ tailWord_1638665).sum := by decide
  have hdescent : baseEnd_1638665 < baseStart_1638665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638688 : List Nat := [2, 1, 1, 5, 2, 1, 4, 7]
def baseStart_1638688 : Nat := 118140960795 + 1638688 * 2 ^ 59
def prefixEnd_1638688 : Nat := 4983230072969 + 3 ^ 40 * 1638688 * 2
def baseEnd_1638688 : Nat := 31164243953888513309771

theorem tailTrace_1638688 : CollatzResearch.WordTrace tailWord_1638688 prefixEnd_1638688 31164243953888513309771 := by
  unfold tailWord_1638688
  simp only [CollatzResearch.WordTrace]
  refine ⟨29883930743660358237134359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39845240991547144316179145 29883930743660358237134359)
  ·
    refine ⟨44825896115490537355701539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29883930743660358237134359 44825896115490537355701539)
    ·
      refine ⟨67238844173235806033552309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44825896115490537355701539 67238844173235806033552309)
      ·
        refine ⟨6303641641240856815645529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67238844173235806033552309 6303641641240856815645529)
        ·
          refine ⟨4727731230930642611734147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6303641641240856815645529 4727731230930642611734147)
          ·
            refine ⟨7091596846395963917601221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4727731230930642611734147 7091596846395963917601221)
            ·
              refine ⟨1329674408699243234550229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7091596846395963917601221 1329674408699243234550229)
              ·
                refine ⟨31164243953888513309771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1329674408699243234550229 31164243953888513309771)
                ·
                  rfl

theorem cell23_1638688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 7].length) (baseStart_1638688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638688 prefixEnd_1638688 := by exact prefixLift 1638688
  have htrace : WordTrace (prefixWord ++ tailWord_1638688) baseStart_1638688 baseEnd_1638688 := by
    simpa [prefixWord, tailWord_1638688, baseEnd_1638688] using wordTrace_append hprefix tailTrace_1638688
  have hstable : (prefixWord ++ tailWord_1638688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638688).length < 2 ^ (prefixWord ++ tailWord_1638688).sum := by decide
  have hdescent : baseEnd_1638688 < baseStart_1638688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638702 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1638702 : Nat := 118140960795 + 1638702 * 2 ^ 59
def prefixEnd_1638702 : Nat := 4983230072969 + 3 ^ 40 * 1638702 * 2
def baseEnd_1638702 : Nat := 841441775484152804588753

theorem tailTrace_1638702 : CollatzResearch.WordTrace tailWord_1638702 prefixEnd_1638702 841441775484152804588753 := by
  unfold tailWord_1638702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7471046513658749608159795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39845581406179997910185573 7471046513658749608159795)
  ·
    refine ⟨11206569770488124412239693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7471046513658749608159795 11206569770488124412239693)
    ·
      refine ⟨4202463663933046654589885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11206569770488124412239693 4202463663933046654589885)
      ·
        refine ⟨1575923873974892495471207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4202463663933046654589885 1575923873974892495471207)
        ·
          refine ⟨2363885810962338743206811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1575923873974892495471207 2363885810962338743206811)
          ·
            refine ⟨3545828716443508114810217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2363885810962338743206811 3545828716443508114810217)
            ·
              refine ⟨2659371537332631086107663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3545828716443508114810217 2659371537332631086107663)
              ·
                refine ⟨3989057305998946629161495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659371537332631086107663 3989057305998946629161495)
                ·
                  refine ⟨5983585958998419943742243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3989057305998946629161495 5983585958998419943742243)
                  ·
                    refine ⟨8975378938497629915613365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5983585958998419943742243 8975378938497629915613365)
                    ·
                      refine ⟨841441775484152804588753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8975378938497629915613365 841441775484152804588753)
                      ·
                        rfl

theorem cell23_1638702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1638702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638702 prefixEnd_1638702 := by exact prefixLift 1638702
  have htrace : WordTrace (prefixWord ++ tailWord_1638702) baseStart_1638702 baseEnd_1638702 := by
    simpa [prefixWord, tailWord_1638702, baseEnd_1638702] using wordTrace_append hprefix tailTrace_1638702
  have hstable : (prefixWord ++ tailWord_1638702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638702).length < 2 ^ (prefixWord ++ tailWord_1638702).sum := by decide
  have hdescent : baseEnd_1638702 < baseStart_1638702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638755 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 1, 4, 2]
def baseStart_1638755 : Nat := 118140960795 + 1638755 * 2 ^ 59
def prefixEnd_1638755 : Nat := 4983230072969 + 3 ^ 40 * 1638755 * 2
def baseEnd_1638755 : Nat := 841468989958841097226009

theorem tailTrace_1638755 : CollatzResearch.WordTrace tailWord_1638755 prefixEnd_1638755 841468989958841097226009 := by
  unfold tailWord_1638755
  simp only [CollatzResearch.WordTrace]
  refine ⟨59770305178077986916957719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39846870118718657944638479 59770305178077986916957719)
  ·
    refine ⟨89655457767116980375436579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59770305178077986916957719 89655457767116980375436579)
    ·
      refine ⟨134483186650675470563154869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89655457767116980375436579 134483186650675470563154869)
      ·
        refine ⟨12607798748500825365295769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134483186650675470563154869 12607798748500825365295769)
        ·
          refine ⟨9455849061375619023971827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12607798748500825365295769 9455849061375619023971827)
          ·
            refine ⟨14183773592063428535957741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9455849061375619023971827 14183773592063428535957741)
            ·
              refine ⟨5318915097023785700984153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14183773592063428535957741 5318915097023785700984153)
              ·
                refine ⟨3989186322767839275738115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5318915097023785700984153 3989186322767839275738115)
                ·
                  refine ⟨5983779484151758913607173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3989186322767839275738115 5983779484151758913607173)
                  ·
                    refine ⟨1121958653278454796301345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5983779484151758913607173 1121958653278454796301345)
                    ·
                      refine ⟨841468989958841097226009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121958653278454796301345 841468989958841097226009)
                      ·
                        rfl

theorem cell23_1638755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_1638755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638755 prefixEnd_1638755 := by exact prefixLift 1638755
  have htrace : WordTrace (prefixWord ++ tailWord_1638755) baseStart_1638755 baseEnd_1638755 := by
    simpa [prefixWord, tailWord_1638755, baseEnd_1638755] using wordTrace_append hprefix tailTrace_1638755
  have hstable : (prefixWord ++ tailWord_1638755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638755).length < 2 ^ (prefixWord ++ tailWord_1638755).sum := by decide
  have hdescent : baseEnd_1638755 < baseStart_1638755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638759 : List Nat := [1, 1, 5, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_1638759 : Nat := 118140960795 + 1638759 * 2 ^ 59
def prefixEnd_1638759 : Nat := 4983230072969 + 3 ^ 40 * 1638759 * 2
def baseEnd_1638759 : Nat := 841471043881459081575991

theorem tailTrace_1638759 : CollatzResearch.WordTrace tailWord_1638759 prefixEnd_1638759 841471043881459081575991 := by
  unfold tailWord_1638759
  simp only [CollatzResearch.WordTrace]
  refine ⟨59770451070063495600103331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39846967380042330400068887 59770451070063495600103331)
  ·
    refine ⟨89655676605095243400154997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59770451070063495600103331 89655676605095243400154997)
    ·
      refine ⟨8405219681727679068764531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89655676605095243400154997 8405219681727679068764531)
      ·
        refine ⟨12607829522591518603146797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8405219681727679068764531 12607829522591518603146797)
        ·
          refine ⟨4727936070971819476180049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12607829522591518603146797 4727936070971819476180049)
          ·
            refine ⟨3545952053228864607135037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4727936070971819476180049 3545952053228864607135037)
            ·
              refine ⟨1329732019960824227675639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3545952053228864607135037 1329732019960824227675639)
              ·
                refine ⟨1994598029941236341513459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1329732019960824227675639 1994598029941236341513459)
                ·
                  refine ⟨2991897044911854512270189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994598029941236341513459 2991897044911854512270189)
                  ·
                    refine ⟨1121961391841945442101321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2991897044911854512270189 1121961391841945442101321)
                    ·
                      refine ⟨841471043881459081575991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1121961391841945442101321 841471043881459081575991)
                      ·
                        rfl

theorem cell23_1638759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_1638759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638759 prefixEnd_1638759 := by exact prefixLift 1638759
  have htrace : WordTrace (prefixWord ++ tailWord_1638759) baseStart_1638759 baseEnd_1638759 := by
    simpa [prefixWord, tailWord_1638759, baseEnd_1638759] using wordTrace_append hprefix tailTrace_1638759
  have hstable : (prefixWord ++ tailWord_1638759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638759).length < 2 ^ (prefixWord ++ tailWord_1638759).sum := by decide
  have hdescent : baseEnd_1638759 < baseStart_1638759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638785 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1638785 : Nat := 118140960795 + 1638785 * 2 ^ 59
def prefixEnd_1638785 : Nat := 4983230072969 + 3 ^ 40 * 1638785 * 2
def baseEnd_1638785 : Nat := 841484394378475979850871

theorem tailTrace_1638785 : CollatzResearch.WordTrace tailWord_1638785 prefixEnd_1638785 841484394378475979850871 := by
  unfold tailWord_1638785
  simp only [CollatzResearch.WordTrace]
  refine ⟨59771399367969302040549809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39847599578646201360366539 59771399367969302040549809)
  ·
    refine ⟨44828549525976976530412357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59771399367969302040549809 44828549525976976530412357)
    ·
      refine ⟨8405353036120683099452317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44828549525976976530412357 8405353036120683099452317)
      ·
        refine ⟨3152007388545256162294619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8405353036120683099452317 3152007388545256162294619)
        ·
          refine ⟨4728011082817884243441929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3152007388545256162294619 4728011082817884243441929)
          ·
            refine ⟨3546008312113413182581447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4728011082817884243441929 3546008312113413182581447)
            ·
              refine ⟨5319012468170119773872171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3546008312113413182581447 5319012468170119773872171)
              ·
                refine ⟨7978518702255179660808257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5319012468170119773872171 7978518702255179660808257)
                ·
                  refine ⟨5983889026691384745606193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7978518702255179660808257 5983889026691384745606193)
                  ·
                    refine ⟨4487916770018538559204645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5983889026691384745606193 4487916770018538559204645)
                    ·
                      refine ⟨841484394378475979850871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4487916770018538559204645 841484394378475979850871)
                      ·
                        rfl

theorem cell23_1638785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1638785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638785 prefixEnd_1638785 := by exact prefixLift 1638785
  have htrace : WordTrace (prefixWord ++ tailWord_1638785) baseStart_1638785 baseEnd_1638785 := by
    simpa [prefixWord, tailWord_1638785, baseEnd_1638785] using wordTrace_append hprefix tailTrace_1638785
  have hstable : (prefixWord ++ tailWord_1638785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638785).length < 2 ^ (prefixWord ++ tailWord_1638785).sum := by decide
  have hdescent : baseEnd_1638785 < baseStart_1638785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638828 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 4]
def baseStart_1638828 : Nat := 118140960795 + 1638828 * 2 ^ 59
def prefixEnd_1638828 : Nat := 4983230072969 + 3 ^ 40 * 1638828 * 2
def baseEnd_1638828 : Nat := 841506474046619311613173

theorem tailTrace_1638828 : CollatzResearch.WordTrace tailWord_1638828 prefixEnd_1638828 841506474046619311613173 := by
  unfold tailWord_1638828
  simp only [CollatzResearch.WordTrace]
  refine ⟨29886483853406760192182569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39848645137875680256243425 29886483853406760192182569)
  ·
    refine ⟨22414862890055070144136927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29886483853406760192182569 22414862890055070144136927)
    ·
      refine ⟨33622294335082605216205391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22414862890055070144136927 33622294335082605216205391)
      ·
        refine ⟨50433441502623907824308087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33622294335082605216205391 50433441502623907824308087)
        ·
          refine ⟨75650162253935861736462131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50433441502623907824308087 75650162253935861736462131)
          ·
            refine ⟨113475243380903792604693197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75650162253935861736462131 113475243380903792604693197)
            ·
              refine ⟨42553216267838922226759949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113475243380903792604693197 42553216267838922226759949)
              ·
                refine ⟨15957456100439595835034981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42553216267838922226759949 15957456100439595835034981)
                ·
                  refine ⟨2992023018832424219069059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15957456100439595835034981 2992023018832424219069059)
                  ·
                    refine ⟨4488034528248636328603589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2992023018832424219069059 4488034528248636328603589)
                    ·
                      refine ⟨841506474046619311613173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4488034528248636328603589 841506474046619311613173)
                      ·
                        rfl

theorem cell23_1638828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_1638828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638828 prefixEnd_1638828 := by exact prefixLift 1638828
  have htrace : WordTrace (prefixWord ++ tailWord_1638828) baseStart_1638828 baseEnd_1638828 := by
    simpa [prefixWord, tailWord_1638828, baseEnd_1638828] using wordTrace_append hprefix tailTrace_1638828
  have hstable : (prefixWord ++ tailWord_1638828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638828).length < 2 ^ (prefixWord ++ tailWord_1638828).sum := by decide
  have hdescent : baseEnd_1638828 < baseStart_1638828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638855 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 3, 4]
def baseStart_1638855 : Nat := 118140960795 + 1638855 * 2 ^ 59
def prefixEnd_1638855 : Nat := 4983230072969 + 3 ^ 40 * 1638855 * 2
def baseEnd_1638855 : Nat := 280506779341430235325183

theorem tailTrace_1638855 : CollatzResearch.WordTrace tailWord_1638855 prefixEnd_1638855 280506779341430235325183 := by
  unfold tailWord_1638855
  simp only [CollatzResearch.WordTrace]
  refine ⟨59773952477715703995598019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39849301651810469330398679 59773952477715703995598019)
  ·
    refine ⟨89660928716573555993397029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59773952477715703995598019 89660928716573555993397029)
    ·
      refine ⟨16811424134357541748761943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89660928716573555993397029 16811424134357541748761943)
      ·
        refine ⟨25217136201536312623142915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16811424134357541748761943 25217136201536312623142915)
        ·
          refine ⟨37825704302304468934714373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25217136201536312623142915 37825704302304468934714373)
          ·
            refine ⟨7092319556682087925258945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37825704302304468934714373 7092319556682087925258945)
            ·
              refine ⟨5319239667511565943944209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7092319556682087925258945 5319239667511565943944209)
              ·
                refine ⟨3989429750633674457958157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5319239667511565943944209 3989429750633674457958157)
                ·
                  refine ⟨1496036156487627921734309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3989429750633674457958157 1496036156487627921734309)
                  ·
                    refine ⟨280506779341430235325183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1496036156487627921734309 280506779341430235325183)
                    ·
                      rfl

theorem cell23_1638855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_1638855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638855 prefixEnd_1638855 := by exact prefixLift 1638855
  have htrace : WordTrace (prefixWord ++ tailWord_1638855) baseStart_1638855 baseEnd_1638855 := by
    simpa [prefixWord, tailWord_1638855, baseEnd_1638855] using wordTrace_append hprefix tailTrace_1638855
  have hstable : (prefixWord ++ tailWord_1638855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638855).length < 2 ^ (prefixWord ++ tailWord_1638855).sum := by decide
  have hdescent : baseEnd_1638855 < baseStart_1638855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638858 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_1638858 : Nat := 118140960795 + 1638858 * 2 ^ 59
def prefixEnd_1638858 : Nat := 4983230072969 + 3 ^ 40 * 1638858 * 2
def baseEnd_1638858 : Nat := 841521878466254194238035

theorem tailTrace_1638858 : CollatzResearch.WordTrace tailWord_1638858 prefixEnd_1638858 841521878466254194238035 := by
  unfold tailWord_1638858
  simp only [CollatzResearch.WordTrace]
  refine ⟨14943515474176208876989307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39849374597803223671971485 14943515474176208876989307)
  ·
    refine ⟨22415273211264313315483961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14943515474176208876989307 22415273211264313315483961)
    ·
      refine ⟨16811454908448234986612971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22415273211264313315483961 16811454908448234986612971)
      ·
        refine ⟨25217182362672352479919457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16811454908448234986612971 25217182362672352479919457)
        ·
          refine ⟨18912886772004264359939593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25217182362672352479919457 18912886772004264359939593)
          ·
            refine ⟨14184665079003198269954695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18912886772004264359939593 14184665079003198269954695)
            ·
              refine ⟨21276997618504797404932043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14184665079003198269954695 21276997618504797404932043)
              ·
                refine ⟨31915496427757196107398065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21276997618504797404932043 31915496427757196107398065)
                ·
                  refine ⟨23936622320817897080548549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31915496427757196107398065 23936622320817897080548549)
                  ·
                    refine ⟨4488116685153355702602853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23936622320817897080548549 4488116685153355702602853)
                    ·
                      refine ⟨841521878466254194238035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4488116685153355702602853 841521878466254194238035)
                      ·
                        rfl

theorem cell23_1638858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_1638858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638858 prefixEnd_1638858 := by exact prefixLift 1638858
  have htrace : WordTrace (prefixWord ++ tailWord_1638858) baseStart_1638858 baseEnd_1638858 := by
    simpa [prefixWord, tailWord_1638858, baseEnd_1638858] using wordTrace_append hprefix tailTrace_1638858
  have hstable : (prefixWord ++ tailWord_1638858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638858).length < 2 ^ (prefixWord ++ tailWord_1638858).sum := by decide
  have hdescent : baseEnd_1638858 < baseStart_1638858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638905 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 3, 5, 2]
def baseStart_1638905 : Nat := 118140960795 + 1638905 * 2 ^ 59
def prefixEnd_1638905 : Nat := 4983230072969 + 3 ^ 40 * 1638905 * 2
def baseEnd_1638905 : Nat := 841546012057015510350319

theorem tailTrace_1638905 : CollatzResearch.WordTrace tailWord_1638905 prefixEnd_1638905 841546012057015510350319 := by
  unfold tailWord_1638905
  simp only [CollatzResearch.WordTrace]
  refine ⟨59775776127534562534918169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39850517418356375023278779 59775776127534562534918169)
  ·
    refine ⟨44831832095650921901188627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59775776127534562534918169 44831832095650921901188627)
    ·
      refine ⟨67247748143476382851782941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44831832095650921901188627 67247748143476382851782941)
      ·
        refine ⟨25217905553803643569418603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67247748143476382851782941 25217905553803643569418603)
        ·
          refine ⟨37826858330705465354127905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25217905553803643569418603 37826858330705465354127905)
          ·
            refine ⟨28370143748029099015595929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37826858330705465354127905 28370143748029099015595929)
            ·
              refine ⟨21277607811021824261696947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28370143748029099015595929 21277607811021824261696947)
              ·
                refine ⟨31916411716532736392545421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21277607811021824261696947 31916411716532736392545421)
                ·
                  refine ⟨11968654393699776147204533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31916411716532736392545421 11968654393699776147204533)
                  ·
                    refine ⟨1122061349409354013800425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11968654393699776147204533 1122061349409354013800425)
                    ·
                      refine ⟨841546012057015510350319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1122061349409354013800425 841546012057015510350319)
                      ·
                        rfl

theorem cell23_1638905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_1638905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638905 prefixEnd_1638905 := by exact prefixLift 1638905
  have htrace : WordTrace (prefixWord ++ tailWord_1638905) baseStart_1638905 baseEnd_1638905 := by
    simpa [prefixWord, tailWord_1638905, baseEnd_1638905] using wordTrace_append hprefix tailTrace_1638905
  have hstable : (prefixWord ++ tailWord_1638905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638905).length < 2 ^ (prefixWord ++ tailWord_1638905).sum := by decide
  have hdescent : baseEnd_1638905 < baseStart_1638905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638952 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1638952 : Nat := 118140960795 + 1638952 * 2 ^ 59
def prefixEnd_1638952 : Nat := 4983230072969 + 3 ^ 40 * 1638952 * 2
def baseEnd_1638952 : Nat := 841570145647776826462603

theorem tailTrace_1638952 : CollatzResearch.WordTrace tailWord_1638952 prefixEnd_1638952 841570145647776826462603 := by
  unfold tailWord_1638952
  simp only [CollatzResearch.WordTrace]
  refine ⟨29888745179182144780939555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39851660238909526374586073 29888745179182144780939555)
  ·
    refine ⟨44833117768773217171409333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29888745179182144780939555 44833117768773217171409333)
    ·
      refine ⟨4203104790822489109819625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44833117768773217171409333 4203104790822489109819625)
      ·
        refine ⟨3152328593116866832364719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4203104790822489109819625 3152328593116866832364719)
        ·
          refine ⟨4728492889675300248547079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3152328593116866832364719 4728492889675300248547079)
          ·
            refine ⟨7092739334512950372820619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728492889675300248547079 7092739334512950372820619)
            ·
              refine ⟨10639109001769425559230929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7092739334512950372820619 10639109001769425559230929)
              ·
                refine ⟨7979331751327069169423197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10639109001769425559230929 7979331751327069169423197)
                ·
                  refine ⟨2992249406747650938533699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7979331751327069169423197 2992249406747650938533699)
                  ·
                    refine ⟨4488374110121476407800549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2992249406747650938533699 4488374110121476407800549)
                    ·
                      refine ⟨841570145647776826462603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4488374110121476407800549 841570145647776826462603)
                      ·
                        rfl

theorem cell23_1638952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1638952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638952 prefixEnd_1638952 := by exact prefixLift 1638952
  have htrace : WordTrace (prefixWord ++ tailWord_1638952) baseStart_1638952 baseEnd_1638952 := by
    simpa [prefixWord, tailWord_1638952, baseEnd_1638952] using wordTrace_append hprefix tailTrace_1638952
  have hstable : (prefixWord ++ tailWord_1638952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638952).length < 2 ^ (prefixWord ++ tailWord_1638952).sum := by decide
  have hdescent : baseEnd_1638952 < baseStart_1638952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638962 : List Nat := [3, 2, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_1638962 : Nat := 118140960795 + 1638962 * 2 ^ 59
def prefixEnd_1638962 : Nat := 4983230072969 + 3 ^ 40 * 1638962 * 2
def baseEnd_1638962 : Nat := 280525093484773929112519

theorem tailTrace_1638962 : CollatzResearch.WordTrace tailWord_1638962 prefixEnd_1638962 280525093484773929112519 := by
  unfold tailWord_1638962
  simp only [CollatzResearch.WordTrace]
  refine ⟨14944463772082015317435785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39851903392218707513162093 14944463772082015317435785)
  ·
    refine ⟨11208347829061511488076839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14944463772082015317435785 11208347829061511488076839)
    ·
      refine ⟨16812521743592267232115259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11208347829061511488076839 16812521743592267232115259)
      ·
        refine ⟨25218782615388400848172889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16812521743592267232115259 25218782615388400848172889)
        ·
          refine ⟨18914086961541300636129667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25218782615388400848172889 18914086961541300636129667)
          ·
            refine ⟨28371130442311950954194501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18914086961541300636129667 28371130442311950954194501)
            ·
              refine ⟨5319586957933490803911469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28371130442311950954194501 5319586957933490803911469)
              ·
                refine ⟨1994845109225059051466801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5319586957933490803911469 1994845109225059051466801)
                ·
                  refine ⟨1496133831918794288600101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1994845109225059051466801 1496133831918794288600101)
                  ·
                    refine ⟨280525093484773929112519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1496133831918794288600101 280525093484773929112519)
                    ·
                      rfl

theorem cell23_1638962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_1638962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638962 prefixEnd_1638962 := by exact prefixLift 1638962
  have htrace : WordTrace (prefixWord ++ tailWord_1638962) baseStart_1638962 baseEnd_1638962 := by
    simpa [prefixWord, tailWord_1638962, baseEnd_1638962] using wordTrace_append hprefix tailTrace_1638962
  have hstable : (prefixWord ++ tailWord_1638962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638962).length < 2 ^ (prefixWord ++ tailWord_1638962).sum := by decide
  have hdescent : baseEnd_1638962 < baseStart_1638962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638969 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 3, 2, 2]
def baseStart_1638969 : Nat := 118140960795 + 1638969 * 2 ^ 59
def prefixEnd_1638969 : Nat := 4983230072969 + 3 ^ 40 * 1638969 * 2
def baseEnd_1638969 : Nat := 841578874818903259950025

theorem tailTrace_1638969 : CollatzResearch.WordTrace tailWord_1638969 prefixEnd_1638969 841578874818903259950025 := by
  unfold tailWord_1638969
  simp only [CollatzResearch.WordTrace]
  refine ⟨59778110399302701465247961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39852073599535134310165307 59778110399302701465247961)
  ·
    refine ⟨44833582799477026098935971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59778110399302701465247961 44833582799477026098935971)
    ·
      refine ⟨67250374199215539148403957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44833582799477026098935971 67250374199215539148403957)
      ·
        refine ⟨6304722581176456795162871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67250374199215539148403957 6304722581176456795162871)
        ·
          refine ⟨9457083871764685192744307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6304722581176456795162871 9457083871764685192744307)
          ·
            refine ⟨14185625807647027789116461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9457083871764685192744307 14185625807647027789116461)
            ·
              refine ⟨5319609677867635420918673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14185625807647027789116461 5319609677867635420918673)
              ·
                refine ⟨3989707258400726565689005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5319609677867635420918673 3989707258400726565689005)
                ·
                  refine ⟨1496140221900272462133377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3989707258400726565689005 1496140221900272462133377)
                  ·
                    refine ⟨1122105166425204346600033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1496140221900272462133377 1122105166425204346600033)
                    ·
                      refine ⟨841578874818903259950025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1122105166425204346600033 841578874818903259950025)
                      ·
                        rfl

theorem cell23_1638969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_1638969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638969 prefixEnd_1638969 := by exact prefixLift 1638969
  have htrace : WordTrace (prefixWord ++ tailWord_1638969) baseStart_1638969 baseEnd_1638969 := by
    simpa [prefixWord, tailWord_1638969, baseEnd_1638969] using wordTrace_append hprefix tailTrace_1638969
  have hstable : (prefixWord ++ tailWord_1638969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638969).length < 2 ^ (prefixWord ++ tailWord_1638969).sum := by decide
  have hdescent : baseEnd_1638969 < baseStart_1638969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638972 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_1638972 : Nat := 118140960795 + 1638972 * 2 ^ 59
def prefixEnd_1638972 : Nat := 4983230072969 + 3 ^ 40 * 1638972 * 2
def baseEnd_1638972 : Nat := 841580415260866748212511

theorem tailTrace_1638972 : CollatzResearch.WordTrace tailWord_1638972 prefixEnd_1638972 841580415260866748212511 := by
  unfold tailWord_1638972
  simp only [CollatzResearch.WordTrace]
  refine ⟨29889109909145916488803585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39852146545527888651738113 29889109909145916488803585)
  ·
    refine ⟨22416832431859437366602689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29889109909145916488803585 22416832431859437366602689)
    ·
      refine ⟨16812624323894578024952017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22416832431859437366602689 16812624323894578024952017)
      ·
        refine ⟨12609468242920933518714013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16812624323894578024952017 12609468242920933518714013)
        ·
          refine ⟨4728550591095350069517755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12609468242920933518714013 4728550591095350069517755)
          ·
            refine ⟨7092825886643025104276633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728550591095350069517755 7092825886643025104276633)
            ·
              refine ⟨5319619414982268828207475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7092825886643025104276633 5319619414982268828207475)
              ·
                refine ⟨7979429122473403242311213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5319619414982268828207475 7979429122473403242311213)
                ·
                  refine ⟨2992285920927526215866705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7979429122473403242311213 2992285920927526215866705)
                  ·
                    refine ⟨2244214440695644661900029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2992285920927526215866705 2244214440695644661900029)
                    ·
                      refine ⟨841580415260866748212511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2244214440695644661900029 841580415260866748212511)
                      ·
                        rfl

theorem cell23_1638972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_1638972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638972 prefixEnd_1638972 := by exact prefixLift 1638972
  have htrace : WordTrace (prefixWord ++ tailWord_1638972) baseStart_1638972 baseEnd_1638972 := by
    simpa [prefixWord, tailWord_1638972, baseEnd_1638972] using wordTrace_append hprefix tailTrace_1638972
  have hstable : (prefixWord ++ tailWord_1638972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638972).length < 2 ^ (prefixWord ++ tailWord_1638972).sum := by decide
  have hdescent : baseEnd_1638972 < baseStart_1638972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638975 : List Nat := [1, 1, 2, 2, 3, 2, 5, 7]
def baseStart_1638975 : Nat := 118140960795 + 1638975 * 2 ^ 59
def prefixEnd_1638975 : Nat := 4983230072969 + 3 ^ 40 * 1638975 * 2
def baseEnd_1638975 : Nat := 31169702063067786536111

theorem tailTrace_1638975 : CollatzResearch.WordTrace tailWord_1638975 prefixEnd_1638975 31169702063067786536111 := by
  unfold tailWord_1638975
  simp only [CollatzResearch.WordTrace]
  refine ⟨59778329237280964489966379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39852219491520642993310919 59778329237280964489966379)
  ·
    refine ⟨89667493855921446734949569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59778329237280964489966379 89667493855921446734949569)
    ·
      refine ⟨67250620391941085051212177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89667493855921446734949569 67250620391941085051212177)
      ·
        refine ⟨50437965293955813788409133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67250620391941085051212177 50437965293955813788409133)
        ·
          refine ⟨18914236985233430170653425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50437965293955813788409133 18914236985233430170653425)
          ·
            refine ⟨14185677738925072627990069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18914236985233430170653425 14185677738925072627990069)
            ·
              refine ⟨1329907288024225558874069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14185677738925072627990069 1329907288024225558874069)
              ·
                refine ⟨31169702063067786536111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1329907288024225558874069 31169702063067786536111)
                ·
                  rfl

theorem cell23_1638975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 7].length) (baseStart_1638975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638975 prefixEnd_1638975 := by exact prefixLift 1638975
  have htrace : WordTrace (prefixWord ++ tailWord_1638975) baseStart_1638975 baseEnd_1638975 := by
    simpa [prefixWord, tailWord_1638975, baseEnd_1638975] using wordTrace_append hprefix tailTrace_1638975
  have hstable : (prefixWord ++ tailWord_1638975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638975).length < 2 ^ (prefixWord ++ tailWord_1638975).sum := by decide
  have hdescent : baseEnd_1638975 < baseStart_1638975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1638986 : List Nat := [3, 1, 2, 1, 1, 4, 1, 5, 1, 2, 2]
def baseStart_1638986 : Nat := 118140960795 + 1638986 * 2 ^ 59
def prefixEnd_1638986 : Nat := 4983230072969 + 3 ^ 40 * 1638986 * 2
def baseEnd_1638986 : Nat := 841587603990029693437447

theorem tailTrace_1638986 : CollatzResearch.WordTrace tailWord_1638986 prefixEnd_1638986 841587603990029693437447 := by
  unfold tailWord_1638986
  simp only [CollatzResearch.WordTrace]
  refine ⟨14944682610060278342154203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39852486960160742245744541 14944682610060278342154203)
  ·
    refine ⟨22417023915090417513231305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14944682610060278342154203 22417023915090417513231305)
    ·
      refine ⟨16812767936317813134923479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22417023915090417513231305 16812767936317813134923479)
      ·
        refine ⟨25219151904476719702385219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16812767936317813134923479 25219151904476719702385219)
        ·
          refine ⟨37828727856715079553577829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25219151904476719702385219 37828727856715079553577829)
          ·
            refine ⟨7092886473134077416295843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37828727856715079553577829 7092886473134077416295843)
            ·
              refine ⟨10639329709701116124443765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7092886473134077416295843 10639329709701116124443765)
              ·
                refine ⟨997437160284479636666603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10639329709701116124443765 997437160284479636666603)
                ·
                  refine ⟨1496155740426719454999905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997437160284479636666603 1496155740426719454999905)
                  ·
                    refine ⟨1122116805320039591249929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1496155740426719454999905 1122116805320039591249929)
                    ·
                      refine ⟨841587603990029693437447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1122116805320039591249929 841587603990029693437447)
                      ·
                        rfl

theorem cell23_1638986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_1638986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1638986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1638986 prefixEnd_1638986 := by exact prefixLift 1638986
  have htrace : WordTrace (prefixWord ++ tailWord_1638986) baseStart_1638986 baseEnd_1638986 := by
    simpa [prefixWord, tailWord_1638986, baseEnd_1638986] using wordTrace_append hprefix tailTrace_1638986
  have hstable : (prefixWord ++ tailWord_1638986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1638986).length < 2 ^ (prefixWord ++ tailWord_1638986).sum := by decide
  have hdescent : baseEnd_1638986 < baseStart_1638986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1638986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639016 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_1639016 : Nat := 118140960795 + 1639016 * 2 ^ 59
def prefixEnd_1639016 : Nat := 4983230072969 + 3 ^ 40 * 1639016 * 2
def baseEnd_1639016 : Nat := 841603008409664576062309

theorem tailTrace_1639016 : CollatzResearch.WordTrace tailWord_1639016 prefixEnd_1639016 841603008409664576062309 := by
  unfold tailWord_1639016
  simp only [CollatzResearch.WordTrace]
  refine ⟨29889912315066214246104451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39853216420088285661472601 29889912315066214246104451)
  ·
    refine ⟨44834868472599321369156677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29889912315066214246104451 44834868472599321369156677)
    ·
      refine ⟨8406537838612372756716877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44834868472599321369156677 8406537838612372756716877)
      ·
        refine ⟨3152451689479639783768829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8406537838612372756716877 3152451689479639783768829)
        ·
          refine ⟨1182169383554864918913311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3152451689479639783768829 1182169383554864918913311)
          ·
            refine ⟨1773254075332297378369967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182169383554864918913311 1773254075332297378369967)
            ·
              refine ⟨2659881112998446067554951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1773254075332297378369967 2659881112998446067554951)
              ·
                refine ⟨3989821669497669101332427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659881112998446067554951 3989821669497669101332427)
                ·
                  refine ⟨5984732504246503651998641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3989821669497669101332427 5984732504246503651998641)
                  ·
                    refine ⟨4488549378184877738998981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5984732504246503651998641 4488549378184877738998981)
                    ·
                      refine ⟨841603008409664576062309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4488549378184877738998981 841603008409664576062309)
                      ·
                        rfl

theorem cell23_1639016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_1639016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639016 prefixEnd_1639016 := by exact prefixLift 1639016
  have htrace : WordTrace (prefixWord ++ tailWord_1639016) baseStart_1639016 baseEnd_1639016 := by
    simpa [prefixWord, tailWord_1639016, baseEnd_1639016] using wordTrace_append hprefix tailTrace_1639016
  have hstable : (prefixWord ++ tailWord_1639016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639016).length < 2 ^ (prefixWord ++ tailWord_1639016).sum := by decide
  have hdescent : baseEnd_1639016 < baseStart_1639016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639045 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_1639045 : Nat := 118140960795 + 1639045 * 2 ^ 59
def prefixEnd_1639045 : Nat := 4983230072969 + 3 ^ 40 * 1639045 * 2
def baseEnd_1639045 : Nat := 841617899348644962599675

theorem tailTrace_1639045 : CollatzResearch.WordTrace tailWord_1639045 prefixEnd_1639045 841617899348644962599675 := by
  unfold tailWord_1639045
  simp only [CollatzResearch.WordTrace]
  refine ⟨59780882347027366445014589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39853921564684910963343059 59780882347027366445014589)
  ·
    refine ⟨22417830880135262416880471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59780882347027366445014589 22417830880135262416880471)
    ·
      refine ⟨33626746320202893625320707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22417830880135262416880471 33626746320202893625320707)
      ·
        refine ⟨50440119480304340437981061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33626746320202893625320707 50440119480304340437981061)
        ·
          refine ⟨9457522402557063832121449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50440119480304340437981061 9457522402557063832121449)
          ·
            refine ⟨7093141801917797874091087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9457522402557063832121449 7093141801917797874091087)
            ·
              refine ⟨10639712702876696811136631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7093141801917797874091087 10639712702876696811136631)
              ·
                refine ⟨15959569054315045216704947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10639712702876696811136631 15959569054315045216704947)
                ·
                  refine ⟨23939353581472567825057421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15959569054315045216704947 23939353581472567825057421)
                  ·
                    refine ⟨8977257593052212934396533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23939353581472567825057421 8977257593052212934396533)
                    ·
                      refine ⟨841617899348644962599675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8977257593052212934396533 841617899348644962599675)
                      ·
                        rfl

theorem cell23_1639045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_1639045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639045 prefixEnd_1639045 := by exact prefixLift 1639045
  have htrace : WordTrace (prefixWord ++ tailWord_1639045) baseStart_1639045 baseEnd_1639045 := by
    simpa [prefixWord, tailWord_1639045, baseEnd_1639045] using wordTrace_append hprefix tailTrace_1639045
  have hstable : (prefixWord ++ tailWord_1639045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639045).length < 2 ^ (prefixWord ++ tailWord_1639045).sum := by decide
  have hdescent : baseEnd_1639045 < baseStart_1639045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639076 : List Nat := [2, 3, 1, 2, 2, 1, 3, 3, 2, 2, 2]
def baseStart_1639076 : Nat := 118140960795 + 1639076 * 2 ^ 59
def prefixEnd_1639076 : Nat := 4983230072969 + 3 ^ 40 * 1639076 * 2
def baseEnd_1639076 : Nat := 841633817248934341312033

theorem tailTrace_1639076 : CollatzResearch.WordTrace tailWord_1639076 prefixEnd_1639076 841633817248934341312033 := by
  unfold tailWord_1639076
  simp only [CollatzResearch.WordTrace]
  refine ⟨29891006504957529369696541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39854675339943372492928721 29891006504957529369696541)
  ·
    refine ⟨11209127439359073513636203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29891006504957529369696541 11209127439359073513636203)
    ·
      refine ⟨16813691159038610270454305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11209127439359073513636203 16813691159038610270454305)
      ·
        refine ⟨12610268369278957702840729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16813691159038610270454305 12610268369278957702840729)
        ·
          refine ⟨9457701276959218277130547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12610268369278957702840729 9457701276959218277130547)
          ·
            refine ⟨14186551915438827415695821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9457701276959218277130547 14186551915438827415695821)
            ·
              refine ⟨5319956968289560280885933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14186551915438827415695821 5319956968289560280885933)
              ·
                refine ⟨1994983863108585105332225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5319956968289560280885933 1994983863108585105332225)
                ·
                  refine ⟨1496237897331438828999169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1994983863108585105332225 1496237897331438828999169)
                  ·
                    refine ⟨1122178422998579121749377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1496237897331438828999169 1122178422998579121749377)
                    ·
                      refine ⟨841633817248934341312033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1122178422998579121749377 841633817248934341312033)
                      ·
                        rfl

theorem cell23_1639076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_1639076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639076 prefixEnd_1639076 := by exact prefixLift 1639076
  have htrace : WordTrace (prefixWord ++ tailWord_1639076) baseStart_1639076 baseEnd_1639076 := by
    simpa [prefixWord, tailWord_1639076, baseEnd_1639076] using wordTrace_append hprefix tailTrace_1639076
  have hstable : (prefixWord ++ tailWord_1639076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639076).length < 2 ^ (prefixWord ++ tailWord_1639076).sum := by decide
  have hdescent : baseEnd_1639076 < baseStart_1639076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639112 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 2, 5]
def baseStart_1639112 : Nat := 118140960795 + 1639112 * 2 ^ 59
def prefixEnd_1639112 : Nat := 4983230072969 + 3 ^ 40 * 1639112 * 2
def baseEnd_1639112 : Nat := 280550767517498733487289

theorem tailTrace_1639112 : CollatzResearch.WordTrace tailWord_1639112 prefixEnd_1639112 280550767517498733487289 := by
  unfold tailWord_1639112
  simp only [CollatzResearch.WordTrace]
  refine ⟨29891663018892318443851795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39855550691856424591802393 29891663018892318443851795)
  ·
    refine ⟨44837494528338477665777693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29891663018892318443851795 44837494528338477665777693)
    ·
      refine ⟨16814060448126929124666635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44837494528338477665777693 16814060448126929124666635)
      ·
        refine ⟨25221090672190393686999953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16814060448126929124666635 25221090672190393686999953)
        ·
          refine ⟨18915818004142795265249965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25221090672190393686999953 18915818004142795265249965)
          ·
            refine ⟨7093431751553548224468737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18915818004142795265249965 7093431751553548224468737)
            ·
              refine ⟨5320073813665161168351553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7093431751553548224468737 5320073813665161168351553)
              ·
                refine ⟨3990055360248870876263665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5320073813665161168351553 3990055360248870876263665)
                ·
                  refine ⟨2992541520186653157197749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3990055360248870876263665 2992541520186653157197749)
                  ·
                    refine ⟨280550767517498733487289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2992541520186653157197749 280550767517498733487289)
                    ·
                      rfl

theorem cell23_1639112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_1639112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639112 prefixEnd_1639112 := by exact prefixLift 1639112
  have htrace : WordTrace (prefixWord ++ tailWord_1639112) baseStart_1639112 baseEnd_1639112 := by
    simpa [prefixWord, tailWord_1639112, baseEnd_1639112] using wordTrace_append hprefix tailTrace_1639112
  have hstable : (prefixWord ++ tailWord_1639112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639112).length < 2 ^ (prefixWord ++ tailWord_1639112).sum := by decide
  have hdescent : baseEnd_1639112 < baseStart_1639112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639115 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 4]
def baseStart_1639115 : Nat := 118140960795 + 1639115 * 2 ^ 59
def prefixEnd_1639115 : Nat := 4983230072969 + 3 ^ 40 * 1639115 * 2
def baseEnd_1639115 : Nat := 841653842994459688724353

theorem tailTrace_1639115 : CollatzResearch.WordTrace tailWord_1639115 prefixEnd_1639115 841653842994459688724353 := by
  unfold tailWord_1639115
  simp only [CollatzResearch.WordTrace]
  refine ⟨59783435456773768400062799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39855623637849178933375199 59783435456773768400062799)
  ·
    refine ⟨89675153185160652600094199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59783435456773768400062799 89675153185160652600094199)
    ·
      refine ⟨134512729777740978900141299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89675153185160652600094199 134512729777740978900141299)
      ·
        refine ⟨201769094666611468350211949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134512729777740978900141299 201769094666611468350211949)
        ·
          refine ⟨75663410499979300631329481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201769094666611468350211949 75663410499979300631329481)
          ·
            refine ⟨56747557874984475473497111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75663410499979300631329481 56747557874984475473497111)
            ·
              refine ⟨85121336812476713210245667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56747557874984475473497111 85121336812476713210245667)
              ·
                refine ⟨127682005218715069815368501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85121336812476713210245667 127682005218715069815368501)
                ·
                  refine ⟨11970187989254537795190797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127682005218715069815368501 11970187989254537795190797)
                  ·
                    refine ⟨4488820495970451673196549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11970187989254537795190797 4488820495970451673196549)
                    ·
                      refine ⟨841653842994459688724353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4488820495970451673196549 841653842994459688724353)
                      ·
                        rfl

theorem cell23_1639115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 4].length) (baseStart_1639115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639115 prefixEnd_1639115 := by exact prefixLift 1639115
  have htrace : WordTrace (prefixWord ++ tailWord_1639115) baseStart_1639115 baseEnd_1639115 := by
    simpa [prefixWord, tailWord_1639115, baseEnd_1639115] using wordTrace_append hprefix tailTrace_1639115
  have hstable : (prefixWord ++ tailWord_1639115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639115).length < 2 ^ (prefixWord ++ tailWord_1639115).sum := by decide
  have hdescent : baseEnd_1639115 < baseStart_1639115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639116 : List Nat := [2, 2, 1, 5, 1, 1, 4, 2, 5]
def baseStart_1639116 : Nat := 118140960795 + 1639116 * 2 ^ 59
def prefixEnd_1639116 : Nat := 4983230072969 + 3 ^ 40 * 1639116 * 2
def baseEnd_1639116 : Nat := 93517150719457131645761

theorem tailTrace_1639116 : CollatzResearch.WordTrace tailWord_1639116 prefixEnd_1639116 93517150719457131645761 := by
  unfold tailWord_1639116
  simp only [CollatzResearch.WordTrace]
  refine ⟨29891735964885072785424601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39855647953180097047232801 29891735964885072785424601)
  ·
    refine ⟨22418801973663804589068451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29891735964885072785424601 22418801973663804589068451)
    ·
      refine ⟨33628202960495706883602677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22418801973663804589068451 33628202960495706883602677)
      ·
        refine ⟨3152644027546472520337751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33628202960495706883602677 3152644027546472520337751)
        ·
          refine ⟨4728966041319708780506627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3152644027546472520337751 4728966041319708780506627)
          ·
            refine ⟨7093449061979563170759941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728966041319708780506627 7093449061979563170759941)
            ·
              refine ⟨1330021699121168094517489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7093449061979563170759941 1330021699121168094517489)
              ·
                refine ⟨997516274340876070888117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1330021699121168094517489 997516274340876070888117)
                ·
                  refine ⟨93517150719457131645761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 997516274340876070888117 93517150719457131645761)
                  ·
                    rfl

theorem cell23_1639116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 5].length) (baseStart_1639116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639116 prefixEnd_1639116 := by exact prefixLift 1639116
  have htrace : WordTrace (prefixWord ++ tailWord_1639116) baseStart_1639116 baseEnd_1639116 := by
    simpa [prefixWord, tailWord_1639116, baseEnd_1639116] using wordTrace_append hprefix tailTrace_1639116
  have hstable : (prefixWord ++ tailWord_1639116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639116).length < 2 ^ (prefixWord ++ tailWord_1639116).sum := by decide
  have hdescent : baseEnd_1639116 < baseStart_1639116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639149 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_1639149 : Nat := 118140960795 + 1639149 * 2 ^ 59
def prefixEnd_1639149 : Nat := 4983230072969 + 3 ^ 40 * 1639149 * 2
def baseEnd_1639149 : Nat := 841671301336712555699197

theorem tailTrace_1639149 : CollatzResearch.WordTrace tailWord_1639149 prefixEnd_1639149 841671301336712555699197 := by
  unfold tailWord_1639149
  simp only [CollatzResearch.WordTrace]
  refine ⟨59784675538650592206800501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39856450359100394804533667 59784675538650592206800501)
  ·
    refine ⟨5604813331748493019387547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59784675538650592206800501 5604813331748493019387547)
    ·
      refine ⟨8407219997622739529081321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5604813331748493019387547 8407219997622739529081321)
      ·
        refine ⟨6305414998217054646810991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8407219997622739529081321 6305414998217054646810991)
        ·
          refine ⟨9458122497325581970216487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6305414998217054646810991 9458122497325581970216487)
          ·
            refine ⟨14187183745988372955324731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9458122497325581970216487 14187183745988372955324731)
            ·
              refine ⟨21280775618982559432987097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14187183745988372955324731 21280775618982559432987097)
              ·
                refine ⟨15960581714236919574740323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21280775618982559432987097 15960581714236919574740323)
                ·
                  refine ⟨23940872571355379362110485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15960581714236919574740323 23940872571355379362110485)
                  ·
                    refine ⟨1122228401782283407598929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23940872571355379362110485 1122228401782283407598929)
                    ·
                      refine ⟨841671301336712555699197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1122228401782283407598929 841671301336712555699197)
                      ·
                        rfl

theorem cell23_1639149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_1639149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639149 prefixEnd_1639149 := by exact prefixLift 1639149
  have htrace : WordTrace (prefixWord ++ tailWord_1639149) baseStart_1639149 baseEnd_1639149 := by
    simpa [prefixWord, tailWord_1639149, baseEnd_1639149] using wordTrace_append hprefix tailTrace_1639149
  have hstable : (prefixWord ++ tailWord_1639149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639149).length < 2 ^ (prefixWord ++ tailWord_1639149).sum := by decide
  have hdescent : baseEnd_1639149 < baseStart_1639149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639152 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 3]
def baseStart_1639152 : Nat := 118140960795 + 1639152 * 2 ^ 59
def prefixEnd_1639152 : Nat := 4983230072969 + 3 ^ 40 * 1639152 * 2
def baseEnd_1639152 : Nat := 841672841778676043961683

theorem tailTrace_1639152 : CollatzResearch.WordTrace tailWord_1639152 prefixEnd_1639152 841672841778676043961683 := by
  unfold tailWord_1639152
  simp only [CollatzResearch.WordTrace]
  refine ⟨29892392478819861859579855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39856523305093149146106473 29892392478819861859579855)
  ·
    refine ⟨44838588718229792789369783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29892392478819861859579855 44838588718229792789369783)
    ·
      refine ⟨67257883077344689184054675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44838588718229792789369783 67257883077344689184054675)
      ·
        refine ⟨100886824616017033776082013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67257883077344689184054675 100886824616017033776082013)
        ·
          refine ⟨37832559231006387666030755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100886824616017033776082013 37832559231006387666030755)
          ·
            refine ⟨56748838846509581499046133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37832559231006387666030755 56748838846509581499046133)
            ·
              refine ⟨5320203641860273265535575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56748838846509581499046133 5320203641860273265535575)
              ·
                refine ⟨7980305462790409898303363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5320203641860273265535575 7980305462790409898303363)
                ·
                  refine ⟨11970458194185614847455045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7980305462790409898303363 11970458194185614847455045)
                  ·
                    refine ⟨2244460911409802783897821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11970458194185614847455045 2244460911409802783897821)
                    ·
                      refine ⟨841672841778676043961683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2244460911409802783897821 841672841778676043961683)
                      ·
                        rfl

theorem cell23_1639152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 3].length) (baseStart_1639152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639152 prefixEnd_1639152 := by exact prefixLift 1639152
  have htrace : WordTrace (prefixWord ++ tailWord_1639152) baseStart_1639152 baseEnd_1639152 := by
    simpa [prefixWord, tailWord_1639152, baseEnd_1639152] using wordTrace_append hprefix tailTrace_1639152
  have hstable : (prefixWord ++ tailWord_1639152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639152).length < 2 ^ (prefixWord ++ tailWord_1639152).sum := by decide
  have hdescent : baseEnd_1639152 < baseStart_1639152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639155 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 8]
def baseStart_1639155 : Nat := 118140960795 + 1639155 * 2 ^ 59
def prefixEnd_1639155 : Nat := 4983230072969 + 3 ^ 40 * 1639155 * 2
def baseEnd_1639155 : Nat := 93519375802293281358241

theorem tailTrace_1639155 : CollatzResearch.WordTrace tailWord_1639155 prefixEnd_1639155 93519375802293281358241 := by
  unfold tailWord_1639155
  simp only [CollatzResearch.WordTrace]
  refine ⟨59784894376628855231518919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39856596251085903487679279 59784894376628855231518919)
  ·
    refine ⟨89677341564943282847278379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59784894376628855231518919 89677341564943282847278379)
    ·
      refine ⟨134516012347414924270917569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89677341564943282847278379 134516012347414924270917569)
      ·
        refine ⟨100887009260561193203188177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134516012347414924270917569 100887009260561193203188177)
        ·
          refine ⟨75665256945420894902391133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100887009260561193203188177 75665256945420894902391133)
          ·
            refine ⟨28374471354532835588396675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75665256945420894902391133 28374471354532835588396675)
            ·
              refine ⟨42561707031799253382595013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28374471354532835588396675 42561707031799253382595013)
              ·
                refine ⟨7980320068462360009236565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42561707031799253382595013 7980320068462360009236565)
                ·
                  refine ⟨93519375802293281358241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7980320068462360009236565 93519375802293281358241)
                  ·
                    rfl

theorem cell23_1639155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 8].length) (baseStart_1639155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639155 prefixEnd_1639155 := by exact prefixLift 1639155
  have htrace : WordTrace (prefixWord ++ tailWord_1639155) baseStart_1639155 baseEnd_1639155 := by
    simpa [prefixWord, tailWord_1639155, baseEnd_1639155] using wordTrace_append hprefix tailTrace_1639155
  have hstable : (prefixWord ++ tailWord_1639155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639155).length < 2 ^ (prefixWord ++ tailWord_1639155).sum := by decide
  have hdescent : baseEnd_1639155 < baseStart_1639155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639166 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_1639166 : Nat := 118140960795 + 1639166 * 2 ^ 59
def prefixEnd_1639166 : Nat := 4983230072969 + 3 ^ 40 * 1639166 * 2
def baseEnd_1639166 : Nat := 841680030507838989186619

theorem tailTrace_1639166 : CollatzResearch.WordTrace tailWord_1639166 prefixEnd_1639166 841680030507838989186619 := by
  unfold tailWord_1639166
  simp only [CollatzResearch.WordTrace]
  refine ⟨7473161947448625513771169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39856863719726002740112901 7473161947448625513771169)
  ·
    refine ⟨5604871460586469135328377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7473161947448625513771169 5604871460586469135328377)
    ·
      refine ⟨4203653595439851851496283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5604871460586469135328377 4203653595439851851496283)
      ·
        refine ⟨6305480393159777777244425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4203653595439851851496283 6305480393159777777244425)
        ·
          refine ⟨4729110294869833332933319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6305480393159777777244425 4729110294869833332933319)
          ·
            refine ⟨7093665442304749999399979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4729110294869833332933319 7093665442304749999399979)
            ·
              refine ⟨10640498163457124999099969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7093665442304749999399979 10640498163457124999099969)
              ·
                refine ⟨7980373622592843749324977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10640498163457124999099969 7980373622592843749324977)
                ·
                  refine ⟨5985280216944632811993733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7980373622592843749324977 5985280216944632811993733)
                  ·
                    refine ⟨1122240040677118652248825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5985280216944632811993733 1122240040677118652248825)
                    ·
                      refine ⟨841680030507838989186619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1122240040677118652248825 841680030507838989186619)
                      ·
                        rfl

theorem cell23_1639166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_1639166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639166 prefixEnd_1639166 := by exact prefixLift 1639166
  have htrace : WordTrace (prefixWord ++ tailWord_1639166) baseStart_1639166 baseEnd_1639166 := by
    simpa [prefixWord, tailWord_1639166, baseEnd_1639166] using wordTrace_append hprefix tailTrace_1639166
  have hstable : (prefixWord ++ tailWord_1639166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639166).length < 2 ^ (prefixWord ++ tailWord_1639166).sum := by decide
  have hdescent : baseEnd_1639166 < baseStart_1639166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639172 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 8]
def baseStart_1639172 : Nat := 118140960795 + 1639172 * 2 ^ 59
def prefixEnd_1639172 : Nat := 4983230072969 + 3 ^ 40 * 1639172 * 2
def baseEnd_1639172 : Nat := 93520345710196218412399

theorem tailTrace_1639172 : CollatzResearch.WordTrace tailWord_1639172 prefixEnd_1639172 93520345710196218412399 := by
  unfold tailWord_1639172
  simp only [CollatzResearch.WordTrace]
  refine ⟨29892757208783633567443885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39857009611711511423258513 29892757208783633567443885)
  ·
    refine ⟨11209783953293862587791457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29892757208783633567443885 11209783953293862587791457)
    ·
      refine ⟨8407337964970396940843593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11209783953293862587791457 8407337964970396940843593)
      ·
        refine ⟨6305503473727797705632695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8407337964970396940843593 6305503473727797705632695)
        ·
          refine ⟨9458255210591696558449043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6305503473727797705632695 9458255210591696558449043)
          ·
            refine ⟨14187382815887544837673565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9458255210591696558449043 14187382815887544837673565)
            ·
              refine ⟨5320268555957829314127587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14187382815887544837673565 5320268555957829314127587)
              ·
                refine ⟨7980402833936743971191381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5320268555957829314127587 7980402833936743971191381)
                ·
                  refine ⟨93520345710196218412399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7980402833936743971191381 93520345710196218412399)
                  ·
                    rfl

theorem cell23_1639172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_1639172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639172 prefixEnd_1639172 := by exact prefixLift 1639172
  have htrace : WordTrace (prefixWord ++ tailWord_1639172) baseStart_1639172 baseEnd_1639172 := by
    simpa [prefixWord, tailWord_1639172, baseEnd_1639172] using wordTrace_append hprefix tailTrace_1639172
  have hstable : (prefixWord ++ tailWord_1639172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639172).length < 2 ^ (prefixWord ++ tailWord_1639172).sum := by decide
  have hdescent : baseEnd_1639172 < baseStart_1639172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639176 : List Nat := [2, 1, 3, 2, 2, 2, 2, 4, 1, 4]
def baseStart_1639176 : Nat := 118140960795 + 1639176 * 2 ^ 59
def prefixEnd_1639176 : Nat := 4983230072969 + 3 ^ 40 * 1639176 * 2
def baseEnd_1639176 : Nat := 280561721771461316687191

theorem tailTrace_1639176 : CollatzResearch.WordTrace tailWord_1639176 prefixEnd_1639176 280561721771461316687191 := by
  unfold tailWord_1639176
  simp only [CollatzResearch.WordTrace]
  refine ⟨29892830154776387909016691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39857106873035183878688921 29892830154776387909016691)
  ·
    refine ⟨44839245232164581863525037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29892830154776387909016691 44839245232164581863525037)
    ·
      refine ⟨16814716962061718198821889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44839245232164581863525037 16814716962061718198821889)
      ·
        refine ⟨12611037721546288649116417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16814716962061718198821889 12611037721546288649116417)
        ·
          refine ⟨9458278291159716486837313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12611037721546288649116417 9458278291159716486837313)
          ·
            refine ⟨7093708718369787365127985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9458278291159716486837313 7093708718369787365127985)
            ·
              refine ⟨5320281538777340523845989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7093708718369787365127985 5320281538777340523845989)
              ·
                refine ⟨997552788520751348221123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5320281538777340523845989 997552788520751348221123)
                ·
                  refine ⟨1496329182781127022331685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997552788520751348221123 1496329182781127022331685)
                  ·
                    refine ⟨280561721771461316687191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1496329182781127022331685 280561721771461316687191)
                    ·
                      rfl

theorem cell23_1639176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_1639176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639176 prefixEnd_1639176 := by exact prefixLift 1639176
  have htrace : WordTrace (prefixWord ++ tailWord_1639176) baseStart_1639176 baseEnd_1639176 := by
    simpa [prefixWord, tailWord_1639176, baseEnd_1639176] using wordTrace_append hprefix tailTrace_1639176
  have hstable : (prefixWord ++ tailWord_1639176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639176).length < 2 ^ (prefixWord ++ tailWord_1639176).sum := by decide
  have hdescent : baseEnd_1639176 < baseStart_1639176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639189 : List Nat := [1, 3, 2, 1, 2, 2, 5, 1, 6]
def baseStart_1639189 : Nat := 118140960795 + 1639189 * 2 ^ 59
def prefixEnd_1639189 : Nat := 4983230072969 + 3 ^ 40 * 1639189 * 2
def baseEnd_1639189 : Nat := 93521315618099155466557

theorem tailTrace_1639189 : CollatzResearch.WordTrace tailWord_1639189 prefixEnd_1639189 93521315618099155466557 := by
  unfold tailWord_1639189
  simp only [CollatzResearch.WordTrace]
  refine ⟨59786134458505679038256621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39857422972337119358837747 59786134458505679038256621)
  ·
    refine ⟨22419800421939629639346233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59786134458505679038256621 22419800421939629639346233)
    ·
      refine ⟨16814850316454722229509675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22419800421939629639346233 16814850316454722229509675)
      ·
        refine ⟨25222275474682083344264513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16814850316454722229509675 25222275474682083344264513)
        ·
          refine ⟨18916706606011562508198385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25222275474682083344264513 18916706606011562508198385)
          ·
            refine ⟨14187529954508671881148789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18916706606011562508198385 14187529954508671881148789)
            ·
              refine ⟨1330080933235187988857699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14187529954508671881148789 1330080933235187988857699)
              ·
                refine ⟨1995121399852781983286549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330080933235187988857699 1995121399852781983286549)
                ·
                  refine ⟨93521315618099155466557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1995121399852781983286549 93521315618099155466557)
                  ·
                    rfl

theorem cell23_1639189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 6].length) (baseStart_1639189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639189 prefixEnd_1639189 := by exact prefixLift 1639189
  have htrace : WordTrace (prefixWord ++ tailWord_1639189) baseStart_1639189 baseEnd_1639189 := by
    simpa [prefixWord, tailWord_1639189, baseEnd_1639189] using wordTrace_append hprefix tailTrace_1639189
  have hstable : (prefixWord ++ tailWord_1639189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639189).length < 2 ^ (prefixWord ++ tailWord_1639189).sum := by decide
  have hdescent : baseEnd_1639189 < baseStart_1639189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639219 : List Nat := [1, 1, 1, 2, 6, 1, 2, 3, 1, 5]
def baseStart_1639219 : Nat := 118140960795 + 1639219 * 2 ^ 59
def prefixEnd_1639219 : Nat := 4983230072969 + 3 ^ 40 * 1639219 * 2
def baseEnd_1639219 : Nat := 280569081660842427274625

theorem tailTrace_1639219 : CollatzResearch.WordTrace tailWord_1639219 prefixEnd_1639219 280569081660842427274625 := by
  unfold tailWord_1639219
  simp only [CollatzResearch.WordTrace]
  refine ⟨59787228648396994161848711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39858152432264662774565807 59787228648396994161848711)
  ·
    refine ⟨89680842972595491242773067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59787228648396994161848711 89680842972595491242773067)
    ·
      refine ⟨134521264458893236864159601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89680842972595491242773067 134521264458893236864159601)
      ·
        refine ⟨100890948344169927648119701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134521264458893236864159601 100890948344169927648119701)
        ·
          refine ⟨4729263203632965358505611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100890948344169927648119701 4729263203632965358505611)
          ·
            refine ⟨7093894805449448037758417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4729263203632965358505611 7093894805449448037758417)
            ·
              refine ⟨5320421104087086028318813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7093894805449448037758417 5320421104087086028318813)
              ·
                refine ⟨1995157914032657260619555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5320421104087086028318813 1995157914032657260619555)
                ·
                  refine ⟨2992736871048985890929333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995157914032657260619555 2992736871048985890929333)
                  ·
                    refine ⟨280569081660842427274625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2992736871048985890929333 280569081660842427274625)
                    ·
                      rfl

theorem cell23_1639219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 5].length) (baseStart_1639219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639219 prefixEnd_1639219 := by exact prefixLift 1639219
  have htrace : WordTrace (prefixWord ++ tailWord_1639219) baseStart_1639219 baseEnd_1639219 := by
    simpa [prefixWord, tailWord_1639219, baseEnd_1639219] using wordTrace_append hprefix tailTrace_1639219
  have hstable : (prefixWord ++ tailWord_1639219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639219).length < 2 ^ (prefixWord ++ tailWord_1639219).sum := by decide
  have hdescent : baseEnd_1639219 < baseStart_1639219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639242 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_1639242 : Nat := 118140960795 + 1639242 * 2 ^ 59
def prefixEnd_1639242 : Nat := 4983230072969 + 3 ^ 40 * 1639242 * 2
def baseEnd_1639242 : Nat := 841719055037580691836269

theorem tailTrace_1639242 : CollatzResearch.WordTrace tailWord_1639242 prefixEnd_1639242 841719055037580691836269 := by
  unfold tailWord_1639242
  simp only [CollatzResearch.WordTrace]
  refine ⟨14947016881828417272483995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39858711684875779393290653 14947016881828417272483995)
  ·
    refine ⟨22420525322742625908725993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14947016881828417272483995 22420525322742625908725993)
    ·
      refine ⟨16815393992056969431544495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22420525322742625908725993 16815393992056969431544495)
      ·
        refine ⟨25223090988085454147316743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16815393992056969431544495 25223090988085454147316743)
        ·
          refine ⟨37834636482128181220975115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25223090988085454147316743 37834636482128181220975115)
          ·
            refine ⟨56751954723192271831462673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37834636482128181220975115 56751954723192271831462673)
            ·
              refine ⟨42563966042394203873597005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56751954723192271831462673 42563966042394203873597005)
              ·
                refine ⟨15961487265897826452598877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42563966042394203873597005 15961487265897826452598877)
                ·
                  refine ⟨5985557724711684919724579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15961487265897826452598877 5985557724711684919724579)
                  ·
                    refine ⟨8978336587067527379586869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5985557724711684919724579 8978336587067527379586869)
                    ·
                      refine ⟨841719055037580691836269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8978336587067527379586869 841719055037580691836269)
                      ·
                        rfl

theorem cell23_1639242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_1639242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639242 prefixEnd_1639242 := by exact prefixLift 1639242
  have htrace : WordTrace (prefixWord ++ tailWord_1639242) baseStart_1639242 baseEnd_1639242 := by
    simpa [prefixWord, tailWord_1639242, baseEnd_1639242] using wordTrace_append hprefix tailTrace_1639242
  have hstable : (prefixWord ++ tailWord_1639242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639242).length < 2 ^ (prefixWord ++ tailWord_1639242).sum := by decide
  have hdescent : baseEnd_1639242 < baseStart_1639242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639256 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 3, 2, 2]
def baseStart_1639256 : Nat := 118140960795 + 1639256 * 2 ^ 59
def prefixEnd_1639256 : Nat := 4983230072969 + 3 ^ 40 * 1639256 * 2
def baseEnd_1639256 : Nat := 841726243766743637061205

theorem tailTrace_1639256 : CollatzResearch.WordTrace tailWord_1639256 prefixEnd_1639256 841726243766743637061205 := by
  unfold tailWord_1639256
  simp only [CollatzResearch.WordTrace]
  refine ⟨29894289074631474740472811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39859052099508632987297081 29894289074631474740472811)
  ·
    refine ⟨44841433611947212110709217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29894289074631474740472811 44841433611947212110709217)
    ·
      refine ⟨33631075208960409083031913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44841433611947212110709217 33631075208960409083031913)
      ·
        refine ⟨25223306406720306812273935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33631075208960409083031913 25223306406720306812273935)
        ·
          refine ⟨37834959610080460218410903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25223306406720306812273935 37834959610080460218410903)
          ·
            refine ⟨56752439415120690327616355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37834959610080460218410903 56752439415120690327616355)
            ·
              refine ⟨85128659122681035491424533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56752439415120690327616355 85128659122681035491424533)
              ·
                refine ⟨3990405896375673538660525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85128659122681035491424533 3990405896375673538660525)
                ·
                  refine ⟨1496402211140877576997697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3990405896375673538660525 1496402211140877576997697)
                  ·
                    refine ⟨1122301658355658182748273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1496402211140877576997697 1122301658355658182748273)
                    ·
                      refine ⟨841726243766743637061205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1122301658355658182748273 841726243766743637061205)
                      ·
                        rfl

theorem cell23_1639256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_1639256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639256 prefixEnd_1639256 := by exact prefixLift 1639256
  have htrace : WordTrace (prefixWord ++ tailWord_1639256) baseStart_1639256 baseEnd_1639256 := by
    simpa [prefixWord, tailWord_1639256, baseEnd_1639256] using wordTrace_append hprefix tailTrace_1639256
  have hstable : (prefixWord ++ tailWord_1639256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639256).length < 2 ^ (prefixWord ++ tailWord_1639256).sum := by decide
  have hdescent : baseEnd_1639256 < baseStart_1639256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639266 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_1639266 : Nat := 118140960795 + 1639266 * 2 ^ 59
def prefixEnd_1639266 : Nat := 4983230072969 + 3 ^ 40 * 1639266 * 2
def baseEnd_1639266 : Nat := 280577126191096199312053

theorem tailTrace_1639266 : CollatzResearch.WordTrace tailWord_1639266 prefixEnd_1639266 280577126191096199312053 := by
  unfold tailWord_1639266
  simp only [CollatzResearch.WordTrace]
  refine ⟨14947235719806680297202413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39859295252817814125873101 14947235719806680297202413)
  ·
    refine ⟨5605213394927505111450905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14947235719806680297202413 5605213394927505111450905)
    ·
      refine ⟨4203910046195628833588179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5605213394927505111450905 4203910046195628833588179)
      ·
        refine ⟨6305865069293443250382269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4203910046195628833588179 6305865069293443250382269)
        ·
          refine ⟨2364699400985041218893351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6305865069293443250382269 2364699400985041218893351)
          ·
            refine ⟨3547049101477561828340027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364699400985041218893351 3547049101477561828340027)
            ·
              refine ⟨5320573652216342742510041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3547049101477561828340027 5320573652216342742510041)
              ·
                refine ⟨3990430239162257056882531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5320573652216342742510041 3990430239162257056882531)
                ·
                  refine ⟨5985645358743385585323797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990430239162257056882531 5985645358743385585323797)
                  ·
                    refine ⟨280577126191096199312053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5985645358743385585323797 280577126191096199312053)
                    ·
                      rfl

theorem cell23_1639266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_1639266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639266 prefixEnd_1639266 := by exact prefixLift 1639266
  have htrace : WordTrace (prefixWord ++ tailWord_1639266) baseStart_1639266 baseEnd_1639266 := by
    simpa [prefixWord, tailWord_1639266, baseEnd_1639266] using wordTrace_append hprefix tailTrace_1639266
  have hstable : (prefixWord ++ tailWord_1639266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639266).length < 2 ^ (prefixWord ++ tailWord_1639266).sum := by decide
  have hdescent : baseEnd_1639266 < baseStart_1639266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639306 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_1639306 : Nat := 118140960795 + 1639306 * 2 ^ 59
def prefixEnd_1639306 : Nat := 4983230072969 + 3 ^ 40 * 1639306 * 2
def baseEnd_1639306 : Nat := 841751917799468441435975

theorem tailTrace_1639306 : CollatzResearch.WordTrace tailWord_1639306 prefixEnd_1639306 841751917799468441435975 := by
  unfold tailWord_1639306
  simp only [CollatzResearch.WordTrace]
  refine ⟨14947600449770452005066443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39860267866054538680177181 14947600449770452005066443)
  ·
    refine ⟨22421400674655678007599665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14947600449770452005066443 22421400674655678007599665)
    ·
      refine ⟨16816050505991758505699749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22421400674655678007599665 16816050505991758505699749)
      ·
        refine ⟨3153009469873454719818703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16816050505991758505699749 3153009469873454719818703)
        ·
          refine ⟨4729514204810182079728055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3153009469873454719818703 4729514204810182079728055)
          ·
            refine ⟨7094271307215273119592083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4729514204810182079728055 7094271307215273119592083)
            ·
              refine ⟨10641406960822909679388125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7094271307215273119592083 10641406960822909679388125)
              ·
                refine ⟨3990527610308591129770547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10641406960822909679388125 3990527610308591129770547)
                ·
                  refine ⟨5985791415462886694655821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990527610308591129770547 5985791415462886694655821)
                  ·
                    refine ⟨2244671780798582510495933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5985791415462886694655821 2244671780798582510495933)
                    ·
                      refine ⟨841751917799468441435975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2244671780798582510495933 841751917799468441435975)
                      ·
                        rfl

theorem cell23_1639306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_1639306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639306 prefixEnd_1639306 := by exact prefixLift 1639306
  have htrace : WordTrace (prefixWord ++ tailWord_1639306) baseStart_1639306 baseEnd_1639306 := by
    simpa [prefixWord, tailWord_1639306, baseEnd_1639306] using wordTrace_append hprefix tailTrace_1639306
  have hstable : (prefixWord ++ tailWord_1639306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639306).length < 2 ^ (prefixWord ++ tailWord_1639306).sum := by decide
  have hdescent : baseEnd_1639306 < baseStart_1639306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639312 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 4]
def baseStart_1639312 : Nat := 118140960795 + 1639312 * 2 ^ 59
def prefixEnd_1639312 : Nat := 4983230072969 + 3 ^ 40 * 1639312 * 2
def baseEnd_1639312 : Nat := 841754998683395417960947

theorem tailTrace_1639312 : CollatzResearch.WordTrace tailWord_1639312 prefixEnd_1639312 841754998683395417960947 := by
  unfold tailWord_1639312
  simp only [CollatzResearch.WordTrace]
  refine ⟨29895310318530035522492095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39860413758040047363322793 29895310318530035522492095)
  ·
    refine ⟨44842965477795053283738143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29895310318530035522492095 44842965477795053283738143)
    ·
      refine ⟨67264448216692579925607215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44842965477795053283738143 67264448216692579925607215)
      ·
        refine ⟨100896672325038869888410823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67264448216692579925607215 100896672325038869888410823)
        ·
          refine ⟨151345008487558304832616235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100896672325038869888410823 151345008487558304832616235)
          ·
            refine ⟨227017512731337457248924353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151345008487558304832616235 227017512731337457248924353)
            ·
              refine ⟨170263134548503092936693265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227017512731337457248924353 170263134548503092936693265)
              ·
                refine ⟨127697350911377319702519949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170263134548503092936693265 127697350911377319702519949)
                ·
                  refine ⟨47886506591766494888444981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127697350911377319702519949 47886506591766494888444981)
                  ·
                    refine ⟨4489359992978108895791717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47886506591766494888444981 4489359992978108895791717)
                    ·
                      refine ⟨841754998683395417960947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4489359992978108895791717 841754998683395417960947)
                      ·
                        rfl

theorem cell23_1639312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_1639312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639312 prefixEnd_1639312 := by exact prefixLift 1639312
  have htrace : WordTrace (prefixWord ++ tailWord_1639312) baseStart_1639312 baseEnd_1639312 := by
    simpa [prefixWord, tailWord_1639312, baseEnd_1639312] using wordTrace_append hprefix tailTrace_1639312
  have hstable : (prefixWord ++ tailWord_1639312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639312).length < 2 ^ (prefixWord ++ tailWord_1639312).sum := by decide
  have hdescent : baseEnd_1639312 < baseStart_1639312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639409 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_1639409 : Nat := 118140960795 + 1639409 * 2 ^ 59
def prefixEnd_1639409 : Nat := 4983230072969 + 3 ^ 40 * 1639409 * 2
def baseEnd_1639409 : Nat := 841804806306881538448001

theorem tailTrace_1639409 : CollatzResearch.WordTrace tailWord_1639409 prefixEnd_1639409 841804806306881538448001 := by
  unfold tailWord_1639409
  simp only [CollatzResearch.WordTrace]
  refine ⟨59794158517708656611265281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39862772345139104407510187 59794158517708656611265281)
  ·
    refine ⟨44845618888281492458448961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59794158517708656611265281 44845618888281492458448961)
    ·
      refine ⟨33634214166211119343836721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44845618888281492458448961 33634214166211119343836721)
      ·
        refine ⟨25225660624658339507877541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33634214166211119343836721 25225660624658339507877541)
        ·
          refine ⟨4729811367123438657727039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25225660624658339507877541 4729811367123438657727039)
          ·
            refine ⟨7094717050685157986590559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4729811367123438657727039 7094717050685157986590559)
            ·
              refine ⟨10642075576027736979885839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7094717050685157986590559 10642075576027736979885839)
              ·
                refine ⟨15963113364041605469828759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10642075576027736979885839 15963113364041605469828759)
                ·
                  refine ⟨23944670046062408204743139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15963113364041605469828759 23944670046062408204743139)
                  ·
                    refine ⟨35917005069093612307114709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23944670046062408204743139 35917005069093612307114709)
                    ·
                      refine ⟨841804806306881538448001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35917005069093612307114709 841804806306881538448001)
                      ·
                        rfl

theorem cell23_1639409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_1639409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639409 prefixEnd_1639409 := by exact prefixLift 1639409
  have htrace : WordTrace (prefixWord ++ tailWord_1639409) baseStart_1639409 baseEnd_1639409 := by
    simpa [prefixWord, tailWord_1639409, baseEnd_1639409] using wordTrace_append hprefix tailTrace_1639409
  have hstable : (prefixWord ++ tailWord_1639409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639409).length < 2 ^ (prefixWord ++ tailWord_1639409).sum := by decide
  have hdescent : baseEnd_1639409 < baseStart_1639409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639414 : List Nat := [5, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_1639414 : Nat := 118140960795 + 1639414 * 2 ^ 59
def prefixEnd_1639414 : Nat := 4983230072969 + 3 ^ 40 * 1639414 * 2
def baseEnd_1639414 : Nat := 841807373710154018885479

theorem tailTrace_1639414 : CollatzResearch.WordTrace tailWord_1639414 prefixEnd_1639414 841807373710154018885479 := by
  unfold tailWord_1639414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3737146305168158904074831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39862893921793694976798197 3737146305168158904074831)
  ·
    refine ⟨5605719457752238356112247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3737146305168158904074831 5605719457752238356112247)
    ·
      refine ⟨8408579186628357534168371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5605719457752238356112247 8408579186628357534168371)
      ·
        refine ⟨12612868779942536301252557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8408579186628357534168371 12612868779942536301252557)
        ·
          refine ⟨4729825792478451112969709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12612868779942536301252557 4729825792478451112969709)
          ·
            refine ⟨1773684672179419167363641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4729825792478451112969709 1773684672179419167363641)
            ·
              refine ⟨1330263504134564375522731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1773684672179419167363641 1330263504134564375522731)
              ·
                refine ⟨1995395256201846563284097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330263504134564375522731 1995395256201846563284097)
                ·
                  refine ⟨1496546442151384922463073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1995395256201846563284097 1496546442151384922463073)
                  ·
                    refine ⟨1122409831613538691847305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1496546442151384922463073 1122409831613538691847305)
                    ·
                      refine ⟨841807373710154018885479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1122409831613538691847305 841807373710154018885479)
                      ·
                        rfl

theorem cell23_1639414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_1639414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639414 prefixEnd_1639414 := by exact prefixLift 1639414
  have htrace : WordTrace (prefixWord ++ tailWord_1639414) baseStart_1639414 baseEnd_1639414 := by
    simpa [prefixWord, tailWord_1639414, baseEnd_1639414] using wordTrace_append hprefix tailTrace_1639414
  have hstable : (prefixWord ++ tailWord_1639414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639414).length < 2 ^ (prefixWord ++ tailWord_1639414).sum := by decide
  have hdescent : baseEnd_1639414 < baseStart_1639414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639419 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 4]
def baseStart_1639419 : Nat := 118140960795 + 1639419 * 2 ^ 59
def prefixEnd_1639419 : Nat := 4983230072969 + 3 ^ 40 * 1639419 * 2
def baseEnd_1639419 : Nat := 841809941113426499322955

theorem tailTrace_1639419 : CollatzResearch.WordTrace tailWord_1639419 prefixEnd_1639419 841809941113426499322955 := by
  unfold tailWord_1639419
  simp only [CollatzResearch.WordTrace]
  refine ⟨59794523247672428319129311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39863015498448285546086207 59794523247672428319129311)
  ·
    refine ⟨89691784871508642478693967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59794523247672428319129311 89691784871508642478693967)
    ·
      refine ⟨134537677307262963718040951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89691784871508642478693967 134537677307262963718040951)
      ·
        refine ⟨201806515960894445577061427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134537677307262963718040951 201806515960894445577061427)
        ·
          refine ⟨302709773941341668365592141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201806515960894445577061427 302709773941341668365592141)
          ·
            refine ⟨113516165228003125637097053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302709773941341668365592141 113516165228003125637097053)
            ·
              refine ⟨42568561960501172113911395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113516165228003125637097053 42568561960501172113911395)
              ·
                refine ⟨63852842940751758170867093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42568561960501172113911395 63852842940751758170867093)
                ·
                  refine ⟨2993102012847738664259395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63852842940751758170867093 2993102012847738664259395)
                  ·
                    refine ⟨4489653019271607996389093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2993102012847738664259395 4489653019271607996389093)
                    ·
                      refine ⟨841809941113426499322955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4489653019271607996389093 841809941113426499322955)
                      ·
                        rfl

theorem cell23_1639419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 4].length) (baseStart_1639419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639419 prefixEnd_1639419 := by exact prefixLift 1639419
  have htrace : WordTrace (prefixWord ++ tailWord_1639419) baseStart_1639419 baseEnd_1639419 := by
    simpa [prefixWord, tailWord_1639419, baseEnd_1639419] using wordTrace_append hprefix tailTrace_1639419
  have hstable : (prefixWord ++ tailWord_1639419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639419).length < 2 ^ (prefixWord ++ tailWord_1639419).sum := by decide
  have hdescent : baseEnd_1639419 < baseStart_1639419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639436 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 2, 1, 4]
def baseStart_1639436 : Nat := 118140960795 + 1639436 * 2 ^ 59
def prefixEnd_1639436 : Nat := 4983230072969 + 3 ^ 40 * 1639436 * 2
def baseEnd_1639436 : Nat := 841818670284552932810377

theorem tailTrace_1639436 : CollatzResearch.WordTrace tailWord_1639436 prefixEnd_1639436 841818670284552932810377 := by
  unfold tailWord_1639436
  simp only [CollatzResearch.WordTrace]
  refine ⟨29897571644305420111249081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39863428859073893481665441 29897571644305420111249081)
  ·
    refine ⟨22423178733229065083436811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29897571644305420111249081 22423178733229065083436811)
    ·
      refine ⟨33634768099843597625155217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22423178733229065083436811 33634768099843597625155217)
      ·
        refine ⟨25226076074882698218866413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33634768099843597625155217 25226076074882698218866413)
        ·
          refine ⟨9459778528081011832074905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25226076074882698218866413 9459778528081011832074905)
          ·
            refine ⟨7094833896060758874056179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9459778528081011832074905 7094833896060758874056179)
            ·
              refine ⟨10642250844091138311084269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7094833896060758874056179 10642250844091138311084269)
              ·
                refine ⟨3990844066534176866656601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10642250844091138311084269 3990844066534176866656601)
                ·
                  refine ⟨2993133049900632649992451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3990844066534176866656601 2993133049900632649992451)
                  ·
                    refine ⟨4489699574850948974988677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2993133049900632649992451 4489699574850948974988677)
                    ·
                      refine ⟨841818670284552932810377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4489699574850948974988677 841818670284552932810377)
                      ·
                        rfl

theorem cell23_1639436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_1639436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639436 prefixEnd_1639436 := by exact prefixLift 1639436
  have htrace : WordTrace (prefixWord ++ tailWord_1639436) baseStart_1639436 baseEnd_1639436 := by
    simpa [prefixWord, tailWord_1639436, baseEnd_1639436] using wordTrace_append hprefix tailTrace_1639436
  have hstable : (prefixWord ++ tailWord_1639436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639436).length < 2 ^ (prefixWord ++ tailWord_1639436).sum := by decide
  have hdescent : baseEnd_1639436 < baseStart_1639436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639510 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_1639510 : Nat := 118140960795 + 1639510 * 2 ^ 59
def prefixEnd_1639510 : Nat := 4983230072969 + 3 ^ 40 * 1639510 * 2
def baseEnd_1639510 : Nat := 93539629761442849253893

theorem tailTrace_1639510 : CollatzResearch.WordTrace tailWord_1639510 prefixEnd_1639510 93539629761442849253893 := by
  unfold tailWord_1639510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3737365143146421928793249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39865228193561833907127989 3737365143146421928793249)
  ·
    refine ⟨2803023857359816446594937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3737365143146421928793249 2803023857359816446594937)
    ·
      refine ⟨2102267893019862334946203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2803023857359816446594937 2102267893019862334946203)
      ·
        refine ⟨3153401839529793502419305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102267893019862334946203 3153401839529793502419305)
        ·
          refine ⟨2365051379647345126814479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3153401839529793502419305 2365051379647345126814479)
          ·
            refine ⟨3547577069471017690221719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2365051379647345126814479 3547577069471017690221719)
            ·
              refine ⟨5321365604206526535332579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3547577069471017690221719 5321365604206526535332579)
              ·
                refine ⟨7982048406309789802998869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5321365604206526535332579 7982048406309789802998869)
                ·
                  refine ⟨93539629761442849253893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7982048406309789802998869 93539629761442849253893)
                  ·
                    rfl

theorem cell23_1639510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_1639510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639510 prefixEnd_1639510 := by exact prefixLift 1639510
  have htrace : WordTrace (prefixWord ++ tailWord_1639510) baseStart_1639510 baseEnd_1639510 := by
    simpa [prefixWord, tailWord_1639510, baseEnd_1639510] using wordTrace_append hprefix tailTrace_1639510
  have hstable : (prefixWord ++ tailWord_1639510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639510).length < 2 ^ (prefixWord ++ tailWord_1639510).sum := by decide
  have hdescent : baseEnd_1639510 < baseStart_1639510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639520 : List Nat := [2, 1, 1, 3, 2, 2, 1, 6, 1, 1, 3]
def baseStart_1639520 : Nat := 118140960795 + 1639520 * 2 ^ 59
def prefixEnd_1639520 : Nat := 4983230072969 + 3 ^ 40 * 1639520 * 2
def baseEnd_1639520 : Nat := 841861802659530604159991

theorem tailTrace_1639520 : CollatzResearch.WordTrace tailWord_1639520 prefixEnd_1639520 841861802659530604159991 := by
  unfold tailWord_1639520
  simp only [CollatzResearch.WordTrace]
  refine ⟨29899103510153261284278007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39865471346871015045704009 29899103510153261284278007)
  ·
    refine ⟨44848655265229891926417011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29899103510153261284278007 44848655265229891926417011)
    ·
      refine ⟨67272982897844837889625517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44848655265229891926417011 67272982897844837889625517)
      ·
        refine ⟨25227368586691814208609569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67272982897844837889625517 25227368586691814208609569)
        ·
          refine ⟨18920526440018860656457177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25227368586691814208609569 18920526440018860656457177)
          ·
            refine ⟨14190394830014145492342883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18920526440018860656457177 14190394830014145492342883)
            ·
              refine ⟨21285592245021218238514325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14190394830014145492342883 21285592245021218238514325)
              ·
                refine ⟨997762136485369604930359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21285592245021218238514325 997762136485369604930359)
                ·
                  refine ⟨1496643204728054407395539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997762136485369604930359 1496643204728054407395539)
                  ·
                    refine ⟨2244964807092081611093309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1496643204728054407395539 2244964807092081611093309)
                    ·
                      refine ⟨841861802659530604159991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2244964807092081611093309 841861802659530604159991)
                      ·
                        rfl

theorem cell23_1639520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_1639520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639520 prefixEnd_1639520 := by exact prefixLift 1639520
  have htrace : WordTrace (prefixWord ++ tailWord_1639520) baseStart_1639520 baseEnd_1639520 := by
    simpa [prefixWord, tailWord_1639520, baseEnd_1639520] using wordTrace_append hprefix tailTrace_1639520
  have hstable : (prefixWord ++ tailWord_1639520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639520).length < 2 ^ (prefixWord ++ tailWord_1639520).sum := by decide
  have hdescent : baseEnd_1639520 < baseStart_1639520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639543 : List Nat := [1, 1, 3, 1, 1, 4, 4, 2, 1, 1, 4]
def baseStart_1639543 : Nat := 118140960795 + 1639543 * 2 ^ 59
def prefixEnd_1639543 : Nat := 4983230072969 + 3 ^ 40 * 1639543 * 2
def baseEnd_1639543 : Nat := 841873612714584014172385

theorem tailTrace_1639543 : CollatzResearch.WordTrace tailWord_1639543 prefixEnd_1639543 841873612714584014172385 := by
  unfold tailWord_1639543
  simp only [CollatzResearch.WordTrace]
  refine ⟨59799045899223197496643283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39866030599482131664428855 59799045899223197496643283)
  ·
    refine ⟨89698568848834796244964925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59799045899223197496643283 89698568848834796244964925)
    ·
      refine ⟨33636963318313048591861847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89698568848834796244964925 33636963318313048591861847)
      ·
        refine ⟨50455444977469572887792771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33636963318313048591861847 50455444977469572887792771)
        ·
          refine ⟨75683167466204359331689157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50455444977469572887792771 75683167466204359331689157)
          ·
            refine ⟨14190593899913317374691717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75683167466204359331689157 14190593899913317374691717)
            ·
              refine ⟨2660736356233747007754697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14190593899913317374691717 2660736356233747007754697)
              ·
                refine ⟨1995552267175310255816023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2660736356233747007754697 1995552267175310255816023)
                ·
                  refine ⟨2993328400762965383724035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995552267175310255816023 2993328400762965383724035)
                  ·
                    refine ⟨4489992601144448075586053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2993328400762965383724035 4489992601144448075586053)
                    ·
                      refine ⟨841873612714584014172385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4489992601144448075586053 841873612714584014172385)
                      ·
                        rfl

theorem cell23_1639543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_1639543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639543 prefixEnd_1639543 := by exact prefixLift 1639543
  have htrace : WordTrace (prefixWord ++ tailWord_1639543) baseStart_1639543 baseEnd_1639543 := by
    simpa [prefixWord, tailWord_1639543, baseEnd_1639543] using wordTrace_append hprefix tailTrace_1639543
  have hstable : (prefixWord ++ tailWord_1639543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639543).length < 2 ^ (prefixWord ++ tailWord_1639543).sum := by decide
  have hdescent : baseEnd_1639543 < baseStart_1639543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639553 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 4, 4]
def baseStart_1639553 : Nat := 118140960795 + 1639553 * 2 ^ 59
def prefixEnd_1639553 : Nat := 4983230072969 + 3 ^ 40 * 1639553 * 2
def baseEnd_1639553 : Nat := 280626249173709658349113

theorem tailTrace_1639553 : CollatzResearch.WordTrace tailWord_1639553 prefixEnd_1639553 280626249173709658349113 := by
  unfold tailWord_1639553
  simp only [CollatzResearch.WordTrace]
  refine ⟨59799410629186969204507313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39866273752791312803004875 59799410629186969204507313)
  ·
    refine ⟨44849557971890226903380485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59799410629186969204507313 44849557971890226903380485)
    ·
      refine ⟨8409292119729417544383841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44849557971890226903380485 8409292119729417544383841)
      ·
        refine ⟨6306969089797063158287881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8409292119729417544383841 6306969089797063158287881)
        ·
          refine ⟨4730226817347797368715911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6306969089797063158287881 4730226817347797368715911)
          ·
            refine ⟨7095340226021696053073867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4730226817347797368715911 7095340226021696053073867)
            ·
              refine ⟨10643010339032544079610801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7095340226021696053073867 10643010339032544079610801)
              ·
                refine ⟨7982257754274408059708101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10643010339032544079610801 7982257754274408059708101)
                ·
                  refine ⟨1496673328926451511195269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7982257754274408059708101 1496673328926451511195269)
                  ·
                    refine ⟨280626249173709658349113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1496673328926451511195269 280626249173709658349113)
                    ·
                      rfl

theorem cell23_1639553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_1639553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639553 prefixEnd_1639553 := by exact prefixLift 1639553
  have htrace : WordTrace (prefixWord ++ tailWord_1639553) baseStart_1639553 baseEnd_1639553 := by
    simpa [prefixWord, tailWord_1639553, baseEnd_1639553] using wordTrace_append hprefix tailTrace_1639553
  have hstable : (prefixWord ++ tailWord_1639553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639553).length < 2 ^ (prefixWord ++ tailWord_1639553).sum := by decide
  have hdescent : baseEnd_1639553 < baseStart_1639553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639566 : List Nat := [4, 1, 1, 3, 2, 1, 11]
def baseStart_1639566 : Nat := 118140960795 + 1639566 * 2 ^ 59
def prefixEnd_1639566 : Nat := 4983230072969 + 3 ^ 40 * 1639566 * 2
def baseEnd_1639566 : Nat := 10393647194686881780059

theorem tailTrace_1639566 : CollatzResearch.WordTrace tailWord_1639566 prefixEnd_1639566 10393647194686881780059 := by
  unfold tailWord_1639566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7474985597267484053091319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39866589852093248283153701 7474985597267484053091319)
  ·
    refine ⟨11212478395901226079636979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7474985597267484053091319 11212478395901226079636979)
    ·
      refine ⟨16818717593851839119455469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11212478395901226079636979 16818717593851839119455469)
      ·
        refine ⟨6307019097694439669795801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16818717593851839119455469 6307019097694439669795801)
        ·
          refine ⟨4730264323270829752346851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6307019097694439669795801 4730264323270829752346851)
          ·
            refine ⟨7095396484906244628520277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4730264323270829752346851 7095396484906244628520277)
            ·
              refine ⟨10393647194686881780059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7095396484906244628520277 10393647194686881780059)
              ·
                rfl

theorem cell23_1639566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 11].length) (baseStart_1639566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639566 prefixEnd_1639566 := by exact prefixLift 1639566
  have htrace : WordTrace (prefixWord ++ tailWord_1639566) baseStart_1639566 baseEnd_1639566 := by
    simpa [prefixWord, tailWord_1639566, baseEnd_1639566] using wordTrace_append hprefix tailTrace_1639566
  have hstable : (prefixWord ++ tailWord_1639566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639566).length < 2 ^ (prefixWord ++ tailWord_1639566).sum := by decide
  have hdescent : baseEnd_1639566 < baseStart_1639566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639583 : List Nat := [1, 1, 2, 6, 2, 1, 2, 8]
def baseStart_1639583 : Nat := 118140960795 + 1639583 * 2 ^ 59
def prefixEnd_1639583 : Nat := 4983230072969 + 3 ^ 40 * 1639583 * 2
def baseEnd_1639583 : Nat := 31181264886694957691563

theorem tailTrace_1639583 : CollatzResearch.WordTrace tailWord_1639583 prefixEnd_1639583 31181264886694957691563 := by
  unfold tailWord_1639583
  simp only [CollatzResearch.WordTrace]
  refine ⟨59800504819078284328099403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39867003212718856218732935 59800504819078284328099403)
  ·
    refine ⟨89700757228617426492149105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59800504819078284328099403 89700757228617426492149105)
    ·
      refine ⟨67275567921463069869111829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89700757228617426492149105 67275567921463069869111829)
      ·
        refine ⟨3153542246318581400114617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67275567921463069869111829 3153542246318581400114617)
        ·
          refine ⟨2365156684738936050085963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3153542246318581400114617 2365156684738936050085963)
          ·
            refine ⟨3547735027108404075128945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2365156684738936050085963 3547735027108404075128945)
            ·
              refine ⟨2660801270331303056346709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3547735027108404075128945 2660801270331303056346709)
              ·
                refine ⟨31181264886694957691563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2660801270331303056346709 31181264886694957691563)
                ·
                  rfl

theorem cell23_1639583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 8].length) (baseStart_1639583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639583 prefixEnd_1639583 := by exact prefixLift 1639583
  have htrace : WordTrace (prefixWord ++ tailWord_1639583) baseStart_1639583 baseEnd_1639583 := by
    simpa [prefixWord, tailWord_1639583, baseEnd_1639583] using wordTrace_append hprefix tailTrace_1639583
  have hstable : (prefixWord ++ tailWord_1639583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639583).length < 2 ^ (prefixWord ++ tailWord_1639583).sum := by decide
  have hdescent : baseEnd_1639583 < baseStart_1639583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639622 : List Nat := [6, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_1639622 : Nat := 118140960795 + 1639622 * 2 ^ 59
def prefixEnd_1639622 : Nat := 4983230072969 + 3 ^ 40 * 1639622 * 2
def baseEnd_1639622 : Nat := 841914177686289205084523

theorem tailTrace_1639622 : CollatzResearch.WordTrace tailWord_1639622 prefixEnd_1639622 841914177686289205084523 := by
  unfold tailWord_1639622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1868810227060531062149035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39867951510624662659179413 1868810227060531062149035)
  ·
    refine ⟨2803215340590796593223553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1868810227060531062149035 2803215340590796593223553)
    ·
      refine ⟨2102411505443097444917665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2803215340590796593223553 2102411505443097444917665)
      ·
        refine ⟨1576808629082323083688249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2102411505443097444917665 1576808629082323083688249)
        ·
          refine ⟨1182606471811742312766187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1576808629082323083688249 1182606471811742312766187)
          ·
            refine ⟨1773909707717613469149281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182606471811742312766187 1773909707717613469149281)
            ·
              refine ⟨1330432280788210101861961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1773909707717613469149281 1330432280788210101861961)
              ·
                refine ⟨997824210591157576396471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1330432280788210101861961 997824210591157576396471)
                ·
                  refine ⟨1496736315886736364594707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997824210591157576396471 1496736315886736364594707)
                  ·
                    refine ⟨2245104473830104546892061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1496736315886736364594707 2245104473830104546892061)
                    ·
                      refine ⟨841914177686289205084523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2245104473830104546892061 841914177686289205084523)
                      ·
                        rfl

theorem cell23_1639622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_1639622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639622 prefixEnd_1639622 := by exact prefixLift 1639622
  have htrace : WordTrace (prefixWord ++ tailWord_1639622) baseStart_1639622 baseEnd_1639622 := by
    simpa [prefixWord, tailWord_1639622, baseEnd_1639622] using wordTrace_append hprefix tailTrace_1639622
  have hstable : (prefixWord ++ tailWord_1639622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639622).length < 2 ^ (prefixWord ++ tailWord_1639622).sum := by decide
  have hdescent : baseEnd_1639622 < baseStart_1639622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639633 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 5, 4, 2]
def baseStart_1639633 : Nat := 118140960795 + 1639633 * 2 ^ 59
def prefixEnd_1639633 : Nat := 4983230072969 + 3 ^ 40 * 1639633 * 2
def baseEnd_1639633 : Nat := 841919825973488662046971

theorem tailTrace_1639633 : CollatzResearch.WordTrace tailWord_1639633 prefixEnd_1639633 841919825973488662046971 := by
  unfold tailWord_1639633
  simp only [CollatzResearch.WordTrace]
  refine ⟨59802328468897142867419553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39868218979264761911613035 59802328468897142867419553)
  ·
    refine ⟨44851746351672857150564665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59802328468897142867419553 44851746351672857150564665)
    ·
      refine ⟨33638809763754642862923499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44851746351672857150564665 33638809763754642862923499)
      ·
        refine ⟨50458214645631964294385249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33638809763754642862923499 50458214645631964294385249)
        ·
          refine ⟨37843660984223973220788937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50458214645631964294385249 37843660984223973220788937)
          ·
            refine ⟨28382745738167979915591703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37843660984223973220788937 28382745738167979915591703)
            ·
              refine ⟨42574118607251969873387555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28382745738167979915591703 42574118607251969873387555)
              ·
                refine ⟨63861177910877954810081333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42574118607251969873387555 63861177910877954810081333)
                ·
                  refine ⟨5986985429144808263445125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63861177910877954810081333 5986985429144808263445125)
                  ·
                    refine ⟨1122559767964651549395961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5986985429144808263445125 1122559767964651549395961)
                    ·
                      refine ⟨841919825973488662046971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1122559767964651549395961 841919825973488662046971)
                      ·
                        rfl

theorem cell23_1639633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 4, 2].length) (baseStart_1639633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639633 prefixEnd_1639633 := by exact prefixLift 1639633
  have htrace : WordTrace (prefixWord ++ tailWord_1639633) baseStart_1639633 baseEnd_1639633 := by
    simpa [prefixWord, tailWord_1639633, baseEnd_1639633] using wordTrace_append hprefix tailTrace_1639633
  have hstable : (prefixWord ++ tailWord_1639633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639633).length < 2 ^ (prefixWord ++ tailWord_1639633).sum := by decide
  have hdescent : baseEnd_1639633 < baseStart_1639633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639683 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 3]
def baseStart_1639683 : Nat := 118140960795 + 1639683 * 2 ^ 59
def prefixEnd_1639683 : Nat := 4983230072969 + 3 ^ 40 * 1639683 * 2
def baseEnd_1639683 : Nat := 841945500006213466421741

theorem tailTrace_1639683 : CollatzResearch.WordTrace tailWord_1639683 prefixEnd_1639683 841945500006213466421741 := by
  unfold tailWord_1639683
  simp only [CollatzResearch.WordTrace]
  refine ⟨59804152118716001406739703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39869434745810667604493135 59804152118716001406739703)
  ·
    refine ⟨89706228178074002110109555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59804152118716001406739703 89706228178074002110109555)
    ·
      refine ⟨134559342267111003165164333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89706228178074002110109555 134559342267111003165164333)
      ·
        refine ⟨50459753350166626186936625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134559342267111003165164333 50459753350166626186936625)
        ·
          refine ⟨37844815012624969640202469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50459753350166626186936625 37844815012624969640202469)
          ·
            refine ⟨7095902814867181807537963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37844815012624969640202469 7095902814867181807537963)
            ·
              refine ⟨10643854222300772711306945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7095902814867181807537963 10643854222300772711306945)
              ·
                refine ⟨7982890666725579533480209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10643854222300772711306945 7982890666725579533480209)
                ·
                  refine ⟨5987168000044184650110157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7982890666725579533480209 5987168000044184650110157)
                  ·
                    refine ⟨2245188000016569243791309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5987168000044184650110157 2245188000016569243791309)
                    ·
                      refine ⟨841945500006213466421741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2245188000016569243791309 841945500006213466421741)
                      ·
                        rfl

theorem cell23_1639683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_1639683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639683 prefixEnd_1639683 := by exact prefixLift 1639683
  have htrace : WordTrace (prefixWord ++ tailWord_1639683) baseStart_1639683 baseEnd_1639683 := by
    simpa [prefixWord, tailWord_1639683, baseEnd_1639683] using wordTrace_append hprefix tailTrace_1639683
  have hstable : (prefixWord ++ tailWord_1639683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639683).length < 2 ^ (prefixWord ++ tailWord_1639683).sum := by decide
  have hdescent : baseEnd_1639683 < baseStart_1639683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639684 : List Nat := [2, 3, 2, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_1639684 : Nat := 118140960795 + 1639684 * 2 ^ 59
def prefixEnd_1639684 : Nat := 4983230072969 + 3 ^ 40 * 1639684 * 2
def baseEnd_1639684 : Nat := 841946013486867962509237

theorem tailTrace_1639684 : CollatzResearch.WordTrace tailWord_1639684 prefixEnd_1639684 841946013486867962509237 := by
  unfold tailWord_1639684
  simp only [CollatzResearch.WordTrace]
  refine ⟨29902094295856189288763053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39869459061141585718350737 29902094295856189288763053)
  ·
    refine ⟨11213285360946070983286145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29902094295856189288763053 11213285360946070983286145)
    ·
      refine ⟨8409964020709553237464609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11213285360946070983286145 8409964020709553237464609)
      ·
        refine ⟨6307473015532164928098457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8409964020709553237464609 6307473015532164928098457)
        ·
          refine ⟨4730604761649123696073843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6307473015532164928098457 4730604761649123696073843)
          ·
            refine ⟨7095907142473685544110765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4730604761649123696073843 7095907142473685544110765)
            ·
              refine ⟨2660965178427632079041537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7095907142473685544110765 2660965178427632079041537)
              ·
                refine ⟨1995723883820724059281153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2660965178427632079041537 1995723883820724059281153)
                ·
                  refine ⟨1496792912865543044460865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1995723883820724059281153 1496792912865543044460865)
                  ·
                    refine ⟨1122594684649157283345649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1496792912865543044460865 1122594684649157283345649)
                    ·
                      refine ⟨841946013486867962509237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1122594684649157283345649 841946013486867962509237)
                      ·
                        rfl

theorem cell23_1639684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_1639684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639684 prefixEnd_1639684 := by exact prefixLift 1639684
  have htrace : WordTrace (prefixWord ++ tailWord_1639684) baseStart_1639684 baseEnd_1639684 := by
    simpa [prefixWord, tailWord_1639684, baseEnd_1639684] using wordTrace_append hprefix tailTrace_1639684
  have hstable : (prefixWord ++ tailWord_1639684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639684).length < 2 ^ (prefixWord ++ tailWord_1639684).sum := by decide
  have hdescent : baseEnd_1639684 < baseStart_1639684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639696 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 5]
def baseStart_1639696 : Nat := 118140960795 + 1639696 * 2 ^ 59
def prefixEnd_1639696 : Nat := 4983230072969 + 3 ^ 40 * 1639696 * 2
def baseEnd_1639696 : Nat := 841952175254721915559181

theorem tailTrace_1639696 : CollatzResearch.WordTrace tailWord_1639696 prefixEnd_1639696 841952175254721915559181 := by
  unfold tailWord_1639696
  simp only [CollatzResearch.WordTrace]
  refine ⟨29902313133834452313481471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39869750845112603084641961 29902313133834452313481471)
  ·
    refine ⟨44853469700751678470222207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29902313133834452313481471 44853469700751678470222207)
    ·
      refine ⟨67280204551127517705333311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44853469700751678470222207 67280204551127517705333311)
      ·
        refine ⟨100920306826691276557999967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67280204551127517705333311 100920306826691276557999967)
        ·
          refine ⟨151380460240036914836999951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100920306826691276557999967 151380460240036914836999951)
          ·
            refine ⟨227070690360055372255499927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151380460240036914836999951 227070690360055372255499927)
            ·
              refine ⟨340606035540083058383249891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227070690360055372255499927 340606035540083058383249891)
              ·
                refine ⟨510909053310124587574874837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340606035540083058383249891 510909053310124587574874837)
                ·
                  refine ⟨11974430936956045021286129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 510909053310124587574874837 11974430936956045021286129)
                  ·
                    refine ⟨8980823202717033765964597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11974430936956045021286129 8980823202717033765964597)
                    ·
                      refine ⟨841952175254721915559181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8980823202717033765964597 841952175254721915559181)
                      ·
                        rfl

theorem cell23_1639696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_1639696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639696 prefixEnd_1639696 := by exact prefixLift 1639696
  have htrace : WordTrace (prefixWord ++ tailWord_1639696) baseStart_1639696 baseEnd_1639696 := by
    simpa [prefixWord, tailWord_1639696, baseEnd_1639696] using wordTrace_append hprefix tailTrace_1639696
  have hstable : (prefixWord ++ tailWord_1639696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639696).length < 2 ^ (prefixWord ++ tailWord_1639696).sum := by decide
  have hdescent : baseEnd_1639696 < baseStart_1639696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639740 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_1639740 : Nat := 118140960795 + 1639740 * 2 ^ 59
def prefixEnd_1639740 : Nat := 4983230072969 + 3 ^ 40 * 1639740 * 2
def baseEnd_1639740 : Nat := 841974768403519743408979

theorem tailTrace_1639740 : CollatzResearch.WordTrace tailWord_1639740 prefixEnd_1639740 841974768403519743408979 := by
  unfold tailWord_1639740
  simp only [CollatzResearch.WordTrace]
  refine ⟨29903115539754750070782337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39870820719673000094376449 29903115539754750070782337)
  ·
    refine ⟨22427336654816062553086753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29903115539754750070782337 22427336654816062553086753)
    ·
      refine ⟨16820502491112046914815065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22427336654816062553086753 16820502491112046914815065)
      ·
        refine ⟨12615376868334035186111299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16820502491112046914815065 12615376868334035186111299)
        ·
          refine ⟨18923065302501052779166949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12615376868334035186111299 18923065302501052779166949)
          ·
            refine ⟨3548074744218947396093803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18923065302501052779166949 3548074744218947396093803)
            ·
              refine ⟨5322112116328421094140705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3548074744218947396093803 5322112116328421094140705)
              ·
                refine ⟨3991584087246315820605529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5322112116328421094140705 3991584087246315820605529)
                ·
                  refine ⟨2993688065434736865454147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3991584087246315820605529 2993688065434736865454147)
                  ·
                    refine ⟨4490532098152105298181221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2993688065434736865454147 4490532098152105298181221)
                    ·
                      refine ⟨841974768403519743408979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4490532098152105298181221 841974768403519743408979)
                      ·
                        rfl

theorem cell23_1639740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_1639740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639740 prefixEnd_1639740 := by exact prefixLift 1639740
  have htrace : WordTrace (prefixWord ++ tailWord_1639740) baseStart_1639740 baseEnd_1639740 := by
    simpa [prefixWord, tailWord_1639740, baseEnd_1639740] using wordTrace_append hprefix tailTrace_1639740
  have hstable : (prefixWord ++ tailWord_1639740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639740).length < 2 ^ (prefixWord ++ tailWord_1639740).sum := by decide
  have hdescent : baseEnd_1639740 < baseStart_1639740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639763 : List Nat := [1, 1, 1, 2, 1, 1, 7, 3, 6]
def baseStart_1639763 : Nat := 118140960795 + 1639763 * 2 ^ 59
def prefixEnd_1639763 : Nat := 4983230072969 + 3 ^ 40 * 1639763 * 2
def baseEnd_1639763 : Nat := 93554064273174794824597

theorem tailTrace_1639763 : CollatzResearch.WordTrace tailWord_1639763 prefixEnd_1639763 93554064273174794824597 := by
  unfold tailWord_1639763
  simp only [CollatzResearch.WordTrace]
  refine ⟨59807069958426175069651943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39871379972284116713101295 59807069958426175069651943)
  ·
    refine ⟨89710604937639262604477915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59807069958426175069651943 89710604937639262604477915)
    ·
      refine ⟨134565907406458893906716873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89710604937639262604477915 134565907406458893906716873)
      ·
        refine ⟨100924430554844170430037655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134565907406458893906716873 100924430554844170430037655)
        ·
          refine ⟨151386645832266255645056483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100924430554844170430037655 151386645832266255645056483)
          ·
            refine ⟨227079968748399383467584725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151386645832266255645056483 227079968748399383467584725)
            ·
              refine ⟨5322186767540610550021517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 227079968748399383467584725 5322186767540610550021517)
              ·
                refine ⟨1995820037827728956258069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5322186767540610550021517 1995820037827728956258069)
                ·
                  refine ⟨93554064273174794824597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1995820037827728956258069 93554064273174794824597)
                  ·
                    rfl

theorem cell23_1639763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 6].length) (baseStart_1639763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639763 prefixEnd_1639763 := by exact prefixLift 1639763
  have htrace : WordTrace (prefixWord ++ tailWord_1639763) baseStart_1639763 baseEnd_1639763 := by
    simpa [prefixWord, tailWord_1639763, baseEnd_1639763] using wordTrace_append hprefix tailTrace_1639763
  have hstable : (prefixWord ++ tailWord_1639763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639763).length < 2 ^ (prefixWord ++ tailWord_1639763).sum := by decide
  have hdescent : baseEnd_1639763 < baseStart_1639763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639797 : List Nat := [1, 3, 4, 1, 3, 1, 2, 2, 6]
def baseStart_1639797 : Nat := 118140960795 + 1639797 * 2 ^ 59
def prefixEnd_1639797 : Nat := 4983230072969 + 3 ^ 40 * 1639797 * 2
def baseEnd_1639797 : Nat := 93556004088980668932913

theorem tailTrace_1639797 : CollatzResearch.WordTrace tailWord_1639797 prefixEnd_1639797 93556004088980668932913 := by
  unfold tailWord_1639797
  simp only [CollatzResearch.WordTrace]
  refine ⟨59808310040302998876389645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39872206693535332584259763 59808310040302998876389645)
  ·
    refine ⟨22428116265113624578646117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59808310040302998876389645 22428116265113624578646117)
    ·
      refine ⟨4205271799708804608496147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22428116265113624578646117 4205271799708804608496147)
      ·
        refine ⟨6307907699563206912744221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4205271799708804608496147 6307907699563206912744221)
        ·
          refine ⟨2365465387336202592279083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6307907699563206912744221 2365465387336202592279083)
          ·
            refine ⟨3548198081004303888418625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2365465387336202592279083 3548198081004303888418625)
            ·
              refine ⟨2661148560753227916313969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3548198081004303888418625 2661148560753227916313969)
              ·
                refine ⟨1995861420564920937235477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2661148560753227916313969 1995861420564920937235477)
                ·
                  refine ⟨93556004088980668932913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1995861420564920937235477 93556004088980668932913)
                  ·
                    rfl

theorem cell23_1639797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 6].length) (baseStart_1639797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639797 prefixEnd_1639797 := by exact prefixLift 1639797
  have htrace : WordTrace (prefixWord ++ tailWord_1639797) baseStart_1639797 baseEnd_1639797 := by
    simpa [prefixWord, tailWord_1639797, baseEnd_1639797] using wordTrace_append hprefix tailTrace_1639797
  have hstable : (prefixWord ++ tailWord_1639797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639797).length < 2 ^ (prefixWord ++ tailWord_1639797).sum := by decide
  have hdescent : baseEnd_1639797 < baseStart_1639797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639840 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 4, 4]
def baseStart_1639840 : Nat := 118140960795 + 1639840 * 2 ^ 59
def prefixEnd_1639840 : Nat := 4983230072969 + 3 ^ 40 * 1639840 * 2
def baseEnd_1639840 : Nat := 280675372156323117386173

theorem tailTrace_1639840 : CollatzResearch.WordTrace tailWord_1639840 prefixEnd_1639840 280675372156323117386173 := by
  unfold tailWord_1639840
  simp only [CollatzResearch.WordTrace]
  refine ⟨29904939189573608610102487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39873252252764811480136649 29904939189573608610102487)
  ·
    refine ⟨44857408784360412915153731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29904939189573608610102487 44857408784360412915153731)
    ·
      refine ⟨67286113176540619372730597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44857408784360412915153731 67286113176540619372730597)
      ·
        refine ⟨12616146220601366132386987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67286113176540619372730597 12616146220601366132386987)
        ·
          refine ⟨18924219330902049198580481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12616146220601366132386987 18924219330902049198580481)
          ·
            refine ⟨14193164498176536898935361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18924219330902049198580481 14193164498176536898935361)
            ·
              refine ⟨10644873373632402674201521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14193164498176536898935361 10644873373632402674201521)
              ·
                refine ⟨7983655030224302005651141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10644873373632402674201521 7983655030224302005651141)
                ·
                  refine ⟨1496935318167056626059589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7983655030224302005651141 1496935318167056626059589)
                  ·
                    refine ⟨280675372156323117386173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1496935318167056626059589 280675372156323117386173)
                    ·
                      rfl

theorem cell23_1639840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 4, 4].length) (baseStart_1639840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639840 prefixEnd_1639840 := by exact prefixLift 1639840
  have htrace : WordTrace (prefixWord ++ tailWord_1639840) baseStart_1639840 baseEnd_1639840 := by
    simpa [prefixWord, tailWord_1639840, baseEnd_1639840] using wordTrace_append hprefix tailTrace_1639840
  have hstable : (prefixWord ++ tailWord_1639840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639840).length < 2 ^ (prefixWord ++ tailWord_1639840).sum := by decide
  have hdescent : baseEnd_1639840 < baseStart_1639840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639847 : List Nat := [1, 1, 6, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_1639847 : Nat := 118140960795 + 1639847 * 2 ^ 59
def prefixEnd_1639847 : Nat := 4983230072969 + 3 ^ 40 * 1639847 * 2
def baseEnd_1639847 : Nat := 842029710833550824770987

theorem tailTrace_1639847 : CollatzResearch.WordTrace tailWord_1639847 prefixEnd_1639847 842029710833550824770987 := by
  unfold tailWord_1639847
  simp only [CollatzResearch.WordTrace]
  refine ⟨59810133690121857415709795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39873422460081238277139863 59810133690121857415709795)
  ·
    refine ⟨89715200535182786123564693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59810133690121857415709795 89715200535182786123564693)
    ·
      refine ⟨4205400025086693099542095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89715200535182786123564693 4205400025086693099542095)
      ·
        refine ⟨6308100037630039649313143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4205400025086693099542095 6308100037630039649313143)
        ·
          refine ⟨9462150056445059473969715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6308100037630039649313143 9462150056445059473969715)
          ·
            refine ⟨14193225084667589210954573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9462150056445059473969715 14193225084667589210954573)
            ·
              refine ⟨5322459406750345954107965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14193225084667589210954573 5322459406750345954107965)
              ·
                refine ⟨1995922277531379732790487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5322459406750345954107965 1995922277531379732790487)
                ·
                  refine ⟨2993883416297069599185731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995922277531379732790487 2993883416297069599185731)
                  ·
                    refine ⟨4490825124445604398778597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2993883416297069599185731 4490825124445604398778597)
                    ·
                      refine ⟨842029710833550824770987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4490825124445604398778597 842029710833550824770987)
                      ·
                        rfl

theorem cell23_1639847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_1639847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639847 prefixEnd_1639847 := by exact prefixLift 1639847
  have htrace : WordTrace (prefixWord ++ tailWord_1639847) baseStart_1639847 baseEnd_1639847 := by
    simpa [prefixWord, tailWord_1639847, baseEnd_1639847] using wordTrace_append hprefix tailTrace_1639847
  have hstable : (prefixWord ++ tailWord_1639847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639847).length < 2 ^ (prefixWord ++ tailWord_1639847).sum := by decide
  have hdescent : baseEnd_1639847 < baseStart_1639847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639883 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 2, 7]
def baseStart_1639883 : Nat := 118140960795 + 1639883 * 2 ^ 59
def prefixEnd_1639883 : Nat := 4983230072969 + 3 ^ 40 * 1639883 * 2
def baseEnd_1639883 : Nat := 280682732045704227973607

theorem tailTrace_1639883 : CollatzResearch.WordTrace tailWord_1639883 prefixEnd_1639883 280682732045704227973607 := by
  unfold tailWord_1639883
  simp only [CollatzResearch.WordTrace]
  refine ⟨59811446717991435564020303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39874297811994290376013535 59811446717991435564020303)
  ·
    refine ⟨89717170076987153346030455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59811446717991435564020303 89717170076987153346030455)
    ·
      refine ⟨134575755115480730019045683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89717170076987153346030455 134575755115480730019045683)
      ·
        refine ⟨201863632673221095028568525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134575755115480730019045683 201863632673221095028568525)
        ·
          refine ⟨75698862252457910635713197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201863632673221095028568525 75698862252457910635713197)
          ·
            refine ⟨28387073344671716488392449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75698862252457910635713197 28387073344671716488392449)
            ·
              refine ⟨21290305008503787366294337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28387073344671716488392449 21290305008503787366294337)
              ·
                refine ⟨15967728756377840524720753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21290305008503787366294337 15967728756377840524720753)
                ·
                  refine ⟨11975796567283380393540565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15967728756377840524720753 11975796567283380393540565)
                  ·
                    refine ⟨280682732045704227973607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11975796567283380393540565 280682732045704227973607)
                    ·
                      rfl

theorem cell23_1639883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 7].length) (baseStart_1639883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639883 prefixEnd_1639883 := by exact prefixLift 1639883
  have htrace : WordTrace (prefixWord ++ tailWord_1639883) baseStart_1639883 baseEnd_1639883 := by
    simpa [prefixWord, tailWord_1639883, baseEnd_1639883] using wordTrace_append hprefix tailTrace_1639883
  have hstable : (prefixWord ++ tailWord_1639883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639883).length < 2 ^ (prefixWord ++ tailWord_1639883).sum := by decide
  have hdescent : baseEnd_1639883 < baseStart_1639883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639884 : List Nat := [2, 2, 1, 4, 2, 2, 2, 2, 1, 2, 3]
def baseStart_1639884 : Nat := 118140960795 + 1639884 * 2 ^ 59
def prefixEnd_1639884 : Nat := 4983230072969 + 3 ^ 40 * 1639884 * 2
def baseEnd_1639884 : Nat := 842048709617767180008317

theorem tailTrace_1639884 : CollatzResearch.WordTrace tailWord_1639884 prefixEnd_1639884 842048709617767180008317 := by
  unfold tailWord_1639884
  simp only [CollatzResearch.WordTrace]
  refine ⟨29905741595493906367403353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39874322127325208489871137 29905741595493906367403353)
  ·
    refine ⟨22429306196620429775552515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29905741595493906367403353 22429306196620429775552515)
    ·
      refine ⟨33643959294930644663328773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22429306196620429775552515 33643959294930644663328773)
      ·
        refine ⟨6308242367799495874374145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33643959294930644663328773 6308242367799495874374145)
        ·
          refine ⟨4731181775849621905780609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6308242367799495874374145 4731181775849621905780609)
          ·
            refine ⟨3548386331887216429335457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4731181775849621905780609 3548386331887216429335457)
            ·
              refine ⟨2661289748915412322001593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3548386331887216429335457 2661289748915412322001593)
              ·
                refine ⟨1995967311686559241501195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2661289748915412322001593 1995967311686559241501195)
                ·
                  refine ⟨2993950967529838862251793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995967311686559241501195 2993950967529838862251793)
                  ·
                    refine ⟨2245463225647379146688845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2993950967529838862251793 2245463225647379146688845)
                    ·
                      refine ⟨842048709617767180008317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2245463225647379146688845 842048709617767180008317)
                      ·
                        rfl

theorem cell23_1639884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_1639884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639884 prefixEnd_1639884 := by exact prefixLift 1639884
  have htrace : WordTrace (prefixWord ++ tailWord_1639884) baseStart_1639884 baseEnd_1639884 := by
    simpa [prefixWord, tailWord_1639884, baseEnd_1639884] using wordTrace_append hprefix tailTrace_1639884
  have hstable : (prefixWord ++ tailWord_1639884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639884).length < 2 ^ (prefixWord ++ tailWord_1639884).sum := by decide
  have hdescent : baseEnd_1639884 < baseStart_1639884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639897 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 4, 1, 3]
def baseStart_1639897 : Nat := 118140960795 + 1639897 * 2 ^ 59
def prefixEnd_1639897 : Nat := 4983230072969 + 3 ^ 40 * 1639897 * 2
def baseEnd_1639897 : Nat := 842055384866275629145757

theorem tailTrace_1639897 : CollatzResearch.WordTrace tailWord_1639897 prefixEnd_1639897 842055384866275629145757 := by
  unfold tailWord_1639897
  simp only [CollatzResearch.WordTrace]
  refine ⟨59811957339940715955029945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39874638226627143970019963 59811957339940715955029945)
  ·
    refine ⟨44858968004955536966272459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59811957339940715955029945 44858968004955536966272459)
    ·
      refine ⟨67288452007433305449408689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44858968004955536966272459 67288452007433305449408689)
      ·
        refine ⟨50466339005574979087056517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67288452007433305449408689 50466339005574979087056517)
        ·
          refine ⟨9462438563545308578823097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50466339005574979087056517 9462438563545308578823097)
          ·
            refine ⟨7096828922658981434117323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9462438563545308578823097 7096828922658981434117323)
            ·
              refine ⟨10645243383988472151175985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7096828922658981434117323 10645243383988472151175985)
              ·
                refine ⟨7983932537991354113381989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10645243383988472151175985 7983932537991354113381989)
                ·
                  refine ⟨1496987350873378896259123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7983932537991354113381989 1496987350873378896259123)
                  ·
                    refine ⟨2245481026310068344388685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1496987350873378896259123 2245481026310068344388685)
                    ·
                      refine ⟨842055384866275629145757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2245481026310068344388685 842055384866275629145757)
                      ·
                        rfl

theorem cell23_1639897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_1639897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639897 prefixEnd_1639897 := by exact prefixLift 1639897
  have htrace : WordTrace (prefixWord ++ tailWord_1639897) baseStart_1639897 baseEnd_1639897 := by
    simpa [prefixWord, tailWord_1639897, baseEnd_1639897] using wordTrace_append hprefix tailTrace_1639897
  have hstable : (prefixWord ++ tailWord_1639897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639897).length < 2 ^ (prefixWord ++ tailWord_1639897).sum := by decide
  have hdescent : baseEnd_1639897 < baseStart_1639897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639898 : List Nat := [3, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2]
def baseStart_1639898 : Nat := 118140960795 + 1639898 * 2 ^ 59
def prefixEnd_1639898 : Nat := 4983230072969 + 3 ^ 40 * 1639898 * 2
def baseEnd_1639898 : Nat := 842055898346930125233253

theorem tailTrace_1639898 : CollatzResearch.WordTrace tailWord_1639898 prefixEnd_1639898 842055898346930125233253 := by
  unfold tailWord_1639898
  simp only [CollatzResearch.WordTrace]
  refine ⟨14952998453234273281454087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39874662541958062083877565 14952998453234273281454087)
  ·
    refine ⟨22429497679851409922181131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14952998453234273281454087 22429497679851409922181131)
    ·
      refine ⟨33644246519777114883271697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22429497679851409922181131 33644246519777114883271697)
      ·
        refine ⟨25233184889832836162453773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33644246519777114883271697 25233184889832836162453773)
        ·
          refine ⟨9462444333687313560920165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25233184889832836162453773 9462444333687313560920165)
          ·
            refine ⟨1774208312566371292672531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9462444333687313560920165 1774208312566371292672531)
            ·
              refine ⟨2661312468849556939008797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774208312566371292672531 2661312468849556939008797)
              ·
                refine ⟨997992175818583852128299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2661312468849556939008797 997992175818583852128299)
                ·
                  refine ⟨1496988263727875778192449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997992175818583852128299 1496988263727875778192449)
                  ·
                    refine ⟨1122741197795906833644337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1496988263727875778192449 1122741197795906833644337)
                    ·
                      refine ⟨842055898346930125233253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1122741197795906833644337 842055898346930125233253)
                      ·
                        rfl

theorem cell23_1639898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_1639898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639898 prefixEnd_1639898 := by exact prefixLift 1639898
  have htrace : WordTrace (prefixWord ++ tailWord_1639898) baseStart_1639898 baseEnd_1639898 := by
    simpa [prefixWord, tailWord_1639898, baseEnd_1639898] using wordTrace_append hprefix tailTrace_1639898
  have hstable : (prefixWord ++ tailWord_1639898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639898).length < 2 ^ (prefixWord ++ tailWord_1639898).sum := by decide
  have hdescent : baseEnd_1639898 < baseStart_1639898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639966 : List Nat := [4, 3, 3, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_1639966 : Nat := 118140960795 + 1639966 * 2 ^ 59
def prefixEnd_1639966 : Nat := 4983230072969 + 3 ^ 40 * 1639966 * 2
def baseEnd_1639966 : Nat := 842090815031435859182941

theorem tailTrace_1639966 : CollatzResearch.WordTrace tailWord_1639966 prefixEnd_1639966 842090815031435859182941 := by
  unfold tailWord_1639966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7476809247086342592411469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39876315984460493826194501 7476809247086342592411469)
  ·
    refine ⟨2803803467657378472154301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7476809247086342592411469 2803803467657378472154301)
    ·
      refine ⟨1051426300371516927057863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2803803467657378472154301 1051426300371516927057863)
      ·
        refine ⟨1577139450557275390586795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1051426300371516927057863 1577139450557275390586795)
        ·
          refine ⟨2365709175835913085880193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1577139450557275390586795 2365709175835913085880193)
          ·
            refine ⟨1774281881876934814410145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2365709175835913085880193 1774281881876934814410145)
            ·
              refine ⟨1330711411407701110807609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1774281881876934814410145 1330711411407701110807609)
              ·
                refine ⟨998033558555775833105707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1330711411407701110807609 998033558555775833105707)
                ·
                  refine ⟨1497050337833663749658561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998033558555775833105707 1497050337833663749658561)
                  ·
                    refine ⟨1122787753375247812243921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1497050337833663749658561 1122787753375247812243921)
                    ·
                      refine ⟨842090815031435859182941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1122787753375247812243921 842090815031435859182941)
                      ·
                        rfl

theorem cell23_1639966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_1639966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639966 prefixEnd_1639966 := by exact prefixLift 1639966
  have htrace : WordTrace (prefixWord ++ tailWord_1639966) baseStart_1639966 baseEnd_1639966 := by
    simpa [prefixWord, tailWord_1639966, baseEnd_1639966] using wordTrace_append hprefix tailTrace_1639966
  have hstable : (prefixWord ++ tailWord_1639966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639966).length < 2 ^ (prefixWord ++ tailWord_1639966).sum := by decide
  have hdescent : baseEnd_1639966 < baseStart_1639966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639970 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1639970 : Nat := 118140960795 + 1639970 * 2 ^ 59
def prefixEnd_1639970 : Nat := 4983230072969 + 3 ^ 40 * 1639970 * 2
def baseEnd_1639970 : Nat := 842092868954053843532921

theorem tailTrace_1639970 : CollatzResearch.WordTrace tailWord_1639970 prefixEnd_1639970 842092868954053843532921 := by
  unfold tailWord_1639970
  simp only [CollatzResearch.WordTrace]
  refine ⟨14953654967169062355609341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39876413245784166281624909 14953654967169062355609341)
  ·
    refine ⟨5607620612688398383353503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14953654967169062355609341 5607620612688398383353503)
    ·
      refine ⟨8411430919032597575030255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5607620612688398383353503 8411430919032597575030255)
      ·
        refine ⟨12617146378548896362545383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8411430919032597575030255 12617146378548896362545383)
        ·
          refine ⟨18925719567823344543818075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12617146378548896362545383 18925719567823344543818075)
          ·
            refine ⟨28388579351735016815727113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18925719567823344543818075 28388579351735016815727113)
            ·
              refine ⟨21291434513801262611795335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28388579351735016815727113 21291434513801262611795335)
              ·
                refine ⟨31937151770701893917693003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21291434513801262611795335 31937151770701893917693003)
                ·
                  refine ⟨47905727656052840876539505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31937151770701893917693003 47905727656052840876539505)
                  ·
                    refine ⟨35929295742039630657404629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47905727656052840876539505 35929295742039630657404629)
                    ·
                      refine ⟨842092868954053843532921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35929295742039630657404629 842092868954053843532921)
                      ·
                        rfl

theorem cell23_1639970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1639970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639970 prefixEnd_1639970 := by exact prefixLift 1639970
  have htrace : WordTrace (prefixWord ++ tailWord_1639970) baseStart_1639970 baseEnd_1639970 := by
    simpa [prefixWord, tailWord_1639970, baseEnd_1639970] using wordTrace_append hprefix tailTrace_1639970
  have hstable : (prefixWord ++ tailWord_1639970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639970).length < 2 ^ (prefixWord ++ tailWord_1639970).sum := by decide
  have hdescent : baseEnd_1639970 < baseStart_1639970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1639987 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 3]
def baseStart_1639987 : Nat := 118140960795 + 1639987 * 2 ^ 59
def prefixEnd_1639987 : Nat := 4983230072969 + 3 ^ 40 * 1639987 * 2
def baseEnd_1639987 : Nat := 842101598125180277020343

theorem tailTrace_1639987 : CollatzResearch.WordTrace tailWord_1639987 prefixEnd_1639987 842101598125180277020343 := by
  unfold tailWord_1639987
  simp only [CollatzResearch.WordTrace]
  refine ⟨59815239909614661325806215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39876826606409774217204143 59815239909614661325806215)
  ·
    refine ⟨89722859864421991988709323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59815239909614661325806215 89722859864421991988709323)
    ·
      refine ⟨134584289796632987983063985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89722859864421991988709323 134584289796632987983063985)
      ·
        refine ⟨100938217347474740987297989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134584289796632987983063985 100938217347474740987297989)
        ·
          refine ⟨18925915752651513935118373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100938217347474740987297989 18925915752651513935118373)
          ·
            refine ⟨3548609203622158862834695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18925915752651513935118373 3548609203622158862834695)
            ·
              refine ⟨5322913805433238294252043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3548609203622158862834695 5322913805433238294252043)
              ·
                refine ⟨7984370708149857441378065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5322913805433238294252043 7984370708149857441378065)
                ·
                  refine ⟨5988278031112393081033549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7984370708149857441378065 5988278031112393081033549)
                  ·
                    refine ⟨2245604261667147405387581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5988278031112393081033549 2245604261667147405387581)
                    ·
                      refine ⟨842101598125180277020343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2245604261667147405387581 842101598125180277020343)
                      ·
                        rfl

theorem cell23_1639987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 3].length) (baseStart_1639987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1639987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1639987 prefixEnd_1639987 := by exact prefixLift 1639987
  have htrace : WordTrace (prefixWord ++ tailWord_1639987) baseStart_1639987 baseEnd_1639987 := by
    simpa [prefixWord, tailWord_1639987, baseEnd_1639987] using wordTrace_append hprefix tailTrace_1639987
  have hstable : (prefixWord ++ tailWord_1639987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1639987).length < 2 ^ (prefixWord ++ tailWord_1639987).sum := by decide
  have hdescent : baseEnd_1639987 < baseStart_1639987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1639987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640007 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 1, 7]
def baseStart_1640007 : Nat := 118140960795 + 1640007 * 2 ^ 59
def prefixEnd_1640007 : Nat := 4983230072969 + 3 ^ 40 * 1640007 * 2
def baseEnd_1640007 : Nat := 280703955912756732923417

theorem tailTrace_1640007 : CollatzResearch.WordTrace tailWord_1640007 prefixEnd_1640007 280703955912756732923417 := by
  unfold tailWord_1640007
  simp only [CollatzResearch.WordTrace]
  refine ⟨59815969369542204741534275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39877312913028136494356183 59815969369542204741534275)
  ·
    refine ⟨89723954054313307112301413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59815969369542204741534275 89723954054313307112301413)
    ·
      refine ⟨16823241385183745083556515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89723954054313307112301413 16823241385183745083556515)
      ·
        refine ⟨25234862077775617625334773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16823241385183745083556515 25234862077775617625334773)
        ·
          refine ⟨2365768319791464152375135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25234862077775617625334773 2365768319791464152375135)
          ·
            refine ⟨3548652479687196228562703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2365768319791464152375135 3548652479687196228562703)
            ·
              refine ⟨5322978719530794342844055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3548652479687196228562703 5322978719530794342844055)
              ·
                refine ⟨7984468079296191514266083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5322978719530794342844055 7984468079296191514266083)
                ·
                  refine ⟨11976702118944287271399125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7984468079296191514266083 11976702118944287271399125)
                  ·
                    refine ⟨280703955912756732923417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11976702118944287271399125 280703955912756732923417)
                    ·
                      rfl

theorem cell23_1640007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_1640007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640007 prefixEnd_1640007 := by exact prefixLift 1640007
  have htrace : WordTrace (prefixWord ++ tailWord_1640007) baseStart_1640007 baseEnd_1640007 := by
    simpa [prefixWord, tailWord_1640007, baseEnd_1640007] using wordTrace_append hprefix tailTrace_1640007
  have hstable : (prefixWord ++ tailWord_1640007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640007).length < 2 ^ (prefixWord ++ tailWord_1640007).sum := by decide
  have hdescent : baseEnd_1640007 < baseStart_1640007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640071 : List Nat := [1, 1, 4, 2, 1, 3, 3, 3, 1, 4]
def baseStart_1640071 : Nat := 118140960795 + 1640071 * 2 ^ 59
def prefixEnd_1640071 : Nat := 4983230072969 + 3 ^ 40 * 1640071 * 2
def baseEnd_1640071 : Nat := 280714910166719316123319

theorem tailTrace_1640071 : CollatzResearch.WordTrace tailWord_1640071 prefixEnd_1640071 280714910166719316123319 := by
  unfold tailWord_1640071
  simp only [CollatzResearch.WordTrace]
  refine ⟨59818303641310343671864067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39878869094206895781242711 59818303641310343671864067)
  ·
    refine ⟨89727455461965515507796101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59818303641310343671864067 89727455461965515507796101)
    ·
      refine ⟨16823897899118534157711769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89727455461965515507796101 16823897899118534157711769)
      ·
        refine ⟨12617923424338900618283827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16823897899118534157711769 12617923424338900618283827)
        ·
          refine ⟨18926885136508350927425741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12617923424338900618283827 18926885136508350927425741)
          ·
            refine ⟨7097581926190631597784653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18926885136508350927425741 7097581926190631597784653)
            ·
              refine ⟨2661593222321486849169245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7097581926190631597784653 2661593222321486849169245)
              ·
                refine ⟨998097458370557568438467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2661593222321486849169245 998097458370557568438467)
                ·
                  refine ⟨1497146187555836352657701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998097458370557568438467 1497146187555836352657701)
                  ·
                    refine ⟨280714910166719316123319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1497146187555836352657701 280714910166719316123319)
                    ·
                      rfl

theorem cell23_1640071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_1640071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640071 prefixEnd_1640071 := by exact prefixLift 1640071
  have htrace : WordTrace (prefixWord ++ tailWord_1640071) baseStart_1640071 baseEnd_1640071 := by
    simpa [prefixWord, tailWord_1640071, baseEnd_1640071] using wordTrace_append hprefix tailTrace_1640071
  have hstable : (prefixWord ++ tailWord_1640071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640071).length < 2 ^ (prefixWord ++ tailWord_1640071).sum := by decide
  have hdescent : baseEnd_1640071 < baseStart_1640071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640088 : List Nat := [2, 1, 2, 4, 1, 3, 3, 2, 1, 4]
def baseStart_1640088 : Nat := 118140960795 + 1640088 * 2 ^ 59
def prefixEnd_1640088 : Nat := 4983230072969 + 3 ^ 40 * 1640088 * 2
def baseEnd_1640088 : Nat := 280717819890428127285793

theorem tailTrace_1640088 : CollatzResearch.WordTrace tailWord_1640088 prefixEnd_1640088 280717819890428127285793 := by
  unfold tailWord_1640088
  simp only [CollatzResearch.WordTrace]
  refine ⟨29909461841124377787616459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39879282454832503716821945 29909461841124377787616459)
  ·
    refine ⟨44864192761686566681424689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29909461841124377787616459 44864192761686566681424689)
    ·
      refine ⟨33648144571264925011068517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44864192761686566681424689 33648144571264925011068517)
      ·
        refine ⟨6309027107112173439575347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33648144571264925011068517 6309027107112173439575347)
        ·
          refine ⟨9463540660668260159363021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6309027107112173439575347 9463540660668260159363021)
          ·
            refine ⟨3548827747750597559761133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9463540660668260159363021 3548827747750597559761133)
            ·
              refine ⟨1330810405406474084910425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3548827747750597559761133 1330810405406474084910425)
              ·
                refine ⟨998107804054855563682819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1330810405406474084910425 998107804054855563682819)
                ·
                  refine ⟨1497161706082283345524229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998107804054855563682819 1497161706082283345524229)
                  ·
                    refine ⟨280717819890428127285793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1497161706082283345524229 280717819890428127285793)
                    ·
                      rfl

theorem cell23_1640088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_1640088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640088 prefixEnd_1640088 := by exact prefixLift 1640088
  have htrace : WordTrace (prefixWord ++ tailWord_1640088) baseStart_1640088 baseEnd_1640088 := by
    simpa [prefixWord, tailWord_1640088, baseEnd_1640088] using wordTrace_append hprefix tailTrace_1640088
  have hstable : (prefixWord ++ tailWord_1640088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640088).length < 2 ^ (prefixWord ++ tailWord_1640088).sum := by decide
  have hdescent : baseEnd_1640088 < baseStart_1640088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640114 : List Nat := [3, 2, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_1640114 : Nat := 118140960795 + 1640114 * 2 ^ 59
def prefixEnd_1640114 : Nat := 4983230072969 + 3 ^ 40 * 1640114 * 2
def baseEnd_1640114 : Nat := 280722270056100426710753

theorem tailTrace_1640114 : CollatzResearch.WordTrace tailWord_1640114 prefixEnd_1640114 280722270056100426710753 := by
  unfold tailWord_1640114
  simp only [CollatzResearch.WordTrace]
  refine ⟨14954967995038640503919849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39879914653436374677119597 14954967995038640503919849)
  ·
    refine ⟨11216225996278980377939887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14954967995038640503919849 11216225996278980377939887)
    ·
      refine ⟨16824338994418470566909831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11216225996278980377939887 16824338994418470566909831)
      ·
        refine ⟨25236508491627705850364747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16824338994418470566909831 25236508491627705850364747)
        ·
          refine ⟨37854762737441558775547121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25236508491627705850364747 37854762737441558775547121)
          ·
            refine ⟨28391072053081169081660341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37854762737441558775547121 28391072053081169081660341)
            ·
              refine ⟨2661663004976359601405657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28391072053081169081660341 2661663004976359601405657)
              ·
                refine ⟨1996247253732269701054243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2661663004976359601405657 1996247253732269701054243)
                ·
                  refine ⟨2994370880598404551581365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996247253732269701054243 2994370880598404551581365)
                  ·
                    refine ⟨280722270056100426710753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2994370880598404551581365 280722270056100426710753)
                    ·
                      rfl

theorem cell23_1640114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_1640114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640114 prefixEnd_1640114 := by exact prefixLift 1640114
  have htrace : WordTrace (prefixWord ++ tailWord_1640114) baseStart_1640114 baseEnd_1640114 := by
    simpa [prefixWord, tailWord_1640114, baseEnd_1640114] using wordTrace_append hprefix tailTrace_1640114
  have hstable : (prefixWord ++ tailWord_1640114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640114).length < 2 ^ (prefixWord ++ tailWord_1640114).sum := by decide
  have hdescent : baseEnd_1640114 < baseStart_1640114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640127 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 1, 6]
def baseStart_1640127 : Nat := 118140960795 + 1640127 * 2 ^ 59
def prefixEnd_1640127 : Nat := 4983230072969 + 3 ^ 40 * 1640127 * 2
def baseEnd_1640127 : Nat := 280724495138936576423233

theorem tailTrace_1640127 : CollatzResearch.WordTrace tailWord_1640127 prefixEnd_1640127 280724495138936576423233 := by
  unfold tailWord_1640127
  simp only [CollatzResearch.WordTrace]
  refine ⟨59820346129107465235902635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39880230752738310157268423 59820346129107465235902635)
  ·
    refine ⟨89730519193661197853853953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59820346129107465235902635 89730519193661197853853953)
    ·
      refine ⟨67297889395245898390390465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89730519193661197853853953 67297889395245898390390465)
      ·
        refine ⟨50473417046434423792792849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67297889395245898390390465 50473417046434423792792849)
        ·
          refine ⟨37855062784825817844594637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50473417046434423792792849 37855062784825817844594637)
          ·
            refine ⟨14195648544309681691722989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37855062784825817844594637 14195648544309681691722989)
            ·
              refine ⟨5323368204116130634396121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14195648544309681691722989 5323368204116130634396121)
              ·
                refine ⟨3992526153087097975797091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5323368204116130634396121 3992526153087097975797091)
                ·
                  refine ⟨5988789229630646963695637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3992526153087097975797091 5988789229630646963695637)
                  ·
                    refine ⟨280724495138936576423233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5988789229630646963695637 280724495138936576423233)
                    ·
                      rfl

theorem cell23_1640127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 6].length) (baseStart_1640127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640127 prefixEnd_1640127 := by exact prefixLift 1640127
  have htrace : WordTrace (prefixWord ++ tailWord_1640127) baseStart_1640127 baseEnd_1640127 := by
    simpa [prefixWord, tailWord_1640127, baseEnd_1640127] using wordTrace_append hprefix tailTrace_1640127
  have hstable : (prefixWord ++ tailWord_1640127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640127).length < 2 ^ (prefixWord ++ tailWord_1640127).sum := by decide
  have hdescent : baseEnd_1640127 < baseStart_1640127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640145 : List Nat := [1, 2, 2, 1, 2, 6, 2, 2, 1, 1, 3]
def baseStart_1640145 : Nat := 118140960795 + 1640145 * 2 ^ 59
def prefixEnd_1640145 : Nat := 4983230072969 + 3 ^ 40 * 1640145 * 2
def baseEnd_1640145 : Nat := 842182728068590658844617

theorem tailTrace_1640145 : CollatzResearch.WordTrace tailWord_1640145 prefixEnd_1640145 842182728068590658844617 := by
  unfold tailWord_1640145
  simp only [CollatzResearch.WordTrace]
  refine ⟨59821002643042254310057889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39880668428694836206705259 59821002643042254310057889)
  ·
    refine ⟨44865751982281690732543417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59821002643042254310057889 44865751982281690732543417)
    ·
      refine ⟨33649313986711268049407563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44865751982281690732543417 33649313986711268049407563)
      ·
        refine ⟨50473970980066902074111345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33649313986711268049407563 50473970980066902074111345)
        ·
          refine ⟨37855478235050176555583509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50473970980066902074111345 37855478235050176555583509)
          ·
            refine ⟨1774475542267977026042977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37855478235050176555583509 1774475542267977026042977)
            ·
              refine ⟨1330856656700982769532233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1774475542267977026042977 1330856656700982769532233)
              ·
                refine ⟨998142492525737077149175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1330856656700982769532233 998142492525737077149175)
                ·
                  refine ⟨1497213738788605615723763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998142492525737077149175 1497213738788605615723763)
                  ·
                    refine ⟨2245820608182908423585645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1497213738788605615723763 2245820608182908423585645)
                    ·
                      refine ⟨842182728068590658844617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2245820608182908423585645 842182728068590658844617)
                      ·
                        rfl

theorem cell23_1640145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 1, 1, 3].length) (baseStart_1640145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640145 prefixEnd_1640145 := by exact prefixLift 1640145
  have htrace : WordTrace (prefixWord ++ tailWord_1640145) baseStart_1640145 baseEnd_1640145 := by
    simpa [prefixWord, tailWord_1640145, baseEnd_1640145] using wordTrace_append hprefix tailTrace_1640145
  have hstable : (prefixWord ++ tailWord_1640145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640145).length < 2 ^ (prefixWord ++ tailWord_1640145).sum := by decide
  have hdescent : baseEnd_1640145 < baseStart_1640145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640151 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 3, 2, 2]
def baseStart_1640151 : Nat := 118140960795 + 1640151 * 2 ^ 59
def prefixEnd_1640151 : Nat := 4983230072969 + 3 ^ 40 * 1640151 * 2
def baseEnd_1640151 : Nat := 842185808952517635369589

theorem tailTrace_1640151 : CollatzResearch.WordTrace tailWord_1640151 prefixEnd_1640151 842185808952517635369589 := by
  unfold tailWord_1640151
  simp only [CollatzResearch.WordTrace]
  refine ⟨59821221481020517334776307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39880814320680344889850871 59821221481020517334776307)
  ·
    refine ⟨89731832221530776002164461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59821221481020517334776307 89731832221530776002164461)
    ·
      refine ⟨33649437083074041000811673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89731832221530776002164461 33649437083074041000811673)
      ·
        refine ⟨25237077812305530750608755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33649437083074041000811673 25237077812305530750608755)
        ·
          refine ⟨37855616718458296125913133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25237077812305530750608755 37855616718458296125913133)
          ·
            refine ⟨14195856269421861047217425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37855616718458296125913133 14195856269421861047217425)
            ·
              refine ⟨10646892202066395785413069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14195856269421861047217425 10646892202066395785413069)
              ·
                refine ⟨3992584575774898419529901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10646892202066395785413069 3992584575774898419529901)
                ·
                  refine ⟨1497219215915586907323713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3992584575774898419529901 1497219215915586907323713)
                  ·
                    refine ⟨1122914411936690180492785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1497219215915586907323713 1122914411936690180492785)
                    ·
                      refine ⟨842185808952517635369589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1122914411936690180492785 842185808952517635369589)
                      ·
                        rfl

theorem cell23_1640151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_1640151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640151 prefixEnd_1640151 := by exact prefixLift 1640151
  have htrace : WordTrace (prefixWord ++ tailWord_1640151) baseStart_1640151 baseEnd_1640151 := by
    simpa [prefixWord, tailWord_1640151, baseEnd_1640151] using wordTrace_append hprefix tailTrace_1640151
  have hstable : (prefixWord ++ tailWord_1640151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640151).length < 2 ^ (prefixWord ++ tailWord_1640151).sum := by decide
  have hdescent : baseEnd_1640151 < baseStart_1640151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640154 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3]
def baseStart_1640154 : Nat := 118140960795 + 1640154 * 2 ^ 59
def prefixEnd_1640154 : Nat := 4983230072969 + 3 ^ 40 * 1640154 * 2
def baseEnd_1640154 : Nat := 842187349394481123632075

theorem tailTrace_1640154 : CollatzResearch.WordTrace tailWord_1640154 prefixEnd_1640154 842187349394481123632075 := by
  unfold tailWord_1640154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14955332725002412211783879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39880887266673099231423677 14955332725002412211783879)
  ·
    refine ⟨22432999087503618317675819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14955332725002412211783879 22432999087503618317675819)
    ·
      refine ⟨33649498631255427476513729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22432999087503618317675819 33649498631255427476513729)
      ·
        refine ⟨25237123973441570607385297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33649498631255427476513729 25237123973441570607385297)
        ·
          refine ⟨18927842980081177955538973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25237123973441570607385297 18927842980081177955538973)
          ·
            refine ⟨7097941117530441733327115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18927842980081177955538973 7097941117530441733327115)
            ·
              refine ⟨10646911676295662599990673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7097941117530441733327115 10646911676295662599990673)
              ·
                refine ⟨7985183757221746949993005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10646911676295662599990673 7985183757221746949993005)
                ·
                  refine ⟨2994443908958155106247377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7985183757221746949993005 2994443908958155106247377)
                  ·
                    refine ⟨2245832931718616329685533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2994443908958155106247377 2245832931718616329685533)
                    ·
                      refine ⟨842187349394481123632075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2245832931718616329685533 842187349394481123632075)
                      ·
                        rfl

theorem cell23_1640154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_1640154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640154 prefixEnd_1640154 := by exact prefixLift 1640154
  have htrace : WordTrace (prefixWord ++ tailWord_1640154) baseStart_1640154 baseEnd_1640154 := by
    simpa [prefixWord, tailWord_1640154, baseEnd_1640154] using wordTrace_append hprefix tailTrace_1640154
  have hstable : (prefixWord ++ tailWord_1640154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640154).length < 2 ^ (prefixWord ++ tailWord_1640154).sum := by decide
  have hdescent : baseEnd_1640154 < baseStart_1640154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640164 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_1640164 : Nat := 118140960795 + 1640164 * 2 ^ 59
def prefixEnd_1640164 : Nat := 4983230072969 + 3 ^ 40 * 1640164 * 2
def baseEnd_1640164 : Nat := 842192484201026084507029

theorem tailTrace_1640164 : CollatzResearch.WordTrace tailWord_1640164 prefixEnd_1640164 842192484201026084507029 := by
  unfold tailWord_1640164
  simp only [CollatzResearch.WordTrace]
  refine ⟨29910847814986710277499773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39881130419982280369999697 29910847814986710277499773)
  ·
    refine ⟨11216567930620016354062415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29910847814986710277499773 11216567930620016354062415)
    ·
      refine ⟨16824851895930024531093623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11216567930620016354062415 16824851895930024531093623)
      ·
        refine ⟨25237277843895036796640435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16824851895930024531093623 25237277843895036796640435)
        ·
          refine ⟨37855916765842555194960653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25237277843895036796640435 37855916765842555194960653)
          ·
            refine ⟨14195968787190958198110245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37855916765842555194960653 14195968787190958198110245)
            ·
              refine ⟨2661744147598304662145671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14195968787190958198110245 2661744147598304662145671)
              ·
                refine ⟨3992616221397456993218507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2661744147598304662145671 3992616221397456993218507)
                ·
                  refine ⟨5988924332096185489827761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3992616221397456993218507 5988924332096185489827761)
                  ·
                    refine ⟨4491693249072139117370821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5988924332096185489827761 4491693249072139117370821)
                    ·
                      refine ⟨842192484201026084507029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4491693249072139117370821 842192484201026084507029)
                      ·
                        rfl

theorem cell23_1640164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_1640164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640164 prefixEnd_1640164 := by exact prefixLift 1640164
  have htrace : WordTrace (prefixWord ++ tailWord_1640164) baseStart_1640164 baseEnd_1640164 := by
    simpa [prefixWord, tailWord_1640164, baseEnd_1640164] using wordTrace_append hprefix tailTrace_1640164
  have hstable : (prefixWord ++ tailWord_1640164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640164).length < 2 ^ (prefixWord ++ tailWord_1640164).sum := by decide
  have hdescent : baseEnd_1640164 < baseStart_1640164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640168 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_1640168 : Nat := 118140960795 + 1640168 * 2 ^ 59
def prefixEnd_1640168 : Nat := 4983230072969 + 3 ^ 40 * 1640168 * 2
def baseEnd_1640168 : Nat := 842194538123644068857011

theorem tailTrace_1640168 : CollatzResearch.WordTrace tailWord_1640168 prefixEnd_1640168 842194538123644068857011 := by
  unfold tailWord_1640168
  simp only [CollatzResearch.WordTrace]
  refine ⟨29910920760979464619072579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39881227681305952825430105 29910920760979464619072579)
  ·
    refine ⟨44866381141469196928608869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29910920760979464619072579 44866381141469196928608869)
    ·
      refine ⟨8412446464025474424114163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44866381141469196928608869 8412446464025474424114163)
      ·
        refine ⟨12618669696038211636171245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8412446464025474424114163 12618669696038211636171245)
        ·
          refine ⟨4732001136014329363564217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12618669696038211636171245 4732001136014329363564217)
          ·
            refine ⟨3549000852010747022673163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4732001136014329363564217 3549000852010747022673163)
            ·
              refine ⟨5323501278016120534009745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3549000852010747022673163 5323501278016120534009745)
              ·
                refine ⟨3992625958512090400507309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5323501278016120534009745 3992625958512090400507309)
                ·
                  refine ⟨1497234734442033900190241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3992625958512090400507309 1497234734442033900190241)
                  ·
                    refine ⟨1122926050831525425142681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1497234734442033900190241 1122926050831525425142681)
                    ·
                      refine ⟨842194538123644068857011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1122926050831525425142681 842194538123644068857011)
                      ·
                        rfl

theorem cell23_1640168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_1640168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640168 prefixEnd_1640168 := by exact prefixLift 1640168
  have htrace : WordTrace (prefixWord ++ tailWord_1640168) baseStart_1640168 baseEnd_1640168 := by
    simpa [prefixWord, tailWord_1640168, baseEnd_1640168] using wordTrace_append hprefix tailTrace_1640168
  have hstable : (prefixWord ++ tailWord_1640168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640168).length < 2 ^ (prefixWord ++ tailWord_1640168).sum := by decide
  have hdescent : baseEnd_1640168 < baseStart_1640168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640174 : List Nat := [4, 1, 2, 1, 1, 2, 5, 7]
def baseStart_1640174 : Nat := 118140960795 + 1640174 * 2 ^ 59
def prefixEnd_1640174 : Nat := 4983230072969 + 3 ^ 40 * 1640174 * 2
def baseEnd_1640174 : Nat := 31192504407687816495629

theorem tailTrace_1640174 : CollatzResearch.WordTrace tailWord_1640174 prefixEnd_1640174 31192504407687816495629 := by
  unfold tailWord_1640174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7477757544992149032857947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39881373573291461508575717 7477757544992149032857947)
  ·
    refine ⟨11216636317488223549286921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7477757544992149032857947 11216636317488223549286921)
    ·
      refine ⟨8412477238116167661965191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11216636317488223549286921 8412477238116167661965191)
      ·
        refine ⟨12618715857174251492947787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8412477238116167661965191 12618715857174251492947787)
        ·
          refine ⟨18928073785761377239421681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12618715857174251492947787 18928073785761377239421681)
          ·
            refine ⟨14196055339321032929566261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18928073785761377239421681 14196055339321032929566261)
            ·
              refine ⟨1330880188061346837146837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14196055339321032929566261 1330880188061346837146837)
              ·
                refine ⟨31192504407687816495629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1330880188061346837146837 31192504407687816495629)
                ·
                  rfl

theorem cell23_1640174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_1640174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640174 prefixEnd_1640174 := by exact prefixLift 1640174
  have htrace : WordTrace (prefixWord ++ tailWord_1640174) baseStart_1640174 baseEnd_1640174 := by
    simpa [prefixWord, tailWord_1640174, baseEnd_1640174] using wordTrace_append hprefix tailTrace_1640174
  have hstable : (prefixWord ++ tailWord_1640174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640174).length < 2 ^ (prefixWord ++ tailWord_1640174).sum := by decide
  have hdescent : baseEnd_1640174 < baseStart_1640174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640207 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 4]
def baseStart_1640207 : Nat := 118140960795 + 1640207 * 2 ^ 59
def prefixEnd_1640207 : Nat := 4983230072969 + 3 ^ 40 * 1640207 * 2
def baseEnd_1640207 : Nat := 842214563869169416269331

theorem tailTrace_1640207 : CollatzResearch.WordTrace tailWord_1640207 prefixEnd_1640207 842214563869169416269331 := by
  unfold tailWord_1640207
  simp only [CollatzResearch.WordTrace]
  refine ⟨59823263968817638898814875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39882175979211759265876583 59823263968817638898814875)
  ·
    refine ⟨89734895953226458348222313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59823263968817638898814875 89734895953226458348222313)
    ·
      refine ⟨67301171964919843761166735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89734895953226458348222313 67301171964919843761166735)
      ·
        refine ⟨100951757947379765641750103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67301171964919843761166735 100951757947379765641750103)
        ·
          refine ⟨151427636921069648462625155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100951757947379765641750103 151427636921069648462625155)
          ·
            refine ⟨227141455381604472693937733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151427636921069648462625155 227141455381604472693937733)
            ·
              refine ⟨42589022884050838630113325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227141455381604472693937733 42589022884050838630113325)
              ·
                refine ⟨15970883581519064486292497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42589022884050838630113325 15970883581519064486292497)
                ·
                  refine ⟨11978162686139298364719373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15970883581519064486292497 11978162686139298364719373)
                  ·
                    refine ⟨4491811007302236886769765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11978162686139298364719373 4491811007302236886769765)
                    ·
                      refine ⟨842214563869169416269331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4491811007302236886769765 842214563869169416269331)
                      ·
                        rfl

theorem cell23_1640207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_1640207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640207 prefixEnd_1640207 := by exact prefixLift 1640207
  have htrace : WordTrace (prefixWord ++ tailWord_1640207) baseStart_1640207 baseEnd_1640207 := by
    simpa [prefixWord, tailWord_1640207, baseEnd_1640207] using wordTrace_append hprefix tailTrace_1640207
  have hstable : (prefixWord ++ tailWord_1640207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640207).length < 2 ^ (prefixWord ++ tailWord_1640207).sum := by decide
  have hdescent : baseEnd_1640207 < baseStart_1640207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640212 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1640212 : Nat := 118140960795 + 1640212 * 2 ^ 59
def prefixEnd_1640212 : Nat := 4983230072969 + 3 ^ 40 * 1640212 * 2
def baseEnd_1640212 : Nat := 280739043757480632235603

theorem tailTrace_1640212 : CollatzResearch.WordTrace tailWord_1640212 prefixEnd_1640212 280739043757480632235603 := by
  unfold tailWord_1640212
  simp only [CollatzResearch.WordTrace]
  refine ⟨29911723166899762376373445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39882297555866349835164593 29911723166899762376373445)
  ·
    refine ⟨5608448093793705445570021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29911723166899762376373445 5608448093793705445570021)
    ·
      refine ⟨1051584017586319771044379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5608448093793705445570021 1051584017586319771044379)
      ·
        refine ⟨1577376026379479656566569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1051584017586319771044379 1577376026379479656566569)
        ·
          refine ⟨1183032019784609742424927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1577376026379479656566569 1183032019784609742424927)
          ·
            refine ⟨1774548029676914613637391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183032019784609742424927 1774548029676914613637391)
            ·
              refine ⟨2661822044515371920456087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774548029676914613637391 2661822044515371920456087)
              ·
                refine ⟨3992733066773057880684131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2661822044515371920456087 3992733066773057880684131)
                ·
                  refine ⟨5989099600159586821026197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3992733066773057880684131 5989099600159586821026197)
                  ·
                    refine ⟨280739043757480632235603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5989099600159586821026197 280739043757480632235603)
                    ·
                      rfl

theorem cell23_1640212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1640212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640212 prefixEnd_1640212 := by exact prefixLift 1640212
  have htrace : WordTrace (prefixWord ++ tailWord_1640212) baseStart_1640212 baseEnd_1640212 := by
    simpa [prefixWord, tailWord_1640212, baseEnd_1640212] using wordTrace_append hprefix tailTrace_1640212
  have hstable : (prefixWord ++ tailWord_1640212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640212).length < 2 ^ (prefixWord ++ tailWord_1640212).sum := by decide
  have hdescent : baseEnd_1640212 < baseStart_1640212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640222 : List Nat := [4, 3, 2, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1640222 : Nat := 118140960795 + 1640222 * 2 ^ 59
def prefixEnd_1640222 : Nat := 4983230072969 + 3 ^ 40 * 1640222 * 2
def baseEnd_1640222 : Nat := 842222266078986857581763

theorem tailTrace_1640222 : CollatzResearch.WordTrace tailWord_1640222 prefixEnd_1640222 842222266078986857581763 := by
  unfold tailWord_1640222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7477976382970412057576365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39882540709175530973740613 7477976382970412057576365)
  ·
    refine ⟨2804241143613904521591137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7477976382970412057576365 2804241143613904521591137)
    ·
      refine ⟨2103180857710428391193353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2804241143613904521591137 2103180857710428391193353)
      ·
        refine ⟨1577385643282821293395015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2103180857710428391193353 1577385643282821293395015)
        ·
          refine ⟨2366078464924231940092523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1577385643282821293395015 2366078464924231940092523)
          ·
            refine ⟨3549117697386347910138785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366078464924231940092523 3549117697386347910138785)
            ·
              refine ⟨2661838273039760932604089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3549117697386347910138785 2661838273039760932604089)
              ·
                refine ⟨1996378704779820699453067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2661838273039760932604089 1996378704779820699453067)
                ·
                  refine ⟨2994568057169731049179601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996378704779820699453067 2994568057169731049179601)
                  ·
                    refine ⟨2245926042877298286884701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2994568057169731049179601 2245926042877298286884701)
                    ·
                      refine ⟨842222266078986857581763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2245926042877298286884701 842222266078986857581763)
                      ·
                        rfl

theorem cell23_1640222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1640222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640222 prefixEnd_1640222 := by exact prefixLift 1640222
  have htrace : WordTrace (prefixWord ++ tailWord_1640222) baseStart_1640222 baseEnd_1640222 := by
    simpa [prefixWord, tailWord_1640222, baseEnd_1640222] using wordTrace_append hprefix tailTrace_1640222
  have hstable : (prefixWord ++ tailWord_1640222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640222).length < 2 ^ (prefixWord ++ tailWord_1640222).sum := by decide
  have hdescent : baseEnd_1640222 < baseStart_1640222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640228 : List Nat := [2, 3, 1, 3, 2, 1, 1, 4, 1, 3, 2]
def baseStart_1640228 : Nat := 118140960795 + 1640228 * 2 ^ 59
def prefixEnd_1640228 : Nat := 4983230072969 + 3 ^ 40 * 1640228 * 2
def baseEnd_1640228 : Nat := 842225346962913834106735

theorem tailTrace_1640228 : CollatzResearch.WordTrace tailWord_1640228 prefixEnd_1640228 842225346962913834106735 := by
  unfold tailWord_1640228
  simp only [CollatzResearch.WordTrace]
  refine ⟨29912014950870779742664669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39882686601161039656886225 29912014950870779742664669)
  ·
    refine ⟨11217005606576542403499251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29912014950870779742664669 11217005606576542403499251)
    ·
      refine ⟨16825508409864813605248877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11217005606576542403499251 16825508409864813605248877)
      ·
        refine ⟨6309565653699305101968329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16825508409864813605248877 6309565653699305101968329)
        ·
          refine ⟨4732174240274478826476247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6309565653699305101968329 4732174240274478826476247)
          ·
            refine ⟨7098261360411718239714371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4732174240274478826476247 7098261360411718239714371)
            ·
              refine ⟨10647392040617577359571557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7098261360411718239714371 10647392040617577359571557)
              ·
                refine ⟨1996386007615795754919667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10647392040617577359571557 1996386007615795754919667)
                ·
                  refine ⟨2994579011423693632379501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996386007615795754919667 2994579011423693632379501)
                  ·
                    refine ⟨1122967129283885112142313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2994579011423693632379501 1122967129283885112142313)
                    ·
                      refine ⟨842225346962913834106735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1122967129283885112142313 842225346962913834106735)
                      ·
                        rfl

theorem cell23_1640228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_1640228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640228 prefixEnd_1640228 := by exact prefixLift 1640228
  have htrace : WordTrace (prefixWord ++ tailWord_1640228) baseStart_1640228 baseEnd_1640228 := by
    simpa [prefixWord, tailWord_1640228, baseEnd_1640228] using wordTrace_append hprefix tailTrace_1640228
  have hstable : (prefixWord ++ tailWord_1640228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640228).length < 2 ^ (prefixWord ++ tailWord_1640228).sum := by decide
  have hdescent : baseEnd_1640228 < baseStart_1640228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640264 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 7]
def baseStart_1640264 : Nat := 118140960795 + 1640264 * 2 ^ 59
def prefixEnd_1640264 : Nat := 4983230072969 + 3 ^ 40 * 1640264 * 2
def baseEnd_1640264 : Nat := 93582648029608410361841

theorem tailTrace_1640264 : CollatzResearch.WordTrace tailWord_1640264 prefixEnd_1640264 93582648029608410361841 := by
  unfold tailWord_1640264
  simp only [CollatzResearch.WordTrace]
  refine ⟨29912671464805568816819923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39883561953074091755759897 29912671464805568816819923)
  ·
    refine ⟨44869007197208353225229885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29912671464805568816819923 44869007197208353225229885)
    ·
      refine ⟨16825877698953132459461207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44869007197208353225229885 16825877698953132459461207)
      ·
        refine ⟨25238816548429698689191811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16825877698953132459461207 25238816548429698689191811)
        ·
          refine ⟨37858224822644548033787717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25238816548429698689191811 37858224822644548033787717)
          ·
            refine ⟨7098417154245852756335197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37858224822644548033787717 7098417154245852756335197)
            ·
              refine ⟨2661906432842194783625699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7098417154245852756335197 2661906432842194783625699)
              ·
                refine ⟨3992859649263292175438549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2661906432842194783625699 3992859649263292175438549)
                ·
                  refine ⟨93582648029608410361841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3992859649263292175438549 93582648029608410361841)
                  ·
                    rfl

theorem cell23_1640264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 7].length) (baseStart_1640264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640264 prefixEnd_1640264 := by exact prefixLift 1640264
  have htrace : WordTrace (prefixWord ++ tailWord_1640264) baseStart_1640264 baseEnd_1640264 := by
    simpa [prefixWord, tailWord_1640264, baseEnd_1640264] using wordTrace_append hprefix tailTrace_1640264
  have hstable : (prefixWord ++ tailWord_1640264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640264).length < 2 ^ (prefixWord ++ tailWord_1640264).sum := by decide
  have hdescent : baseEnd_1640264 < baseStart_1640264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640341 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 3, 4]
def baseStart_1640341 : Nat := 118140960795 + 1640341 * 2 ^ 59
def prefixEnd_1640341 : Nat := 4983230072969 + 3 ^ 40 * 1640341 * 2
def baseEnd_1640341 : Nat := 280761123425623963997905

theorem tailTrace_1640341 : CollatzResearch.WordTrace tailWord_1640341 prefixEnd_1640341 280761123425623963997905 := by
  unfold tailWord_1640341
  simp only [CollatzResearch.WordTrace]
  refine ⟨59828151350332179784192877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39885434233554786522795251 59828151350332179784192877)
  ·
    refine ⟨22435556756374567419072329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59828151350332179784192877 22435556756374567419072329)
    ·
      refine ⟨16826667567280925564304247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22435556756374567419072329 16826667567280925564304247)
      ·
        refine ⟨25240001350921388346456371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16826667567280925564304247 25240001350921388346456371)
        ·
          refine ⟨37860002026382082519684557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25240001350921388346456371 37860002026382082519684557)
          ·
            refine ⟨14197500759893280944881709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37860002026382082519684557 14197500759893280944881709)
            ·
              refine ⟨5324062784959980354330641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14197500759893280944881709 5324062784959980354330641)
              ·
                refine ⟨3993047088719985265747981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5324062784959980354330641 3993047088719985265747981)
                ·
                  refine ⟨1497392658269994474655493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3993047088719985265747981 1497392658269994474655493)
                  ·
                    refine ⟨280761123425623963997905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1497392658269994474655493 280761123425623963997905)
                    ·
                      rfl

theorem cell23_1640341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_1640341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640341 prefixEnd_1640341 := by exact prefixLift 1640341
  have htrace : WordTrace (prefixWord ++ tailWord_1640341) baseStart_1640341 baseEnd_1640341 := by
    simpa [prefixWord, tailWord_1640341, baseEnd_1640341] using wordTrace_append hprefix tailTrace_1640341
  have hstable : (prefixWord ++ tailWord_1640341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640341).length < 2 ^ (prefixWord ++ tailWord_1640341).sum := by decide
  have hdescent : baseEnd_1640341 < baseStart_1640341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640348 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1640348 : Nat := 118140960795 + 1640348 * 2 ^ 59
def prefixEnd_1640348 : Nat := 4983230072969 + 3 ^ 40 * 1640348 * 2
def baseEnd_1640348 : Nat := 842286964641453364606183

theorem tailTrace_1640348 : CollatzResearch.WordTrace tailWord_1640348 prefixEnd_1640348 842286964641453364606183 := by
  unfold tailWord_1640348
  simp only [CollatzResearch.WordTrace]
  refine ⟨29914203330653409989848849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39885604440871213319798465 29914203330653409989848849)
  ·
    refine ⟨22435652497990057492386637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29914203330653409989848849 22435652497990057492386637)
    ·
      refine ⟨8413369686746271559644989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22435652497990057492386637 8413369686746271559644989)
      ·
        refine ⟨3155013632529851834866871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8413369686746271559644989 3155013632529851834866871)
        ·
          refine ⟨4732520448794777752300307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3155013632529851834866871 4732520448794777752300307)
          ·
            refine ⟨7098780673192166628450461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4732520448794777752300307 7098780673192166628450461)
            ·
              refine ⟨2662042752447062485668923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7098780673192166628450461 2662042752447062485668923)
              ·
                refine ⟨3993064128670593728503385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2662042752447062485668923 3993064128670593728503385)
                ·
                  refine ⟨2994798096502945296377539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3993064128670593728503385 2994798096502945296377539)
                  ·
                    refine ⟨4492197144754417944566309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2994798096502945296377539 4492197144754417944566309)
                    ·
                      refine ⟨842286964641453364606183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4492197144754417944566309 842286964641453364606183)
                      ·
                        rfl

theorem cell23_1640348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1640348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640348 prefixEnd_1640348 := by exact prefixLift 1640348
  have htrace : WordTrace (prefixWord ++ tailWord_1640348) baseStart_1640348 baseEnd_1640348 := by
    simpa [prefixWord, tailWord_1640348, baseEnd_1640348] using wordTrace_append hprefix tailTrace_1640348
  have hstable : (prefixWord ++ tailWord_1640348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640348).length < 2 ^ (prefixWord ++ tailWord_1640348).sum := by decide
  have hdescent : baseEnd_1640348 < baseStart_1640348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640394 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_1640394 : Nat := 118140960795 + 1640394 * 2 ^ 59
def prefixEnd_1640394 : Nat := 4983230072969 + 3 ^ 40 * 1640394 * 2
def baseEnd_1640394 : Nat := 842310584751560184630971

theorem tailTrace_1640394 : CollatzResearch.WordTrace tailWord_1640394 prefixEnd_1640394 842310584751560184630971 := by
  unfold tailWord_1640394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14957521104785042458968059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39886722946093446557248157 14957521104785042458968059)
  ·
    refine ⟨22436281657177563688452089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14957521104785042458968059 22436281657177563688452089)
    ·
      refine ⟨16827211242883172766339067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22436281657177563688452089 16827211242883172766339067)
      ·
        refine ⟨25240816864324759149508601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16827211242883172766339067 25240816864324759149508601)
        ·
          refine ⟨18930612648243569362131451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25240816864324759149508601 18930612648243569362131451)
          ·
            refine ⟨28395918972365354043197177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18930612648243569362131451 28395918972365354043197177)
            ·
              refine ⟨21296939229274015532397883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28395918972365354043197177 21296939229274015532397883)
              ·
                refine ⟨31945408843911023298596825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21296939229274015532397883 31945408843911023298596825)
                ·
                  refine ⟨23959056632933267473947619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31945408843911023298596825 23959056632933267473947619)
                  ·
                    refine ⟨35938584949399901210921429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23959056632933267473947619 35938584949399901210921429)
                    ·
                      refine ⟨842310584751560184630971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35938584949399901210921429 842310584751560184630971)
                      ·
                        rfl

theorem cell23_1640394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_1640394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640394 prefixEnd_1640394 := by exact prefixLift 1640394
  have htrace : WordTrace (prefixWord ++ tailWord_1640394) baseStart_1640394 baseEnd_1640394 := by
    simpa [prefixWord, tailWord_1640394, baseEnd_1640394] using wordTrace_append hprefix tailTrace_1640394
  have hstable : (prefixWord ++ tailWord_1640394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640394).length < 2 ^ (prefixWord ++ tailWord_1640394).sum := by decide
  have hdescent : baseEnd_1640394 < baseStart_1640394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640398 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3]
def baseStart_1640398 : Nat := 118140960795 + 1640398 * 2 ^ 59
def prefixEnd_1640398 : Nat := 4983230072969 + 3 ^ 40 * 1640398 * 2
def baseEnd_1640398 : Nat := 842312638674178168980953

theorem tailTrace_1640398 : CollatzResearch.WordTrace tailWord_1640398 prefixEnd_1640398 842312638674178168980953 := by
  unfold tailWord_1640398
  simp only [CollatzResearch.WordTrace]
  refine ⟨7478778788890709814877231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39886820207417119012678565 7478778788890709814877231)
  ·
    refine ⟨11218168183336064722315847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7478778788890709814877231 11218168183336064722315847)
    ·
      refine ⟨16827252275004097083473771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11218168183336064722315847 16827252275004097083473771)
      ·
        refine ⟨25240878412506145625210657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16827252275004097083473771 25240878412506145625210657)
        ·
          refine ⟨18930658809379609218907993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25240878412506145625210657 18930658809379609218907993)
          ·
            refine ⟨14197994107034706914180995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18930658809379609218907993 14197994107034706914180995)
            ·
              refine ⟨21296991160552060371271493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14197994107034706914180995 21296991160552060371271493)
              ·
                refine ⟨3993185842603511319613405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21296991160552060371271493 3993185842603511319613405)
                ·
                  refine ⟨1497444690976316744855027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3993185842603511319613405 1497444690976316744855027)
                  ·
                    refine ⟨2246167036464475117282541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1497444690976316744855027 2246167036464475117282541)
                    ·
                      refine ⟨842312638674178168980953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2246167036464475117282541 842312638674178168980953)
                      ·
                        rfl

theorem cell23_1640398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_1640398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640398 prefixEnd_1640398 := by exact prefixLift 1640398
  have htrace : WordTrace (prefixWord ++ tailWord_1640398) baseStart_1640398 baseEnd_1640398 := by
    simpa [prefixWord, tailWord_1640398, baseEnd_1640398] using wordTrace_append hprefix tailTrace_1640398
  have hstable : (prefixWord ++ tailWord_1640398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640398).length < 2 ^ (prefixWord ++ tailWord_1640398).sum := by decide
  have hdescent : baseEnd_1640398 < baseStart_1640398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640408 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 2, 3, 2]
def baseStart_1640408 : Nat := 118140960795 + 1640408 * 2 ^ 59
def prefixEnd_1640408 : Nat := 4983230072969 + 3 ^ 40 * 1640408 * 2
def baseEnd_1640408 : Nat := 842317773480723129855907

theorem tailTrace_1640408 : CollatzResearch.WordTrace tailWord_1640408 prefixEnd_1640408 842317773480723129855907 := by
  unfold tailWord_1640408
  simp only [CollatzResearch.WordTrace]
  refine ⟨29915297520544725113440939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39887063360726300151254585 29915297520544725113440939)
  ·
    refine ⟨44872946280817087670161409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29915297520544725113440939 44872946280817087670161409)
    ·
      refine ⟨33654709710612815752621057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44872946280817087670161409 33654709710612815752621057)
      ·
        refine ⟨25241032282959611814465793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33654709710612815752621057 25241032282959611814465793)
        ·
          refine ⟨18930774212219708860849345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25241032282959611814465793 18930774212219708860849345)
          ·
            refine ⟨14198080659164781645637009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18930774212219708860849345 14198080659164781645637009)
            ·
              refine ⟨10648560494373586234227757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14198080659164781645637009 10648560494373586234227757)
              ·
                refine ⟨3993210185390094837835409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10648560494373586234227757 3993210185390094837835409)
                ·
                  refine ⟨2994907639042571128376557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3993210185390094837835409 2994907639042571128376557)
                  ·
                    refine ⟨1123090364640964173141209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2994907639042571128376557 1123090364640964173141209)
                    ·
                      refine ⟨842317773480723129855907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1123090364640964173141209 842317773480723129855907)
                      ·
                        rfl

theorem cell23_1640408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_1640408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640408 prefixEnd_1640408 := by exact prefixLift 1640408
  have htrace : WordTrace (prefixWord ++ tailWord_1640408) baseStart_1640408 baseEnd_1640408 := by
    simpa [prefixWord, tailWord_1640408, baseEnd_1640408] using wordTrace_append hprefix tailTrace_1640408
  have hstable : (prefixWord ++ tailWord_1640408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640408).length < 2 ^ (prefixWord ++ tailWord_1640408).sum := by decide
  have hdescent : baseEnd_1640408 < baseStart_1640408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640431 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 4, 4]
def baseStart_1640431 : Nat := 118140960795 + 1640431 * 2 ^ 59
def prefixEnd_1640431 : Nat := 4983230072969 + 3 ^ 40 * 1640431 * 2
def baseEnd_1640431 : Nat := 280776527845258846622767

theorem tailTrace_1640431 : CollatzResearch.WordTrace tailWord_1640431 prefixEnd_1640431 280776527845258846622767 := by
  unfold tailWord_1640431
  simp only [CollatzResearch.WordTrace]
  refine ⟨59831433920006125154969147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39887622613337416769979431 59831433920006125154969147)
  ·
    refine ⟨89747150880009187732453721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59831433920006125154969147 89747150880009187732453721)
    ·
      refine ⟨67310363160006890799340291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89747150880009187732453721 67310363160006890799340291)
      ·
        refine ⟨100965544740010336199010437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67310363160006890799340291 100965544740010336199010437)
        ·
          refine ⟨18931039638751938037314457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100965544740010336199010437 18931039638751938037314457)
          ·
            refine ⟨14198279729063953527985843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18931039638751938037314457 14198279729063953527985843)
            ·
              refine ⟨21297419593595930291978765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14198279729063953527985843 21297419593595930291978765)
              ·
                refine ⟨7986532347598473859492037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21297419593595930291978765 7986532347598473859492037)
                ·
                  refine ⟨1497474815174713848654757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7986532347598473859492037 1497474815174713848654757)
                  ·
                    refine ⟨280776527845258846622767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1497474815174713848654757 280776527845258846622767)
                    ·
                      rfl

theorem cell23_1640431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 4].length) (baseStart_1640431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640431 prefixEnd_1640431 := by exact prefixLift 1640431
  have htrace : WordTrace (prefixWord ++ tailWord_1640431) baseStart_1640431 baseEnd_1640431 := by
    simpa [prefixWord, tailWord_1640431, baseEnd_1640431] using wordTrace_append hprefix tailTrace_1640431
  have hstable : (prefixWord ++ tailWord_1640431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640431).length < 2 ^ (prefixWord ++ tailWord_1640431).sum := by decide
  have hdescent : baseEnd_1640431 < baseStart_1640431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640441 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 1, 1, 5]
def baseStart_1640441 : Nat := 118140960795 + 1640441 * 2 ^ 59
def prefixEnd_1640441 : Nat := 4983230072969 + 3 ^ 40 * 1640441 * 2
def baseEnd_1640441 : Nat := 842334718342321500743255

theorem tailTrace_1640441 : CollatzResearch.WordTrace tailWord_1640441 prefixEnd_1640441 842334718342321500743255 := by
  unfold tailWord_1640441
  simp only [CollatzResearch.WordTrace]
  refine ⟨59831798649969896862833177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39887865766646597908555451 59831798649969896862833177)
  ·
    refine ⟨44873848987477422647124883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59831798649969896862833177 44873848987477422647124883)
    ·
      refine ⟨67310773481216133970687325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44873848987477422647124883 67310773481216133970687325)
      ·
        refine ⟨25241540055456050239007747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67310773481216133970687325 25241540055456050239007747)
        ·
          refine ⟨37862310083184075358511621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25241540055456050239007747 37862310083184075358511621)
          ·
            refine ⟨7099183140597014129720929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37862310083184075358511621 7099183140597014129720929)
            ·
              refine ⟨5324387355447760597290697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7099183140597014129720929 5324387355447760597290697)
              ·
                refine ⟨3993290516585820447968023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5324387355447760597290697 3993290516585820447968023)
                ·
                  refine ⟨5989935774878730671952035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3993290516585820447968023 5989935774878730671952035)
                  ·
                    refine ⟨8984903662318096007928053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5989935774878730671952035 8984903662318096007928053)
                    ·
                      refine ⟨842334718342321500743255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8984903662318096007928053 842334718342321500743255)
                      ·
                        rfl

theorem cell23_1640441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_1640441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640441 prefixEnd_1640441 := by exact prefixLift 1640441
  have htrace : WordTrace (prefixWord ++ tailWord_1640441) baseStart_1640441 baseEnd_1640441 := by
    simpa [prefixWord, tailWord_1640441, baseEnd_1640441] using wordTrace_append hprefix tailTrace_1640441
  have hstable : (prefixWord ++ tailWord_1640441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640441).length < 2 ^ (prefixWord ++ tailWord_1640441).sum := by decide
  have hdescent : baseEnd_1640441 < baseStart_1640441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640452 : List Nat := [2, 3, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_1640452 : Nat := 118140960795 + 1640452 * 2 ^ 59
def prefixEnd_1640452 : Nat := 4983230072969 + 3 ^ 40 * 1640452 * 2
def baseEnd_1640452 : Nat := 280780122209840319235235

theorem tailTrace_1640452 : CollatzResearch.WordTrace tailWord_1640452 prefixEnd_1640452 280780122209840319235235 := by
  unfold tailWord_1640452
  simp only [CollatzResearch.WordTrace]
  refine ⟨29916099926465022870741805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39888133235286697160989073 29916099926465022870741805)
  ·
    refine ⟨11218537472424383576528177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29916099926465022870741805 11218537472424383576528177)
    ·
      refine ⟨8413903104318287682396133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11218537472424383576528177 8413903104318287682396133)
      ·
        refine ⟨1577606832059678940449275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8413903104318287682396133 1577606832059678940449275)
        ·
          refine ⟨2366410248089518410673913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1577606832059678940449275 2366410248089518410673913)
          ·
            refine ⟨1774807686067138808005435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2366410248089518410673913 1774807686067138808005435)
            ·
              refine ⟨2662211529100708212008153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774807686067138808005435 2662211529100708212008153)
              ·
                refine ⟨1996658646825531159006115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2662211529100708212008153 1996658646825531159006115)
                ·
                  refine ⟨2994987970238296738509173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996658646825531159006115 2994987970238296738509173)
                  ·
                    refine ⟨280780122209840319235235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2994987970238296738509173 280780122209840319235235)
                    ·
                      rfl

theorem cell23_1640452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_1640452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640452 prefixEnd_1640452 := by exact prefixLift 1640452
  have htrace : WordTrace (prefixWord ++ tailWord_1640452) baseStart_1640452 baseEnd_1640452 := by
    simpa [prefixWord, tailWord_1640452, baseEnd_1640452] using wordTrace_append hprefix tailTrace_1640452
  have hstable : (prefixWord ++ tailWord_1640452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640452).length < 2 ^ (prefixWord ++ tailWord_1640452).sum := by decide
  have hdescent : baseEnd_1640452 < baseStart_1640452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640455 : List Nat := [1, 1, 4, 3, 1, 4, 1, 2, 1, 1, 4]
def baseStart_1640455 : Nat := 118140960795 + 1640455 * 2 ^ 59
def prefixEnd_1640455 : Nat := 4983230072969 + 3 ^ 40 * 1640455 * 2
def baseEnd_1640455 : Nat := 842341907071484445968191

theorem tailTrace_1640455 : CollatzResearch.WordTrace tailWord_1640455 prefixEnd_1640455 842341907071484445968191 := by
  unfold tailWord_1640455
  simp only [CollatzResearch.WordTrace]
  refine ⟨59832309271919177253842819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39888206181279451502561879 59832309271919177253842819)
  ·
    refine ⟨89748463907878765880764229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59832309271919177253842819 89748463907878765880764229)
    ·
      refine ⟨16827836982727268602643293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89748463907878765880764229 16827836982727268602643293)
      ·
        refine ⟨6310438868522725725991235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16827836982727268602643293 6310438868522725725991235)
        ·
          refine ⟨9465658302784088588986853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6310438868522725725991235 9465658302784088588986853)
          ·
            refine ⟨1774810931772016610435035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9465658302784088588986853 1774810931772016610435035)
            ·
              refine ⟨2662216397658024915652553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774810931772016610435035 2662216397658024915652553)
              ·
                refine ⟨1996662298243518686739415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2662216397658024915652553 1996662298243518686739415)
                ·
                  refine ⟨2994993447365278030109123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996662298243518686739415 2994993447365278030109123)
                  ·
                    refine ⟨4492490171047917045163685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2994993447365278030109123 4492490171047917045163685)
                    ·
                      refine ⟨842341907071484445968191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4492490171047917045163685 842341907071484445968191)
                      ·
                        rfl

theorem cell23_1640455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_1640455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640455 prefixEnd_1640455 := by exact prefixLift 1640455
  have htrace : WordTrace (prefixWord ++ tailWord_1640455) baseStart_1640455 baseEnd_1640455 := by
    simpa [prefixWord, tailWord_1640455, baseEnd_1640455] using wordTrace_append hprefix tailTrace_1640455
  have hstable : (prefixWord ++ tailWord_1640455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640455).length < 2 ^ (prefixWord ++ tailWord_1640455).sum := by decide
  have hdescent : baseEnd_1640455 < baseStart_1640455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640464 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 6]
def baseStart_1640464 : Nat := 118140960795 + 1640464 * 2 ^ 59
def prefixEnd_1640464 : Nat := 4983230072969 + 3 ^ 40 * 1640464 * 2
def baseEnd_1640464 : Nat := 842346528397374910755649

theorem tailTrace_1640464 : CollatzResearch.WordTrace tailWord_1640464 prefixEnd_1640464 842346528397374910755649 := by
  unfold tailWord_1640464
  simp only [CollatzResearch.WordTrace]
  refine ⟨29916318764443285895460223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39888425019257714527280297 29916318764443285895460223)
  ·
    refine ⟨44874478146664928843190335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29916318764443285895460223 44874478146664928843190335)
    ·
      refine ⟨67311717219997393264785503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44874478146664928843190335 67311717219997393264785503)
      ·
        refine ⟨100967575829996089897178255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67311717219997393264785503 100967575829996089897178255)
        ·
          refine ⟨151451363744994134845767383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100967575829996089897178255 151451363744994134845767383)
          ·
            refine ⟨227177045617491202268651075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151451363744994134845767383 227177045617491202268651075)
            ·
              refine ⟨340765568426236803402976613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227177045617491202268651075 340765568426236803402976613)
              ·
                refine ⟨63893544079919400638058115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 340765568426236803402976613 63893544079919400638058115)
                ·
                  refine ⟨95840316119879100957087173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63893544079919400638058115 95840316119879100957087173)
                  ·
                    refine ⟨17970059272477331429453845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95840316119879100957087173 17970059272477331429453845)
                    ·
                      refine ⟨842346528397374910755649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17970059272477331429453845 842346528397374910755649)
                      ·
                        rfl

theorem cell23_1640464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_1640464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640464 prefixEnd_1640464 := by exact prefixLift 1640464
  have htrace : WordTrace (prefixWord ++ tailWord_1640464) baseStart_1640464 baseEnd_1640464 := by
    simpa [prefixWord, tailWord_1640464, baseEnd_1640464] using wordTrace_append hprefix tailTrace_1640464
  have hstable : (prefixWord ++ tailWord_1640464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640464).length < 2 ^ (prefixWord ++ tailWord_1640464).sum := by decide
  have hdescent : baseEnd_1640464 < baseStart_1640464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640472 : List Nat := [2, 1, 2, 3, 2, 1, 2, 5, 1, 2, 2]
def baseStart_1640472 : Nat := 118140960795 + 1640472 * 2 ^ 59
def prefixEnd_1640472 : Nat := 4983230072969 + 3 ^ 40 * 1640472 * 2
def baseEnd_1640472 : Nat := 842350636242610879455613

theorem tailTrace_1640472 : CollatzResearch.WordTrace tailWord_1640472 prefixEnd_1640472 842350636242610879455613 := by
  unfold tailWord_1640472
  simp only [CollatzResearch.WordTrace]
  refine ⟨29916464656428794578605835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39888619541905059438141113 29916464656428794578605835)
  ·
    refine ⟨44874696984643191867908753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29916464656428794578605835 44874696984643191867908753)
    ·
      refine ⟨33656022738482393900931565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44874696984643191867908753 33656022738482393900931565)
      ·
        refine ⟨12621008526930897712849337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33656022738482393900931565 12621008526930897712849337)
        ·
          refine ⟨9465756395198173284637003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12621008526930897712849337 9465756395198173284637003)
          ·
            refine ⟨14198634592797259926955505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9465756395198173284637003 14198634592797259926955505)
            ·
              refine ⟨10648975944597944945216629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14198634592797259926955505 10648975944597944945216629)
              ·
                refine ⟨998341494806057338614059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10648975944597944945216629 998341494806057338614059)
                ·
                  refine ⟨1497512242209086007921089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998341494806057338614059 1497512242209086007921089)
                  ·
                    refine ⟨1123134181656814505940817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1497512242209086007921089 1123134181656814505940817)
                    ·
                      refine ⟨842350636242610879455613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1123134181656814505940817 842350636242610879455613)
                      ·
                        rfl

theorem cell23_1640472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_1640472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640472 prefixEnd_1640472 := by exact prefixLift 1640472
  have htrace : WordTrace (prefixWord ++ tailWord_1640472) baseStart_1640472 baseEnd_1640472 := by
    simpa [prefixWord, tailWord_1640472, baseEnd_1640472] using wordTrace_append hprefix tailTrace_1640472
  have hstable : (prefixWord ++ tailWord_1640472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640472).length < 2 ^ (prefixWord ++ tailWord_1640472).sum := by decide
  have hdescent : baseEnd_1640472 < baseStart_1640472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640505 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 1, 3, 3]
def baseStart_1640505 : Nat := 118140960795 + 1640505 * 2 ^ 59
def prefixEnd_1640505 : Nat := 4983230072969 + 3 ^ 40 * 1640505 * 2
def baseEnd_1640505 : Nat := 842367581104209250342961

theorem tailTrace_1640505 : CollatzResearch.WordTrace tailWord_1640505 prefixEnd_1640505 842367581104209250342961 := by
  unfold tailWord_1640505
  simp only [CollatzResearch.WordTrace]
  refine ⟨59834132921738035793162969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39889421947825357195441979 59834132921738035793162969)
  ·
    refine ⟨44875599691303526844872227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59834132921738035793162969 44875599691303526844872227)
    ·
      refine ⟨67313399536955290267308341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44875599691303526844872227 67313399536955290267308341)
      ·
        refine ⟨6310631206589558462560157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67313399536955290267308341 6310631206589558462560157)
        ·
          refine ⟨2366486702471084423460059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6310631206589558462560157 2366486702471084423460059)
          ·
            refine ⟨3549730053706626635190089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366486702471084423460059 3549730053706626635190089)
            ·
              refine ⟨2662297540279969976392567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3549730053706626635190089 2662297540279969976392567)
              ·
                refine ⟨3993446310419954964588851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2662297540279969976392567 3993446310419954964588851)
                ·
                  refine ⟨5990169465629932446883277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3993446310419954964588851 5990169465629932446883277)
                  ·
                    refine ⟨2246313549611224667581229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5990169465629932446883277 2246313549611224667581229)
                    ·
                      refine ⟨842367581104209250342961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2246313549611224667581229 842367581104209250342961)
                      ·
                        rfl

theorem cell23_1640505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_1640505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640505 prefixEnd_1640505 := by exact prefixLift 1640505
  have htrace : WordTrace (prefixWord ++ tailWord_1640505) baseStart_1640505 baseEnd_1640505 := by
    simpa [prefixWord, tailWord_1640505, baseEnd_1640505] using wordTrace_append hprefix tailTrace_1640505
  have hstable : (prefixWord ++ tailWord_1640505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640505).length < 2 ^ (prefixWord ++ tailWord_1640505).sum := by decide
  have hdescent : baseEnd_1640505 < baseStart_1640505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640558 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1640558 : Nat := 118140960795 + 1640558 * 2 ^ 59
def prefixEnd_1640558 : Nat := 4983230072969 + 3 ^ 40 * 1640558 * 2
def baseEnd_1640558 : Nat := 842394795578897542980217

theorem tailTrace_1640558 : CollatzResearch.WordTrace tailWord_1640558 prefixEnd_1640558 842394795578897542980217 := by
  unfold tailWord_1640558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7479508248818253230605291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39890710660364017229894885 7479508248818253230605291)
  ·
    refine ⟨11219262373227379845907937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7479508248818253230605291 11219262373227379845907937)
    ·
      refine ⟨8414446779920534884430953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11219262373227379845907937 8414446779920534884430953)
      ·
        refine ⟨6310835084940401163323215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8414446779920534884430953 6310835084940401163323215)
        ·
          refine ⟨9466252627410601744984823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6310835084940401163323215 9466252627410601744984823)
          ·
            refine ⟨14199378941115902617477235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9466252627410601744984823 14199378941115902617477235)
            ·
              refine ⟨21299068411673853926215853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14199378941115902617477235 21299068411673853926215853)
              ·
                refine ⟨7987150654377695222330945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21299068411673853926215853 7987150654377695222330945)
                ·
                  refine ⟨5990362990783271416748209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7987150654377695222330945 5990362990783271416748209)
                  ·
                    refine ⟨4492772243087453562561157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5990362990783271416748209 4492772243087453562561157)
                    ·
                      refine ⟨842394795578897542980217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4492772243087453562561157 842394795578897542980217)
                      ·
                        rfl

theorem cell23_1640558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1640558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640558 prefixEnd_1640558 := by exact prefixLift 1640558
  have htrace : WordTrace (prefixWord ++ tailWord_1640558) baseStart_1640558 baseEnd_1640558 := by
    simpa [prefixWord, tailWord_1640558, baseEnd_1640558] using wordTrace_append hprefix tailTrace_1640558
  have hstable : (prefixWord ++ tailWord_1640558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640558).length < 2 ^ (prefixWord ++ tailWord_1640558).sum := by decide
  have hdescent : baseEnd_1640558 < baseStart_1640558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640562 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 1, 4, 2]
def baseStart_1640562 : Nat := 118140960795 + 1640562 * 2 ^ 59
def prefixEnd_1640562 : Nat := 4983230072969 + 3 ^ 40 * 1640562 * 2
def baseEnd_1640562 : Nat := 842396849501515527330199

theorem tailTrace_1640562 : CollatzResearch.WordTrace tailWord_1640562 prefixEnd_1640562 842396849501515527330199 := by
  unfold tailWord_1640562
  simp only [CollatzResearch.WordTrace]
  refine ⟨14959052970632883631996985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39890807921687689685325293 14959052970632883631996985)
  ·
    refine ⟨11219289727974662723997739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14959052970632883631996985 11219289727974662723997739)
    ·
      refine ⟨16828934591961994085996609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11219289727974662723997739 16828934591961994085996609)
      ·
        refine ⟨12621700943971495564497457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16828934591961994085996609 12621700943971495564497457)
        ·
          refine ⟨9466275707978621673373093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12621700943971495564497457 9466275707978621673373093)
          ·
            refine ⟨1774926695245991563757455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9466275707978621673373093 1774926695245991563757455)
            ·
              refine ⟨2662390042868987345636183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774926695245991563757455 2662390042868987345636183)
              ·
                refine ⟨3993585064303481018454275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2662390042868987345636183 3993585064303481018454275)
                ·
                  refine ⟨5990377596455221527681413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3993585064303481018454275 5990377596455221527681413)
                  ·
                    refine ⟨1123195799335354036440265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5990377596455221527681413 1123195799335354036440265)
                    ·
                      refine ⟨842396849501515527330199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1123195799335354036440265 842396849501515527330199)
                      ·
                        rfl

theorem cell23_1640562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_1640562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640562 prefixEnd_1640562 := by exact prefixLift 1640562
  have htrace : WordTrace (prefixWord ++ tailWord_1640562) baseStart_1640562 baseEnd_1640562 := by
    simpa [prefixWord, tailWord_1640562, baseEnd_1640562] using wordTrace_append hprefix tailTrace_1640562
  have hstable : (prefixWord ++ tailWord_1640562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640562).length < 2 ^ (prefixWord ++ tailWord_1640562).sum := by decide
  have hdescent : baseEnd_1640562 < baseStart_1640562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640588 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 3, 7, 2]
def baseStart_1640588 : Nat := 118140960795 + 1640588 * 2 ^ 59
def prefixEnd_1640588 : Nat := 4983230072969 + 3 ^ 40 * 1640588 * 2
def baseEnd_1640588 : Nat := 842410199998532425605079

theorem tailTrace_1640588 : CollatzResearch.WordTrace tailWord_1640588 prefixEnd_1640588 842410199998532425605079 := by
  unfold tailWord_1640588
  simp only [CollatzResearch.WordTrace]
  refine ⟨29918580090218670484217209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39891440120291560645622945 29918580090218670484217209)
  ·
    refine ⟨22438935067664002863162907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29918580090218670484217209 22438935067664002863162907)
    ·
      refine ⟨33658402601496004294744361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22438935067664002863162907 33658402601496004294744361)
      ·
        refine ⟨25243801951122003221058271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33658402601496004294744361 25243801951122003221058271)
        ·
          refine ⟨37865702926683004831587407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25243801951122003221058271 37865702926683004831587407)
          ·
            refine ⟨56798554390024507247381111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37865702926683004831587407 56798554390024507247381111)
            ·
              refine ⟨85197831585036760871071667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56798554390024507247381111 85197831585036760871071667)
              ·
                refine ⟨127796747377555141306607501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85197831585036760871071667 127796747377555141306607501)
                ·
                  refine ⟨47923780266583177989977813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127796747377555141306607501 47923780266583177989977813)
                  ·
                    refine ⟨1123213599998043234140105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47923780266583177989977813 1123213599998043234140105)
                    ·
                      refine ⟨842410199998532425605079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1123213599998043234140105 842410199998532425605079)
                      ·
                        rfl

theorem cell23_1640588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_1640588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640588 prefixEnd_1640588 := by exact prefixLift 1640588
  have htrace : WordTrace (prefixWord ++ tailWord_1640588) baseStart_1640588 baseEnd_1640588 := by
    simpa [prefixWord, tailWord_1640588, baseEnd_1640588] using wordTrace_append hprefix tailTrace_1640588
  have hstable : (prefixWord ++ tailWord_1640588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640588).length < 2 ^ (prefixWord ++ tailWord_1640588).sum := by decide
  have hdescent : baseEnd_1640588 < baseStart_1640588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640602 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 7]
def baseStart_1640602 : Nat := 118140960795 + 1640602 * 2 ^ 59
def prefixEnd_1640602 : Nat := 4983230072969 + 3 ^ 40 * 1640602 * 2
def baseEnd_1640602 : Nat := 93601932080855041203335

theorem tailTrace_1640602 : CollatzResearch.WordTrace tailWord_1640602 prefixEnd_1640602 93601932080855041203335 := by
  unfold tailWord_1640602
  simp only [CollatzResearch.WordTrace]
  refine ⟨14959417700596655339861015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39891780534924414239629373 14959417700596655339861015)
  ·
    refine ⟨22439126550894983009791523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14959417700596655339861015 22439126550894983009791523)
    ·
      refine ⟨33658689826342474514687285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22439126550894983009791523 33658689826342474514687285)
      ·
        refine ⟨3155502171219606985751933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33658689826342474514687285 3155502171219606985751933)
        ·
          refine ⟨1183313314207352619656975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3155502171219606985751933 1183313314207352619656975)
          ·
            refine ⟨1774969971311028929485463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183313314207352619656975 1774969971311028929485463)
            ·
              refine ⟨2662454956966543394228195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774969971311028929485463 2662454956966543394228195)
              ·
                refine ⟨3993682435449815091342293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2662454956966543394228195 3993682435449815091342293)
                ·
                  refine ⟨93601932080855041203335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3993682435449815091342293 93601932080855041203335)
                  ·
                    rfl

theorem cell23_1640602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 7].length) (baseStart_1640602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640602 prefixEnd_1640602 := by exact prefixLift 1640602
  have htrace : WordTrace (prefixWord ++ tailWord_1640602) baseStart_1640602 baseEnd_1640602 := by
    simpa [prefixWord, tailWord_1640602, baseEnd_1640602] using wordTrace_append hprefix tailTrace_1640602
  have hstable : (prefixWord ++ tailWord_1640602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640602).length < 2 ^ (prefixWord ++ tailWord_1640602).sum := by decide
  have hdescent : baseEnd_1640602 < baseStart_1640602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640608 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 5]
def baseStart_1640608 : Nat := 118140960795 + 1640608 * 2 ^ 59
def prefixEnd_1640608 : Nat := 4983230072969 + 3 ^ 40 * 1640608 * 2
def baseEnd_1640608 : Nat := 842420469611622347354987

theorem tailTrace_1640608 : CollatzResearch.WordTrace tailWord_1640608 prefixEnd_1640608 842420469611622347354987 := by
  unfold tailWord_1640608
  simp only [CollatzResearch.WordTrace]
  refine ⟨29918944820182442192081239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39891926426909922922774985 29918944820182442192081239)
  ·
    refine ⟨44878417230273663288121859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29918944820182442192081239 44878417230273663288121859)
    ·
      refine ⟨67317625845410494932182789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44878417230273663288121859 67317625845410494932182789)
      ·
        refine ⟨12622054846014467799784273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67317625845410494932182789 12622054846014467799784273)
        ·
          refine ⟨9466541134510850849838205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12622054846014467799784273 9466541134510850849838205)
          ·
            refine ⟨3549952925441569068689327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9466541134510850849838205 3549952925441569068689327)
            ·
              refine ⟨5324929388162353603033991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3549952925441569068689327 5324929388162353603033991)
              ·
                refine ⟨7987394082243530404550987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5324929388162353603033991 7987394082243530404550987)
                ·
                  refine ⟨11981091123365295606826481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7987394082243530404550987 11981091123365295606826481)
                  ·
                    refine ⟨8985818342523971705119861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11981091123365295606826481 8985818342523971705119861)
                    ·
                      refine ⟨842420469611622347354987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8985818342523971705119861 842420469611622347354987)
                      ·
                        rfl

theorem cell23_1640608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_1640608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640608 prefixEnd_1640608 := by exact prefixLift 1640608
  have htrace : WordTrace (prefixWord ++ tailWord_1640608) baseStart_1640608 baseEnd_1640608 := by
    simpa [prefixWord, tailWord_1640608, baseEnd_1640608] using wordTrace_append hprefix tailTrace_1640608
  have hstable : (prefixWord ++ tailWord_1640608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640608).length < 2 ^ (prefixWord ++ tailWord_1640608).sum := by decide
  have hdescent : baseEnd_1640608 < baseStart_1640608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640642 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1640642 : Nat := 118140960795 + 1640642 * 2 ^ 59
def prefixEnd_1640642 : Nat := 4983230072969 + 3 ^ 40 * 1640642 * 2
def baseEnd_1640642 : Nat := 842437927953875214329831

theorem tailTrace_1640642 : CollatzResearch.WordTrace tailWord_1640642 prefixEnd_1640642 842437927953875214329831 := by
  unfold tailWord_1640642
  simp only [CollatzResearch.WordTrace]
  refine ⟨14959782430560427047725045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39892753148161138793933453 14959782430560427047725045)
  ·
    refine ⟨1402479602865040035724223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14959782430560427047725045 1402479602865040035724223)
    ·
      refine ⟨2103719404297560053586335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1402479602865040035724223 2103719404297560053586335)
      ·
        refine ⟨3155579106446340080379503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103719404297560053586335 3155579106446340080379503)
        ·
          refine ⟨4733368659669510120569255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3155579106446340080379503 4733368659669510120569255)
          ·
            refine ⟨7100052989504265180853883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733368659669510120569255 7100052989504265180853883)
            ·
              refine ⟨10650079484256397771280825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7100052989504265180853883 10650079484256397771280825)
              ·
                refine ⟨7987559613192298328460619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10650079484256397771280825 7987559613192298328460619)
                ·
                  refine ⟨11981339419788447492690929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7987559613192298328460619 11981339419788447492690929)
                  ·
                    refine ⟨8986004564841335619518197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11981339419788447492690929 8986004564841335619518197)
                    ·
                      refine ⟨842437927953875214329831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8986004564841335619518197 842437927953875214329831)
                      ·
                        rfl

theorem cell23_1640642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1640642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640642 prefixEnd_1640642 := by exact prefixLift 1640642
  have htrace : WordTrace (prefixWord ++ tailWord_1640642) baseStart_1640642 baseEnd_1640642 := by
    simpa [prefixWord, tailWord_1640642, baseEnd_1640642] using wordTrace_append hprefix tailTrace_1640642
  have hstable : (prefixWord ++ tailWord_1640642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640642).length < 2 ^ (prefixWord ++ tailWord_1640642).sum := by decide
  have hdescent : baseEnd_1640642 < baseStart_1640642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640702 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_1640702 : Nat := 118140960795 + 1640702 * 2 ^ 59
def prefixEnd_1640702 : Nat := 4983230072969 + 3 ^ 40 * 1640702 * 2
def baseEnd_1640702 : Nat := 842468736793144979579555

theorem tailTrace_1640702 : CollatzResearch.WordTrace tailWord_1640702 prefixEnd_1640702 842468736793144979579555 := by
  unfold tailWord_1640702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7480164762753042304760545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39894212068016225625389573 7480164762753042304760545)
  ·
    refine ⟨5610123572064781728570409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7480164762753042304760545 5610123572064781728570409)
    ·
      refine ⟨4207592679048586296427807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5610123572064781728570409 4207592679048586296427807)
      ·
        refine ⟨6311389018572879444641711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4207592679048586296427807 6311389018572879444641711)
        ·
          refine ⟨9467083527859319166962567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6311389018572879444641711 9467083527859319166962567)
          ·
            refine ⟨14200625291788978750443851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9467083527859319166962567 14200625291788978750443851)
            ·
              refine ⟨21300937937683468125665777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14200625291788978750443851 21300937937683468125665777)
              ·
                refine ⟨15975703453262601094249333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21300937937683468125665777 15975703453262601094249333)
                ·
                  refine ⟨1497722198743368852585875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15975703453262601094249333 1497722198743368852585875)
                  ·
                    refine ⟨2246583298115053278878813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1497722198743368852585875 2246583298115053278878813)
                    ·
                      refine ⟨842468736793144979579555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2246583298115053278878813 842468736793144979579555)
                      ·
                        rfl

theorem cell23_1640702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_1640702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640702 prefixEnd_1640702 := by exact prefixLift 1640702
  have htrace : WordTrace (prefixWord ++ tailWord_1640702) baseStart_1640702 baseEnd_1640702 := by
    simpa [prefixWord, tailWord_1640702, baseEnd_1640702] using wordTrace_append hprefix tailTrace_1640702
  have hstable : (prefixWord ++ tailWord_1640702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640702).length < 2 ^ (prefixWord ++ tailWord_1640702).sum := by decide
  have hdescent : baseEnd_1640702 < baseStart_1640702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640705 : List Nat := [1, 2, 4, 1, 1, 2, 3, 3, 1, 5]
def baseStart_1640705 : Nat := 118140960795 + 1640705 * 2 ^ 59
def prefixEnd_1640705 : Nat := 4983230072969 + 3 ^ 40 * 1640705 * 2
def baseEnd_1640705 : Nat := 280823425745036155947347

theorem tailTrace_1640705 : CollatzResearch.WordTrace tailWord_1640705 prefixEnd_1640705 280823425745036155947347 := by
  unfold tailWord_1640705
  simp only [CollatzResearch.WordTrace]
  refine ⟨59841427521013469950443569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39894285014008979966962379 59841427521013469950443569)
  ·
    refine ⟨44881070640760102462832677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59841427521013469950443569 44881070640760102462832677)
    ·
      refine ⟨8415200745142519211781127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44881070640760102462832677 8415200745142519211781127)
      ·
        refine ⟨12622801117713778817671691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8415200745142519211781127 12622801117713778817671691)
        ·
          refine ⟨18934201676570668226507537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12622801117713778817671691 18934201676570668226507537)
          ·
            refine ⟨14200651257428001169880653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18934201676570668226507537 14200651257428001169880653)
            ·
              refine ⟨5325244221535500438705245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14200651257428001169880653 5325244221535500438705245)
              ·
                refine ⟨1996966583075812664514467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5325244221535500438705245 1996966583075812664514467)
                ·
                  refine ⟨2995449874613718996771701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1996966583075812664514467 2995449874613718996771701)
                  ·
                    refine ⟨280823425745036155947347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2995449874613718996771701 280823425745036155947347)
                    ·
                      rfl

theorem cell23_1640705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_1640705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640705 prefixEnd_1640705 := by exact prefixLift 1640705
  have htrace : WordTrace (prefixWord ++ tailWord_1640705) baseStart_1640705 baseEnd_1640705 := by
    simpa [prefixWord, tailWord_1640705, baseEnd_1640705] using wordTrace_append hprefix tailTrace_1640705
  have hstable : (prefixWord ++ tailWord_1640705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640705).length < 2 ^ (prefixWord ++ tailWord_1640705).sum := by decide
  have hdescent : baseEnd_1640705 < baseStart_1640705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640735 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 1, 6]
def baseStart_1640735 : Nat := 118140960795 + 1640735 * 2 ^ 59
def prefixEnd_1640735 : Nat := 4983230072969 + 3 ^ 40 * 1640735 * 2
def baseEnd_1640735 : Nat := 280828560551581116822301

theorem tailTrace_1640735 : CollatzResearch.WordTrace tailWord_1640735 prefixEnd_1640735 280828560551581116822301 := by
  unfold tailWord_1640735
  simp only [CollatzResearch.WordTrace]
  refine ⟨59842521710904785074035659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39895014473936523382690439 59842521710904785074035659)
  ·
    refine ⟨89763782566357177611053489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59842521710904785074035659 89763782566357177611053489)
    ·
      refine ⟨67322836924767883208290117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89763782566357177611053489 67322836924767883208290117)
      ·
        refine ⟨12623031923393978101554397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67322836924767883208290117 12623031923393978101554397)
        ·
          refine ⟨4733636971272741788082899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12623031923393978101554397 4733636971272741788082899)
          ·
            refine ⟨7100455456909112682124349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733636971272741788082899 7100455456909112682124349)
            ·
              refine ⟨2662670796340917255796631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7100455456909112682124349 2662670796340917255796631)
              ·
                refine ⟨3994006194511375883694947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2662670796340917255796631 3994006194511375883694947)
                ·
                  refine ⟨5991009291767063825542421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3994006194511375883694947 5991009291767063825542421)
                  ·
                    refine ⟨280828560551581116822301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5991009291767063825542421 280828560551581116822301)
                    ·
                      rfl

theorem cell23_1640735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 6].length) (baseStart_1640735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640735 prefixEnd_1640735 := by exact prefixLift 1640735
  have htrace : WordTrace (prefixWord ++ tailWord_1640735) baseStart_1640735 baseEnd_1640735 := by
    simpa [prefixWord, tailWord_1640735, baseEnd_1640735] using wordTrace_append hprefix tailTrace_1640735
  have hstable : (prefixWord ++ tailWord_1640735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640735).length < 2 ^ (prefixWord ++ tailWord_1640735).sum := by decide
  have hdescent : baseEnd_1640735 < baseStart_1640735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640753 : List Nat := [1, 2, 2, 3, 5, 1, 1, 3, 1, 1, 3]
def baseStart_1640753 : Nat := 118140960795 + 1640753 * 2 ^ 59
def prefixEnd_1640753 : Nat := 4983230072969 + 3 ^ 40 * 1640753 * 2
def baseEnd_1640753 : Nat := 842494924306524280041821

theorem tailTrace_1640753 : CollatzResearch.WordTrace tailWord_1640753 prefixEnd_1640753 842494924306524280041821 := by
  unfold tailWord_1640753
  simp only [CollatzResearch.WordTrace]
  refine ⟨59843178224839574148190913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39895452149893049432127275 59843178224839574148190913)
  ·
    refine ⟨44882383668629680611143185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59843178224839574148190913 44882383668629680611143185)
    ·
      refine ⟨33661787751472260458357389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44882383668629680611143185 33661787751472260458357389)
      ·
        refine ⟨12623170406802097671884021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33661787751472260458357389 12623170406802097671884021)
        ·
          refine ⟨1183422225637696656739127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12623170406802097671884021 1183422225637696656739127)
          ·
            refine ⟨1775133338456544985108691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183422225637696656739127 1775133338456544985108691)
            ·
              refine ⟨2662700007684817477663037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775133338456544985108691 2662700007684817477663037)
              ·
                refine ⟨998512502881806554123639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2662700007684817477663037 998512502881806554123639)
                ·
                  refine ⟨1497768754322709831185459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998512502881806554123639 1497768754322709831185459)
                  ·
                    refine ⟨2246653131484064746778189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1497768754322709831185459 2246653131484064746778189)
                    ·
                      refine ⟨842494924306524280041821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2246653131484064746778189 842494924306524280041821)
                      ·
                        rfl

theorem cell23_1640753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_1640753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640753 prefixEnd_1640753 := by exact prefixLift 1640753
  have htrace : WordTrace (prefixWord ++ tailWord_1640753) baseStart_1640753 baseEnd_1640753 := by
    simpa [prefixWord, tailWord_1640753, baseEnd_1640753] using wordTrace_append hprefix tailTrace_1640753
  have hstable : (prefixWord ++ tailWord_1640753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640753).length < 2 ^ (prefixWord ++ tailWord_1640753).sum := by decide
  have hdescent : baseEnd_1640753 < baseStart_1640753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640762 : List Nat := [3, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3]
def baseStart_1640762 : Nat := 118140960795 + 1640762 * 2 ^ 59
def prefixEnd_1640762 : Nat := 4983230072969 + 3 ^ 40 * 1640762 * 2
def baseEnd_1640762 : Nat := 842499545632414744829279

theorem tailTrace_1640762 : CollatzResearch.WordTrace tailWord_1640762 prefixEnd_1640762 842499545632414744829279 := by
  unfold tailWord_1640762
  simp only [CollatzResearch.WordTrace]
  refine ⟨14960876620451742171317135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39895670987871312456845693 14960876620451742171317135)
  ·
    refine ⟨22441314930677613256975703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14960876620451742171317135 22441314930677613256975703)
    ·
      refine ⟨33661972396016419885463555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22441314930677613256975703 33661972396016419885463555)
      ·
        refine ⟨50492958594024629828195333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33661972396016419885463555 50492958594024629828195333)
        ·
          refine ⟨9467429736379618092786625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50492958594024629828195333 9467429736379618092786625)
          ·
            refine ⟨7100572302284713569589969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9467429736379618092786625 7100572302284713569589969)
            ·
              refine ⟨5325429226713535177192477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7100572302284713569589969 5325429226713535177192477)
              ·
                refine ⟨1997035960017575691447179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5325429226713535177192477 1997035960017575691447179)
                ·
                  refine ⟨2995553940026363537170769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1997035960017575691447179 2995553940026363537170769)
                  ·
                    refine ⟨2246665455019772652878077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2995553940026363537170769 2246665455019772652878077)
                    ·
                      refine ⟨842499545632414744829279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2246665455019772652878077 842499545632414744829279)
                      ·
                        rfl

theorem cell23_1640762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_1640762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640762 prefixEnd_1640762 := by exact prefixLift 1640762
  have htrace : WordTrace (prefixWord ++ tailWord_1640762) baseStart_1640762 baseEnd_1640762 := by
    simpa [prefixWord, tailWord_1640762, baseEnd_1640762] using wordTrace_append hprefix tailTrace_1640762
  have hstable : (prefixWord ++ tailWord_1640762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640762).length < 2 ^ (prefixWord ++ tailWord_1640762).sum := by decide
  have hdescent : baseEnd_1640762 < baseStart_1640762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640848 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 9]
def baseStart_1640848 : Nat := 118140960795 + 1640848 * 2 ^ 59
def prefixEnd_1640848 : Nat := 4983230072969 + 3 ^ 40 * 1640848 * 2
def baseEnd_1640848 : Nat := 842543704968701408353883

theorem tailTrace_1640848 : CollatzResearch.WordTrace tailWord_1640848 prefixEnd_1640848 842543704968701408353883 := by
  unfold tailWord_1640848
  simp only [CollatzResearch.WordTrace]
  refine ⟨29923321579747702686449599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39897762106330270248599465 29923321579747702686449599)
  ·
    refine ⟨44884982369621554029674399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29923321579747702686449599 44884982369621554029674399)
    ·
      refine ⟨67327473554432331044511599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44884982369621554029674399 67327473554432331044511599)
      ·
        refine ⟨100991210331648496566767399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67327473554432331044511599 100991210331648496566767399)
        ·
          refine ⟨151486815497472744850151099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100991210331648496566767399 151486815497472744850151099)
          ·
            refine ⟨227230223246209117275226649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151486815497472744850151099 227230223246209117275226649)
            ·
              refine ⟨170422667434656837956419987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227230223246209117275226649 170422667434656837956419987)
              ·
                refine ⟨255634001151985256934629981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170422667434656837956419987 255634001151985256934629981)
                ·
                  refine ⟨95862750431994471350486243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255634001151985256934629981 95862750431994471350486243)
                  ·
                    refine ⟨143794125647991707025729365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95862750431994471350486243 143794125647991707025729365)
                    ·
                      refine ⟨842543704968701408353883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 143794125647991707025729365 842543704968701408353883)
                      ·
                        rfl

theorem cell23_1640848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_1640848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640848 prefixEnd_1640848 := by exact prefixLift 1640848
  have htrace : WordTrace (prefixWord ++ tailWord_1640848) baseStart_1640848 baseEnd_1640848 := by
    simpa [prefixWord, tailWord_1640848, baseEnd_1640848] using wordTrace_append hprefix tailTrace_1640848
  have hstable : (prefixWord ++ tailWord_1640848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640848).length < 2 ^ (prefixWord ++ tailWord_1640848).sum := by decide
  have hdescent : baseEnd_1640848 < baseStart_1640848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640900 : List Nat := [2, 3, 3, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_1640900 : Nat := 118140960795 + 1640900 * 2 ^ 59
def prefixEnd_1640900 : Nat := 4983230072969 + 3 ^ 40 * 1640900 * 2
def baseEnd_1640900 : Nat := 842570405962735204903645

theorem tailTrace_1640900 : CollatzResearch.WordTrace tailWord_1640900 prefixEnd_1640900 842570405962735204903645 := by
  unfold tailWord_1640900
  simp only [CollatzResearch.WordTrace]
  refine ⟨29924269877653509126896077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39899026503538012169194769 29924269877653509126896077)
  ·
    refine ⟨11221601204120065922586029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29924269877653509126896077 11221601204120065922586029)
    ·
      refine ⟨4208100451545024720969761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11221601204120065922586029 4208100451545024720969761)
      ·
        refine ⟨3156075338658768540727321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4208100451545024720969761 3156075338658768540727321)
        ·
          refine ⟨2367056503994076405545491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3156075338658768540727321 2367056503994076405545491)
          ·
            refine ⟨3550584755991114608318237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367056503994076405545491 3550584755991114608318237)
            ·
              refine ⟨1331469283496667978119339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3550584755991114608318237 1331469283496667978119339)
              ·
                refine ⟨1997203925245001967179009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331469283496667978119339 1997203925245001967179009)
                ·
                  refine ⟨1497902943933751475384257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1997203925245001967179009 1497902943933751475384257)
                  ·
                    refine ⟨1123427207950313606538193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1497902943933751475384257 1123427207950313606538193)
                    ·
                      refine ⟨842570405962735204903645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1123427207950313606538193 842570405962735204903645)
                      ·
                        rfl

theorem cell23_1640900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_1640900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640900 prefixEnd_1640900 := by exact prefixLift 1640900
  have htrace : WordTrace (prefixWord ++ tailWord_1640900) baseStart_1640900 baseEnd_1640900 := by
    simpa [prefixWord, tailWord_1640900, baseEnd_1640900] using wordTrace_append hprefix tailTrace_1640900
  have hstable : (prefixWord ++ tailWord_1640900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640900).length < 2 ^ (prefixWord ++ tailWord_1640900).sum := by decide
  have hdescent : baseEnd_1640900 < baseStart_1640900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640905 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 1, 3, 4]
def baseStart_1640905 : Nat := 118140960795 + 1640905 * 2 ^ 59
def prefixEnd_1640905 : Nat := 4983230072969 + 3 ^ 40 * 1640905 * 2
def baseEnd_1640905 : Nat := 842572973366007685341121

theorem tailTrace_1640905 : CollatzResearch.WordTrace tailWord_1640905 prefixEnd_1640905 842572973366007685341121 := by
  unfold tailWord_1640905
  simp only [CollatzResearch.WordTrace]
  refine ⟨59848722120288904107724169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39899148080192602738482779 59848722120288904107724169)
  ·
    refine ⟨44886541590216678080793127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59848722120288904107724169 44886541590216678080793127)
    ·
      refine ⟨67329812385325017121189691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44886541590216678080793127 67329812385325017121189691)
      ·
        refine ⟨100994718577987525681784537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67329812385325017121189691 100994718577987525681784537)
        ·
          refine ⟨75746038933490644261338403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100994718577987525681784537 75746038933490644261338403)
          ·
            refine ⟨113619058400235966392007605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75746038933490644261338403 113619058400235966392007605)
            ·
              refine ⟨10651786725022121849250713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113619058400235966392007605 10651786725022121849250713)
              ·
                refine ⟨7988840043766591386938035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10651786725022121849250713 7988840043766591386938035)
                ·
                  refine ⟨11983260065649887080407053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7988840043766591386938035 11983260065649887080407053)
                  ·
                    refine ⟨4493722524618707655152645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11983260065649887080407053 4493722524618707655152645)
                    ·
                      refine ⟨842572973366007685341121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4493722524618707655152645 842572973366007685341121)
                      ·
                        rfl

theorem cell23_1640905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_1640905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640905 prefixEnd_1640905 := by exact prefixLift 1640905
  have htrace : WordTrace (prefixWord ++ tailWord_1640905) baseStart_1640905 baseEnd_1640905 := by
    simpa [prefixWord, tailWord_1640905, baseEnd_1640905] using wordTrace_append hprefix tailTrace_1640905
  have hstable : (prefixWord ++ tailWord_1640905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640905).length < 2 ^ (prefixWord ++ tailWord_1640905).sum := by decide
  have hdescent : baseEnd_1640905 < baseStart_1640905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640922 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4]
def baseStart_1640922 : Nat := 118140960795 + 1640922 * 2 ^ 59
def prefixEnd_1640922 : Nat := 4983230072969 + 3 ^ 40 * 1640922 * 2
def baseEnd_1640922 : Nat := 842581702537134118828543

theorem tailTrace_1640922 : CollatzResearch.WordTrace tailWord_1640922 prefixEnd_1640922 842581702537134118828543 := by
  unfold tailWord_1640922
  simp only [CollatzResearch.WordTrace]
  refine ⟨14962335540306829002773255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39899561440818210674062013 14962335540306829002773255)
  ·
    refine ⟨22443503310460243504159883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14962335540306829002773255 22443503310460243504159883)
    ·
      refine ⟨33665254965690365256239825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22443503310460243504159883 33665254965690365256239825)
      ·
        refine ⟨25248941224267773942179869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33665254965690365256239825 25248941224267773942179869)
        ·
          refine ⟨9468352959100415228317451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25248941224267773942179869 9468352959100415228317451)
          ·
            refine ⟨14202529438650622842476177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9468352959100415228317451 14202529438650622842476177)
            ·
              refine ⟨10651897078987967131857133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14202529438650622842476177 10651897078987967131857133)
              ·
                refine ⟨3994461404620487674446425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10651897078987967131857133 3994461404620487674446425)
                ·
                  refine ⟨2995846053465365755834819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3994461404620487674446425 2995846053465365755834819)
                  ·
                    refine ⟨4493769080198048633752229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2995846053465365755834819 4493769080198048633752229)
                    ·
                      refine ⟨842581702537134118828543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4493769080198048633752229 842581702537134118828543)
                      ·
                        rfl

theorem cell23_1640922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_1640922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640922 prefixEnd_1640922 := by exact prefixLift 1640922
  have htrace : WordTrace (prefixWord ++ tailWord_1640922) baseStart_1640922 baseEnd_1640922 := by
    simpa [prefixWord, tailWord_1640922, baseEnd_1640922] using wordTrace_append hprefix tailTrace_1640922
  have hstable : (prefixWord ++ tailWord_1640922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640922).length < 2 ^ (prefixWord ++ tailWord_1640922).sum := by decide
  have hdescent : baseEnd_1640922 < baseStart_1640922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640945 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 8]
def baseStart_1640945 : Nat := 118140960795 + 1640945 * 2 ^ 59
def prefixEnd_1640945 : Nat := 4983230072969 + 3 ^ 40 * 1640945 * 2
def baseEnd_1640945 : Nat := 93621501399131947648993

theorem tailTrace_1640945 : CollatzResearch.WordTrace tailWord_1640945 prefixEnd_1640945 93621501399131947648993 := by
  unfold tailWord_1640945
  simp only [CollatzResearch.WordTrace]
  refine ⟨59850181040143990939180289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39900120693429327292786859 59850181040143990939180289)
  ·
    refine ⟨44887635780107993204385217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59850181040143990939180289 44887635780107993204385217)
    ·
      refine ⟨33665726835080994903288913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44887635780107993204385217 33665726835080994903288913)
      ·
        refine ⟨25249295126310746177466685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33665726835080994903288913 25249295126310746177466685)
        ·
          refine ⟨9468485672366529816550007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25249295126310746177466685 9468485672366529816550007)
          ·
            refine ⟨14202728508549794724825011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9468485672366529816550007 14202728508549794724825011)
            ·
              refine ⟨21304092762824692087237517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14202728508549794724825011 21304092762824692087237517)
              ·
                refine ⟨7989034786059259532714069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21304092762824692087237517 7989034786059259532714069)
                ·
                  refine ⟨93621501399131947648993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7989034786059259532714069 93621501399131947648993)
                  ·
                    rfl

theorem cell23_1640945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 8].length) (baseStart_1640945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640945 prefixEnd_1640945 := by exact prefixLift 1640945
  have htrace : WordTrace (prefixWord ++ tailWord_1640945) baseStart_1640945 baseEnd_1640945 := by
    simpa [prefixWord, tailWord_1640945, baseEnd_1640945] using wordTrace_append hprefix tailTrace_1640945
  have hstable : (prefixWord ++ tailWord_1640945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640945).length < 2 ^ (prefixWord ++ tailWord_1640945).sum := by decide
  have hdescent : baseEnd_1640945 < baseStart_1640945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640965 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_1640965 : Nat := 118140960795 + 1640965 * 2 ^ 59
def prefixEnd_1640965 : Nat := 4983230072969 + 3 ^ 40 * 1640965 * 2
def baseEnd_1640965 : Nat := 842603782205277450590845

theorem tailTrace_1640965 : CollatzResearch.WordTrace tailWord_1640965 prefixEnd_1640965 842603782205277450590845 := by
  unfold tailWord_1640965
  simp only [CollatzResearch.WordTrace]
  refine ⟨59850910500071534354908349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39900607000047689569938899 59850910500071534354908349)
  ·
    refine ⟨22444091437526825383090631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59850910500071534354908349 22444091437526825383090631)
    ·
      refine ⟨33666137156290238074635947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22444091437526825383090631 33666137156290238074635947)
      ·
        refine ⟨50499205734435357111953921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33666137156290238074635947 50499205734435357111953921)
        ·
          refine ⟨37874404300826517833965441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50499205734435357111953921 37874404300826517833965441)
          ·
            refine ⟨28405803225619888375474081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37874404300826517833965441 28405803225619888375474081)
            ·
              refine ⟨21304352419214916281605561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28405803225619888375474081 21304352419214916281605561)
              ·
                refine ⟨15978264314411187211204171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21304352419214916281605561 15978264314411187211204171)
                ·
                  refine ⟨23967396471616780816806257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15978264314411187211204171 23967396471616780816806257)
                  ·
                    refine ⟨17975547353712585612604693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23967396471616780816806257 17975547353712585612604693)
                    ·
                      refine ⟨842603782205277450590845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17975547353712585612604693 842603782205277450590845)
                      ·
                        rfl

theorem cell23_1640965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_1640965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640965 prefixEnd_1640965 := by exact prefixLift 1640965
  have htrace : WordTrace (prefixWord ++ tailWord_1640965) baseStart_1640965 baseEnd_1640965 := by
    simpa [prefixWord, tailWord_1640965, baseEnd_1640965] using wordTrace_append hprefix tailTrace_1640965
  have hstable : (prefixWord ++ tailWord_1640965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640965).length < 2 ^ (prefixWord ++ tailWord_1640965).sum := by decide
  have hdescent : baseEnd_1640965 < baseStart_1640965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640973 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1640973 : Nat := 118140960795 + 1640973 * 2 ^ 59
def prefixEnd_1640973 : Nat := 4983230072969 + 3 ^ 40 * 1640973 * 2
def baseEnd_1640973 : Nat := 842607890050513419290809

theorem tailTrace_1640973 : CollatzResearch.WordTrace tailWord_1640973 prefixEnd_1640973 842607890050513419290809 := by
  unfold tailWord_1640973
  simp only [CollatzResearch.WordTrace]
  refine ⟨59851202284042551721199573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39900801522695034480799715 59851202284042551721199573)
  ·
    refine ⟨1402762553532247305965615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 59851202284042551721199573 1402762553532247305965615)
    ·
      refine ⟨2104143830298370958948423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1402762553532247305965615 2104143830298370958948423)
      ·
        refine ⟨3156215745447556438422635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2104143830298370958948423 3156215745447556438422635)
        ·
          refine ⟨4734323618171334657633953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3156215745447556438422635 4734323618171334657633953)
          ·
            refine ⟨3550742713628500993225465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4734323618171334657633953 3550742713628500993225465)
            ·
              refine ⟨2663057035221375744919099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3550742713628500993225465 2663057035221375744919099)
              ·
                refine ⟨3994585552832063617378649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2663057035221375744919099 3994585552832063617378649)
                ·
                  refine ⟨2995939164624047713033987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3994585552832063617378649 2995939164624047713033987)
                  ·
                    refine ⟨4493908746936071569550981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2995939164624047713033987 4493908746936071569550981)
                    ·
                      refine ⟨842607890050513419290809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4493908746936071569550981 842607890050513419290809)
                      ·
                        rfl

theorem cell23_1640973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1640973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640973 prefixEnd_1640973 := by exact prefixLift 1640973
  have htrace : WordTrace (prefixWord ++ tailWord_1640973) baseStart_1640973 baseEnd_1640973 := by
    simpa [prefixWord, tailWord_1640973, baseEnd_1640973] using wordTrace_append hprefix tailTrace_1640973
  have hstable : (prefixWord ++ tailWord_1640973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640973).length < 2 ^ (prefixWord ++ tailWord_1640973).sum := by decide
  have hdescent : baseEnd_1640973 < baseStart_1640973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1640996 : List Nat := [2, 3, 1, 5, 1, 1, 2, 2, 6]
def baseStart_1640996 : Nat := 118140960795 + 1640996 * 2 ^ 59
def prefixEnd_1640996 : Nat := 4983230072969 + 3 ^ 40 * 1640996 * 2
def baseEnd_1640996 : Nat := 93624411122840758811467

theorem tailTrace_1640996 : CollatzResearch.WordTrace tailWord_1640996 prefixEnd_1640996 93624411122840758811467 := by
  unfold tailWord_1640996
  simp only [CollatzResearch.WordTrace]
  refine ⟨29926020581479613324643421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39901360775306151099524561 29926020581479613324643421)
  ·
    refine ⟨11222257718054854996741283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29926020581479613324643421 11222257718054854996741283)
    ·
      refine ⟨16833386577082282495111925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11222257718054854996741283 16833386577082282495111925)
      ·
        refine ⟨1578129991601463983916743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16833386577082282495111925 1578129991601463983916743)
        ·
          refine ⟨2367194987402195975875115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578129991601463983916743 2367194987402195975875115)
          ·
            refine ⟨3550792481103293963812673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367194987402195975875115 3550792481103293963812673)
            ·
              refine ⟨2663094360827470472859505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3550792481103293963812673 2663094360827470472859505)
              ·
                refine ⟨1997320770620602854644629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2663094360827470472859505 1997320770620602854644629)
                ·
                  refine ⟨93624411122840758811467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1997320770620602854644629 93624411122840758811467)
                  ·
                    rfl

theorem cell23_1640996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_1640996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1640996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1640996 prefixEnd_1640996 := by exact prefixLift 1640996
  have htrace : WordTrace (prefixWord ++ tailWord_1640996) baseStart_1640996 baseEnd_1640996 := by
    simpa [prefixWord, tailWord_1640996, baseEnd_1640996] using wordTrace_append hprefix tailTrace_1640996
  have hstable : (prefixWord ++ tailWord_1640996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1640996).length < 2 ^ (prefixWord ++ tailWord_1640996).sum := by decide
  have hdescent : baseEnd_1640996 < baseStart_1640996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1640996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641000 : List Nat := [2, 1, 5, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1641000 : Nat := 118140960795 + 1641000 * 2 ^ 59
def prefixEnd_1641000 : Nat := 4983230072969 + 3 ^ 40 * 1641000 * 2
def baseEnd_1641000 : Nat := 280873918009394937884395

theorem tailTrace_1641000 : CollatzResearch.WordTrace tailWord_1641000 prefixEnd_1641000 280873918009394937884395 := by
  unfold tailWord_1641000
  simp only [CollatzResearch.WordTrace]
  refine ⟨29926093527472367666216227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39901458036629823554954969 29926093527472367666216227)
  ·
    refine ⟨44889140291208551499324341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29926093527472367666216227 44889140291208551499324341)
    ·
      refine ⟨4208356902300801703061657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44889140291208551499324341 4208356902300801703061657)
      ·
        refine ⟨3156267676725601277296243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4208356902300801703061657 3156267676725601277296243)
        ·
          refine ⟨4734401515088401915944365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3156267676725601277296243 4734401515088401915944365)
          ·
            refine ⟨1775400568158150718479137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4734401515088401915944365 1775400568158150718479137)
            ·
              refine ⟨1331550426118613038859353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1775400568158150718479137 1331550426118613038859353)
              ·
                refine ⟨998662819588959779144515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1331550426118613038859353 998662819588959779144515)
                ·
                  refine ⟨1497994229383439668716773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998662819588959779144515 1497994229383439668716773)
                  ·
                    refine ⟨280873918009394937884395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1497994229383439668716773 280873918009394937884395)
                    ·
                      rfl

theorem cell23_1641000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1641000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641000 prefixEnd_1641000 := by exact prefixLift 1641000
  have htrace : WordTrace (prefixWord ++ tailWord_1641000) baseStart_1641000 baseEnd_1641000 := by
    simpa [prefixWord, tailWord_1641000, baseEnd_1641000] using wordTrace_append hprefix tailTrace_1641000
  have hstable : (prefixWord ++ tailWord_1641000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641000).length < 2 ^ (prefixWord ++ tailWord_1641000).sum := by decide
  have hdescent : baseEnd_1641000 < baseStart_1641000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641035 : List Nat := [1, 1, 1, 1, 3, 1, 4, 11]
def baseStart_1641035 : Nat := 118140960795 + 1641035 * 2 ^ 59
def prefixEnd_1641035 : Nat := 4983230072969 + 3 ^ 40 * 1641035 * 2
def baseEnd_1641035 : Nat := 31208878735225636174649

theorem tailTrace_1641035 : CollatzResearch.WordTrace tailWord_1641035 prefixEnd_1641035 31208878735225636174649 := by
  unfold tailWord_1641035
  simp only [CollatzResearch.WordTrace]
  refine ⟨59853463609817936309956559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39902309073211957539971039 59853463609817936309956559)
  ·
    refine ⟨89780195414726904464934839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59853463609817936309956559 89780195414726904464934839)
    ·
      refine ⟨134670293122090356697402259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89780195414726904464934839 134670293122090356697402259)
      ·
        refine ⟨202005439683135535046103389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134670293122090356697402259 202005439683135535046103389)
        ·
          refine ⟨75752039881175825642288771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202005439683135535046103389 75752039881175825642288771)
          ·
            refine ⟨113628059821763738463433157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75752039881175825642288771 113628059821763738463433157)
            ·
              refine ⟨21305261216580700961893717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113628059821763738463433157 21305261216580700961893717)
              ·
                refine ⟨31208878735225636174649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 21305261216580700961893717 31208878735225636174649)
                ·
                  rfl

theorem cell23_1641035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 11].length) (baseStart_1641035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641035 prefixEnd_1641035 := by exact prefixLift 1641035
  have htrace : WordTrace (prefixWord ++ tailWord_1641035) baseStart_1641035 baseEnd_1641035 := by
    simpa [prefixWord, tailWord_1641035, baseEnd_1641035] using wordTrace_append hprefix tailTrace_1641035
  have hstable : (prefixWord ++ tailWord_1641035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641035).length < 2 ^ (prefixWord ++ tailWord_1641035).sum := by decide
  have hdescent : baseEnd_1641035 < baseStart_1641035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641079 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 3]
def baseStart_1641079 : Nat := 118140960795 + 1641079 * 2 ^ 59
def prefixEnd_1641079 : Nat := 4983230072969 + 3 ^ 40 * 1641079 * 2
def baseEnd_1641079 : Nat := 842662318999890004565321

theorem tailTrace_1641079 : CollatzResearch.WordTrace tailWord_1641079 prefixEnd_1641079 842662318999890004565321 := by
  unfold tailWord_1641079
  simp only [CollatzResearch.WordTrace]
  refine ⟨59855068421658531824558291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39903378947772354549705527 59855068421658531824558291)
  ·
    refine ⟨89782602632487797736837437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59855068421658531824558291 89782602632487797736837437)
    ·
      refine ⟨33668475987182924151314039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89782602632487797736837437 33668475987182924151314039)
      ·
        refine ⟨50502713980774386226971059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33668475987182924151314039 50502713980774386226971059)
        ·
          refine ⟨75754070971161579340456589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50502713980774386226971059 75754070971161579340456589)
          ·
            refine ⟨28407776614185592252671221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75754070971161579340456589 28407776614185592252671221)
            ·
              refine ⟨2663229057579899273687927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28407776614185592252671221 2663229057579899273687927)
              ·
                refine ⟨3994843586369848910531891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2663229057579899273687927 3994843586369848910531891)
                ·
                  refine ⟨5992265379554773365797837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3994843586369848910531891 5992265379554773365797837)
                  ·
                    refine ⟨2247099517333040012174189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5992265379554773365797837 2247099517333040012174189)
                    ·
                      refine ⟨842662318999890004565321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2247099517333040012174189 842662318999890004565321)
                      ·
                        rfl

theorem cell23_1641079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_1641079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641079 prefixEnd_1641079 := by exact prefixLift 1641079
  have htrace : WordTrace (prefixWord ++ tailWord_1641079) baseStart_1641079 baseEnd_1641079 := by
    simpa [prefixWord, tailWord_1641079, baseEnd_1641079] using wordTrace_append hprefix tailTrace_1641079
  have hstable : (prefixWord ++ tailWord_1641079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641079).length < 2 ^ (prefixWord ++ tailWord_1641079).sum := by decide
  have hdescent : baseEnd_1641079 < baseStart_1641079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641114 : List Nat := [3, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2]
def baseStart_1641114 : Nat := 118140960795 + 1641114 * 2 ^ 59
def prefixEnd_1641114 : Nat := 4983230072969 + 3 ^ 40 * 1641114 * 2
def baseEnd_1641114 : Nat := 842680290822797367627661

theorem tailTrace_1641114 : CollatzResearch.WordTrace tailWord_1641114 prefixEnd_1641114 842680290822797367627661 := by
  unfold tailWord_1641114
  simp only [CollatzResearch.WordTrace]
  refine ⟨14964086244132933200520599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39904229984354488534721597 14964086244132933200520599)
  ·
    refine ⟨22446129366199399800780899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14964086244132933200520599 22446129366199399800780899)
    ·
      refine ⟨33669194049299099701171349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22446129366199399800780899 33669194049299099701171349)
      ·
        refine ⟨1578243471060895298492407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33669194049299099701171349 1578243471060895298492407)
        ·
          refine ⟨2367365206591342947738611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578243471060895298492407 2367365206591342947738611)
          ·
            refine ⟨3551047809887014421607917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367365206591342947738611 3551047809887014421607917)
            ·
              refine ⟨1331642928707630408102969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3551047809887014421607917 1331642928707630408102969)
              ·
                refine ⟨998732196530722806077227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1331642928707630408102969 998732196530722806077227)
                ·
                  refine ⟨1498098294796084209115841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 998732196530722806077227 1498098294796084209115841)
                  ·
                    refine ⟨1123573721097063156836881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1498098294796084209115841 1123573721097063156836881)
                    ·
                      refine ⟨842680290822797367627661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1123573721097063156836881 842680290822797367627661)
                      ·
                        rfl

theorem cell23_1641114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_1641114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641114 prefixEnd_1641114 := by exact prefixLift 1641114
  have htrace : WordTrace (prefixWord ++ tailWord_1641114) baseStart_1641114 baseEnd_1641114 := by
    simpa [prefixWord, tailWord_1641114, baseEnd_1641114] using wordTrace_append hprefix tailTrace_1641114
  have hstable : (prefixWord ++ tailWord_1641114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641114).length < 2 ^ (prefixWord ++ tailWord_1641114).sum := by decide
  have hdescent : baseEnd_1641114 < baseStart_1641114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641169 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 2, 3, 3]
def baseStart_1641169 : Nat := 118140960795 + 1641169 * 2 ^ 59
def prefixEnd_1641169 : Nat := 4983230072969 + 3 ^ 40 * 1641169 * 2
def baseEnd_1641169 : Nat := 842708532258794652439907

theorem tailTrace_1641169 : CollatzResearch.WordTrace tailWord_1641169 prefixEnd_1641169 842708532258794652439907 := by
  unfold tailWord_1641169
  simp only [CollatzResearch.WordTrace]
  refine ⟨59858350991332477195334561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39905567327554984796889707 59858350991332477195334561)
  ·
    refine ⟨44893763243499357896500921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59858350991332477195334561 44893763243499357896500921)
    ·
      refine ⟨33670322432624518422375691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44893763243499357896500921 33670322432624518422375691)
      ·
        refine ⟨50505483648936777633563537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33670322432624518422375691 50505483648936777633563537)
        ·
          refine ⟨37879112736702583225172653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50505483648936777633563537 37879112736702583225172653)
          ·
            refine ⟨14204667276263468709439745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37879112736702583225172653 14204667276263468709439745)
            ·
              refine ⟨10653500457197601532079809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14204667276263468709439745 10653500457197601532079809)
              ·
                refine ⟨7990125342898201149059857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10653500457197601532079809 7990125342898201149059857)
                ·
                  refine ⟨5992594007173650861794893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7990125342898201149059857 5992594007173650861794893)
                  ·
                    refine ⟨2247222752690119073173085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5992594007173650861794893 2247222752690119073173085)
                    ·
                      refine ⟨842708532258794652439907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2247222752690119073173085 842708532258794652439907)
                      ·
                        rfl

theorem cell23_1641169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_1641169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641169 prefixEnd_1641169 := by exact prefixLift 1641169
  have htrace : WordTrace (prefixWord ++ tailWord_1641169) baseStart_1641169 baseEnd_1641169 := by
    simpa [prefixWord, tailWord_1641169, baseEnd_1641169] using wordTrace_append hprefix tailTrace_1641169
  have hstable : (prefixWord ++ tailWord_1641169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641169).length < 2 ^ (prefixWord ++ tailWord_1641169).sum := by decide
  have hdescent : baseEnd_1641169 < baseStart_1641169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641176 : List Nat := [2, 1, 2, 2, 3, 3, 1, 4, 5]
def baseStart_1641176 : Nat := 118140960795 + 1641176 * 2 ^ 59
def prefixEnd_1641176 : Nat := 4983230072969 + 3 ^ 40 * 1641176 * 2
def baseEnd_1641176 : Nat := 93634680735930680561375

theorem tailTrace_1641176 : CollatzResearch.WordTrace tailWord_1641176 prefixEnd_1641176 93634680735930680561375 := by
  unfold tailWord_1641176
  simp only [CollatzResearch.WordTrace]
  refine ⟨29929303151153558695419691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39905737534871411593892921 29929303151153558695419691)
  ·
    refine ⟨44893954726730338043129537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29929303151153558695419691 44893954726730338043129537)
    ·
      refine ⟨33670466045047753532347153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44893954726730338043129537 33670466045047753532347153)
      ·
        refine ⟨25252849533785815149260365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33670466045047753532347153 25252849533785815149260365)
        ·
          refine ⟨9469818575169680680972637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25252849533785815149260365 9469818575169680680972637)
          ·
            refine ⟨3551181965688630255364739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9469818575169680680972637 3551181965688630255364739)
            ·
              refine ⟨5326772948532945383047109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3551181965688630255364739 5326772948532945383047109)
              ·
                refine ⟨998769927849927259321333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5326772948532945383047109 998769927849927259321333)
                ·
                  refine ⟨93634680735930680561375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 998769927849927259321333 93634680735930680561375)
                  ·
                    rfl

theorem cell23_1641176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 5].length) (baseStart_1641176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641176 prefixEnd_1641176 := by exact prefixLift 1641176
  have htrace : WordTrace (prefixWord ++ tailWord_1641176) baseStart_1641176 baseEnd_1641176 := by
    simpa [prefixWord, tailWord_1641176, baseEnd_1641176] using wordTrace_append hprefix tailTrace_1641176
  have hstable : (prefixWord ++ tailWord_1641176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641176).length < 2 ^ (prefixWord ++ tailWord_1641176).sum := by decide
  have hdescent : baseEnd_1641176 < baseStart_1641176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641219 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 7, 4]
def baseStart_1641219 : Nat := 118140960795 + 1641219 * 2 ^ 59
def prefixEnd_1641219 : Nat := 4983230072969 + 3 ^ 40 * 1641219 * 2
def baseEnd_1641219 : Nat := 280911402097173152271559

theorem tailTrace_1641219 : CollatzResearch.WordTrace tailWord_1641219 prefixEnd_1641219 280911402097173152271559 := by
  unfold tailWord_1641219
  simp only [CollatzResearch.WordTrace]
  refine ⟨59860174641151335734654711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39906783094100890489769807 59860174641151335734654711)
  ·
    refine ⟨89790261961727003601982067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59860174641151335734654711 89790261961727003601982067)
    ·
      refine ⟨134685392942590505402973101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89790261961727003601982067 134685392942590505402973101)
      ·
        refine ⟨50507022353471439526114913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134685392942590505402973101 50507022353471439526114913)
        ·
          refine ⟨37880266765103579644586185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50507022353471439526114913 37880266765103579644586185)
          ·
            refine ⟨28410200073827684733439639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37880266765103579644586185 28410200073827684733439639)
            ·
              refine ⟨42615300110741527100159459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28410200073827684733439639 42615300110741527100159459)
              ·
                refine ⟨63922950166112290650239189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42615300110741527100159459 63922950166112290650239189)
                ·
                  refine ⟨1498194144518256812114981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 63922950166112290650239189 1498194144518256812114981)
                  ·
                    refine ⟨280911402097173152271559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1498194144518256812114981 280911402097173152271559)
                    ·
                      rfl

theorem cell23_1641219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 4].length) (baseStart_1641219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641219 prefixEnd_1641219 := by exact prefixLift 1641219
  have htrace : WordTrace (prefixWord ++ tailWord_1641219) baseStart_1641219 baseEnd_1641219 := by
    simpa [prefixWord, tailWord_1641219, baseEnd_1641219] using wordTrace_append hprefix tailTrace_1641219
  have hstable : (prefixWord ++ tailWord_1641219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641219).length < 2 ^ (prefixWord ++ tailWord_1641219).sum := by decide
  have hdescent : baseEnd_1641219 < baseStart_1641219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641226 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 4, 4, 2]
def baseStart_1641226 : Nat := 118140960795 + 1641226 * 2 ^ 59
def prefixEnd_1641226 : Nat := 4983230072969 + 3 ^ 40 * 1641226 * 2
def baseEnd_1641226 : Nat := 842737800656100929427145

theorem tailTrace_1641226 : CollatzResearch.WordTrace tailWord_1641226 prefixEnd_1641226 842737800656100929427145 := by
  unfold tailWord_1641226
  simp only [CollatzResearch.WordTrace]
  refine ⟨14965107488031493982539883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39906953301417317286773021 14965107488031493982539883)
  ·
    refine ⟨22447661232047240973809825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14965107488031493982539883 22447661232047240973809825)
    ·
      refine ⟨16835745924035430730357369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22447661232047240973809825 16835745924035430730357369)
      ·
        refine ⟨12626809443026573047768027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16835745924035430730357369 12626809443026573047768027)
        ·
          refine ⟨18940214164539859571652041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12626809443026573047768027 18940214164539859571652041)
          ·
            refine ⟨14205160623404894678739031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18940214164539859571652041 14205160623404894678739031)
            ·
              refine ⟨21307740935107342018108547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14205160623404894678739031 21307740935107342018108547)
              ·
                refine ⟨31961611402661013027162821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21307740935107342018108547 31961611402661013027162821)
                ·
                  refine ⟨5992802137998939942593029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31961611402661013027162821 5992802137998939942593029)
                  ·
                    refine ⟨1123650400874801239236193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5992802137998939942593029 1123650400874801239236193)
                    ·
                      refine ⟨842737800656100929427145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1123650400874801239236193 842737800656100929427145)
                      ·
                        rfl

theorem cell23_1641226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_1641226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641226 prefixEnd_1641226 := by exact prefixLift 1641226
  have htrace : WordTrace (prefixWord ++ tailWord_1641226) baseStart_1641226 baseEnd_1641226 := by
    simpa [prefixWord, tailWord_1641226, baseEnd_1641226] using wordTrace_append hprefix tailTrace_1641226
  have hstable : (prefixWord ++ tailWord_1641226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641226).length < 2 ^ (prefixWord ++ tailWord_1641226).sum := by decide
  have hdescent : baseEnd_1641226 < baseStart_1641226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641300 : List Nat := [2, 4, 1, 1, 4, 2, 2, 1, 6]
def baseStart_1641300 : Nat := 118140960795 + 1641300 * 2 ^ 59
def prefixEnd_1641300 : Nat := 4983230072969 + 3 ^ 40 * 1641300 * 2
def baseEnd_1641300 : Nat := 93641755358281515544645

theorem tailTrace_1641300 : CollatzResearch.WordTrace tailWord_1641300 prefixEnd_1641300 93641755358281515544645 := by
  unfold tailWord_1641300
  simp only [CollatzResearch.WordTrace]
  refine ⟨29931564476928943284176677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39908752635905257712235569 29931564476928943284176677)
  ·
    refine ⟨5612168339424176865783127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29931564476928943284176677 5612168339424176865783127)
    ·
      refine ⟨8418252509136265298674691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5612168339424176865783127 8418252509136265298674691)
      ·
        refine ⟨12627378763704397948012037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8418252509136265298674691 12627378763704397948012037)
        ·
          refine ⟨2367633518194574615252257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12627378763704397948012037 2367633518194574615252257)
          ·
            refine ⟨1775725138645930961439193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2367633518194574615252257 1775725138645930961439193)
            ·
              refine ⟨1331793853984448221079395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1775725138645930961439193 1331793853984448221079395)
              ·
                refine ⟨1997690780976672331619093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331793853984448221079395 1997690780976672331619093)
                ·
                  refine ⟨93641755358281515544645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1997690780976672331619093 93641755358281515544645)
                  ·
                    rfl

theorem cell23_1641300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_1641300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641300 prefixEnd_1641300 := by exact prefixLift 1641300
  have htrace : WordTrace (prefixWord ++ tailWord_1641300) baseStart_1641300 baseEnd_1641300 := by
    simpa [prefixWord, tailWord_1641300, baseEnd_1641300] using wordTrace_append hprefix tailTrace_1641300
  have hstable : (prefixWord ++ tailWord_1641300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641300).length < 2 ^ (prefixWord ++ tailWord_1641300).sum := by decide
  have hdescent : baseEnd_1641300 < baseStart_1641300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641320 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_1641320 : Nat := 118140960795 + 1641320 * 2 ^ 59
def prefixEnd_1641320 : Nat := 4983230072969 + 3 ^ 40 * 1641320 * 2
def baseEnd_1641320 : Nat := 842786067837623561651713

theorem tailTrace_1641320 : CollatzResearch.WordTrace tailWord_1641320 prefixEnd_1641320 842786067837623561651713 := by
  unfold tailWord_1641320
  simp only [CollatzResearch.WordTrace]
  refine ⟨29931929206892714992040707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39909238942523619989387609 29931929206892714992040707)
  ·
    refine ⟨44897893810339072488061061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29931929206892714992040707 44897893810339072488061061)
    ·
      refine ⟨8418355089438576091511449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44897893810339072488061061 8418355089438576091511449)
      ·
        refine ⟨6313766317078932068633587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8418355089438576091511449 6313766317078932068633587)
        ·
          refine ⟨9470649475618398102950381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6313766317078932068633587 9470649475618398102950381)
          ·
            refine ⟨3551493553356899288606393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9470649475618398102950381 3551493553356899288606393)
            ·
              refine ⟨2663620165017674466454795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3551493553356899288606393 2663620165017674466454795)
              ·
                refine ⟨3995430247526511699682193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2663620165017674466454795 3995430247526511699682193)
                ·
                  refine ⟨2996572685644883774761645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3995430247526511699682193 2996572685644883774761645)
                  ·
                    refine ⟨1123714757116831415535617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2996572685644883774761645 1123714757116831415535617)
                    ·
                      refine ⟨842786067837623561651713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1123714757116831415535617 842786067837623561651713)
                      ·
                        rfl

theorem cell23_1641320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_1641320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641320 prefixEnd_1641320 := by exact prefixLift 1641320
  have htrace : WordTrace (prefixWord ++ tailWord_1641320) baseStart_1641320 baseEnd_1641320 := by
    simpa [prefixWord, tailWord_1641320, baseEnd_1641320] using wordTrace_append hprefix tailTrace_1641320
  have hstable : (prefixWord ++ tailWord_1641320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641320).length < 2 ^ (prefixWord ++ tailWord_1641320).sum := by decide
  have hdescent : baseEnd_1641320 < baseStart_1641320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641369 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 4, 7]
def baseStart_1641369 : Nat := 118140960795 + 1641369 * 2 ^ 59
def prefixEnd_1641369 : Nat := 4983230072969 + 3 ^ 40 * 1641369 * 2
def baseEnd_1641369 : Nat := 280937076129897956646329

theorem tailTrace_1641369 : CollatzResearch.WordTrace tailWord_1641369 prefixEnd_1641369 280937076129897956646329 := by
  unfold tailWord_1641369
  simp only [CollatzResearch.WordTrace]
  refine ⟨59865645590607911352615161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39910430393738607568410107 59865645590607911352615161)
  ·
    refine ⟨44899234192955933514461371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59865645590607911352615161 44899234192955933514461371)
    ·
      refine ⟨67348851289433900271692057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44899234192955933514461371 67348851289433900271692057)
      ·
        refine ⟨50511638467075425203769043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67348851289433900271692057 50511638467075425203769043)
        ·
          refine ⟨75767457700613137805653565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50511638467075425203769043 75767457700613137805653565)
          ·
            refine ⟨28412796637729926677120087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75767457700613137805653565 28412796637729926677120087)
            ·
              refine ⟨42619194956594890015680131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28412796637729926677120087 42619194956594890015680131)
              ·
                refine ⟨63928792434892335023520197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42619194956594890015680131 63928792434892335023520197)
                ·
                  refine ⟨11986648581542312816910037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63928792434892335023520197 11986648581542312816910037)
                  ·
                    refine ⟨280937076129897956646329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11986648581542312816910037 280937076129897956646329)
                    ·
                      rfl

theorem cell23_1641369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_1641369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641369 prefixEnd_1641369 := by exact prefixLift 1641369
  have htrace : WordTrace (prefixWord ++ tailWord_1641369) baseStart_1641369 baseEnd_1641369 := by
    simpa [prefixWord, tailWord_1641369, baseEnd_1641369] using wordTrace_append hprefix tailTrace_1641369
  have hstable : (prefixWord ++ tailWord_1641369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641369).length < 2 ^ (prefixWord ++ tailWord_1641369).sum := by decide
  have hdescent : baseEnd_1641369 < baseStart_1641369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641400 : List Nat := [2, 1, 2, 1, 2, 4, 3, 2, 2, 1, 3]
def baseStart_1641400 : Nat := 118140960795 + 1641400 * 2 ^ 59
def prefixEnd_1641400 : Nat := 4983230072969 + 3 ^ 40 * 1641400 * 2
def baseEnd_1641400 : Nat := 842827146289983248651345

theorem tailTrace_1641400 : CollatzResearch.WordTrace tailWord_1641400 prefixEnd_1641400 842827146289983248651345 := by
  unfold tailWord_1641400
  simp only [CollatzResearch.WordTrace]
  refine ⟨29933388126747801823496827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39911184168997069097995769 29933388126747801823496827)
  ·
    refine ⟨44900082190121702735245241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29933388126747801823496827 44900082190121702735245241)
    ·
      refine ⟨33675061642591277051433931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44900082190121702735245241 33675061642591277051433931)
      ·
        refine ⟨50512592463886915577150897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33675061642591277051433931 50512592463886915577150897)
        ·
          refine ⟨37884444347915186682863173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50512592463886915577150897 37884444347915186682863173)
          ·
            refine ⟨7103333315234097503036845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37884444347915186682863173 7103333315234097503036845)
            ·
              refine ⟨2663749993212786563638817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7103333315234097503036845 2663749993212786563638817)
              ·
                refine ⟨1997812494909589922729113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2663749993212786563638817 1997812494909589922729113)
                ·
                  refine ⟨1498359371182192442046835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1997812494909589922729113 1498359371182192442046835)
                  ·
                    refine ⟨2247539056773288663070253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1498359371182192442046835 2247539056773288663070253)
                    ·
                      refine ⟨842827146289983248651345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2247539056773288663070253 842827146289983248651345)
                      ·
                        rfl

theorem cell23_1641400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_1641400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641400 prefixEnd_1641400 := by exact prefixLift 1641400
  have htrace : WordTrace (prefixWord ++ tailWord_1641400) baseStart_1641400 baseEnd_1641400 := by
    simpa [prefixWord, tailWord_1641400, baseEnd_1641400] using wordTrace_append hprefix tailTrace_1641400
  have hstable : (prefixWord ++ tailWord_1641400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641400).length < 2 ^ (prefixWord ++ tailWord_1641400).sum := by decide
  have hdescent : baseEnd_1641400 < baseStart_1641400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641414 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1641414 : Nat := 118140960795 + 1641414 * 2 ^ 59
def prefixEnd_1641414 : Nat := 4983230072969 + 3 ^ 40 * 1641414 * 2
def baseEnd_1641414 : Nat := 842834335019146193876281

theorem tailTrace_1641414 : CollatzResearch.WordTrace tailWord_1641414 prefixEnd_1641414 842834335019146193876281 := by
  unfold tailWord_1641414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1870852714857652626187603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39911524583629922692002197 1870852714857652626187603)
  ·
    refine ⟨2806279072286478939281405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1870852714857652626187603 2806279072286478939281405)
    ·
      refine ⟨1052354652107429602230527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2806279072286478939281405 1052354652107429602230527)
      ·
        refine ⟨1578531978161144403345791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1052354652107429602230527 1578531978161144403345791)
        ·
          refine ⟨2367797967241716605018687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578531978161144403345791 2367797967241716605018687)
          ·
            refine ⟨3551696950862574907528031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367797967241716605018687 3551696950862574907528031)
            ·
              refine ⟨5327545426293862361292047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3551696950862574907528031 5327545426293862361292047)
              ·
                refine ⟨7991318139440793541938071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5327545426293862361292047 7991318139440793541938071)
                ·
                  refine ⟨11986977209161190312907107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7991318139440793541938071 11986977209161190312907107)
                  ·
                    refine ⟨17980465813741785469360661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11986977209161190312907107 17980465813741785469360661)
                    ·
                      refine ⟨842834335019146193876281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17980465813741785469360661 842834335019146193876281)
                      ·
                        rfl

theorem cell23_1641414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1641414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641414 prefixEnd_1641414 := by exact prefixLift 1641414
  have htrace : WordTrace (prefixWord ++ tailWord_1641414) baseStart_1641414 baseEnd_1641414 := by
    simpa [prefixWord, tailWord_1641414, baseEnd_1641414] using wordTrace_append hprefix tailTrace_1641414
  have hstable : (prefixWord ++ tailWord_1641414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641414).length < 2 ^ (prefixWord ++ tailWord_1641414).sum := by decide
  have hdescent : baseEnd_1641414 < baseStart_1641414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641421 : List Nat := [1, 6, 3, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1641421 : Nat := 118140960795 + 1641421 * 2 ^ 59
def prefixEnd_1641421 : Nat := 4983230072969 + 3 ^ 40 * 1641421 * 2
def baseEnd_1641421 : Nat := 842837929383727666488749

theorem tailTrace_1641421 : CollatzResearch.WordTrace tailWord_1641421 prefixEnd_1641421 842837929383727666488749 := by
  unfold tailWord_1641421
  simp only [CollatzResearch.WordTrace]
  refine ⟨59867542186419524233508117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39911694790946349489005411 59867542186419524233508117)
  ·
    refine ⟨2806291039988415198445693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59867542186419524233508117 2806291039988415198445693)
    ·
      refine ⟨1052359139995655699417135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2806291039988415198445693 1052359139995655699417135)
      ·
        refine ⟨1578538709993483549125703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1052359139995655699417135 1578538709993483549125703)
        ·
          refine ⟨2367808064990225323688555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578538709993483549125703 2367808064990225323688555)
          ·
            refine ⟨3551712097485337985532833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367808064990225323688555 3551712097485337985532833)
            ·
              refine ⟨2663784073114003489149625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3551712097485337985532833 2663784073114003489149625)
              ·
                refine ⟨1997838054835502616862219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2663784073114003489149625 1997838054835502616862219)
                ·
                  refine ⟨2996757082253253925293329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1997838054835502616862219 2996757082253253925293329)
                  ·
                    refine ⟨2247567811689940443969997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2996757082253253925293329 2247567811689940443969997)
                    ·
                      refine ⟨842837929383727666488749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2247567811689940443969997 842837929383727666488749)
                      ·
                        rfl

theorem cell23_1641421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1641421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641421 prefixEnd_1641421 := by exact prefixLift 1641421
  have htrace : WordTrace (prefixWord ++ tailWord_1641421) baseStart_1641421 baseEnd_1641421 := by
    simpa [prefixWord, tailWord_1641421, baseEnd_1641421] using wordTrace_append hprefix tailTrace_1641421
  have hstable : (prefixWord ++ tailWord_1641421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641421).length < 2 ^ (prefixWord ++ tailWord_1641421).sum := by decide
  have hdescent : baseEnd_1641421 < baseStart_1641421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641493 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 2, 5]
def baseStart_1641493 : Nat := 118140960795 + 1641493 * 2 ^ 59
def prefixEnd_1641493 : Nat := 4983230072969 + 3 ^ 40 * 1641493 * 2
def baseEnd_1641493 : Nat := 280958299996950461596139

theorem tailTrace_1641493 : CollatzResearch.WordTrace tailWord_1641493 prefixEnd_1641493 280958299996950461596139 := by
  unfold tailWord_1641493
  simp only [CollatzResearch.WordTrace]
  refine ⟨59870168242158680530129133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39913445494772453686752755 59870168242158680530129133)
  ·
    refine ⟨22451313090809505198798425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59870168242158680530129133 22451313090809505198798425)
    ·
      refine ⟨16838484818107128899098819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22451313090809505198798425 16838484818107128899098819)
      ·
        refine ⟨25257727227160693348648229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16838484818107128899098819 25257727227160693348648229)
        ·
          refine ⟨4735823855092630002871543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25257727227160693348648229 4735823855092630002871543)
          ·
            refine ⟨7103735782638945004307315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4735823855092630002871543 7103735782638945004307315)
            ·
              refine ⟨10655603673958417506460973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7103735782638945004307315 10655603673958417506460973)
              ·
                refine ⟨3995851377734406564922865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10655603673958417506460973 3995851377734406564922865)
                ·
                  refine ⟨2996888533300804923692149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3995851377734406564922865 2996888533300804923692149)
                  ·
                    refine ⟨280958299996950461596139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2996888533300804923692149 280958299996950461596139)
                    ·
                      rfl

theorem cell23_1641493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_1641493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641493 prefixEnd_1641493 := by exact prefixLift 1641493
  have htrace : WordTrace (prefixWord ++ tailWord_1641493) baseStart_1641493 baseEnd_1641493 := by
    simpa [prefixWord, tailWord_1641493, baseEnd_1641493] using wordTrace_append hprefix tailTrace_1641493
  have hstable : (prefixWord ++ tailWord_1641493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641493).length < 2 ^ (prefixWord ++ tailWord_1641493).sum := by decide
  have hdescent : baseEnd_1641493 < baseStart_1641493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641514 : List Nat := [3, 1, 4, 1, 3, 2, 2, 2, 5]
def baseStart_1641514 : Nat := 118140960795 + 1641514 * 2 ^ 59
def prefixEnd_1641514 : Nat := 4983230072969 + 3 ^ 40 * 1641514 * 2
def baseEnd_1641514 : Nat := 93653964787177311402869

theorem tailTrace_1641514 : CollatzResearch.WordTrace tailWord_1641514 prefixEnd_1641514 93653964787177311402869 := by
  unfold tailWord_1641514
  simp only [CollatzResearch.WordTrace]
  refine ⟨14967733543770650279160899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39913956116721734077762397 14967733543770650279160899)
  ·
    refine ⟨22451600315655975418741349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14967733543770650279160899 22451600315655975418741349)
    ·
      refine ⟨4209675059185495391014003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22451600315655975418741349 4209675059185495391014003)
      ·
        refine ⟨6314512588778243086521005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4209675059185495391014003 6314512588778243086521005)
        ·
          refine ⟨2367942220791841157445377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6314512588778243086521005 2367942220791841157445377)
          ·
            refine ⟨1775956665593880868084033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2367942220791841157445377 1775956665593880868084033)
            ·
              refine ⟨1331967499195410651063025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1775956665593880868084033 1331967499195410651063025)
              ·
                refine ⟨998975624396557988297269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1331967499195410651063025 998975624396557988297269)
                ·
                  refine ⟨93653964787177311402869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 998975624396557988297269 93653964787177311402869)
                  ·
                    rfl

theorem cell23_1641514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 5].length) (baseStart_1641514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641514 prefixEnd_1641514 := by exact prefixLift 1641514
  have htrace : WordTrace (prefixWord ++ tailWord_1641514) baseStart_1641514 baseEnd_1641514 := by
    simpa [prefixWord, tailWord_1641514, baseEnd_1641514] using wordTrace_append hprefix tailTrace_1641514
  have hstable : (prefixWord ++ tailWord_1641514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641514).length < 2 ^ (prefixWord ++ tailWord_1641514).sum := by decide
  have hdescent : baseEnd_1641514 < baseStart_1641514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641516 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_1641516 : Nat := 118140960795 + 1641516 * 2 ^ 59
def prefixEnd_1641516 : Nat := 4983230072969 + 3 ^ 40 * 1641516 * 2
def baseEnd_1641516 : Nat := 842886710045904794800811

theorem tailTrace_1641516 : CollatzResearch.WordTrace tailWord_1641516 prefixEnd_1641516 842886710045904794800811 := by
  unfold tailWord_1641516
  simp only [CollatzResearch.WordTrace]
  refine ⟨29935503560537677729108201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39914004747383570305477601 29935503560537677729108201)
  ·
    refine ⟨22451627670403258296831151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29935503560537677729108201 22451627670403258296831151)
    ·
      refine ⟨33677441505604887445246727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22451627670403258296831151 33677441505604887445246727)
      ·
        refine ⟨50516162258407331167870091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33677441505604887445246727 50516162258407331167870091)
        ·
          refine ⟨75774243387610996751805137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50516162258407331167870091 75774243387610996751805137)
          ·
            refine ⟨56830682540708247563853853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75774243387610996751805137 56830682540708247563853853)
            ·
              refine ⟨21311505952765592836445195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56830682540708247563853853 21311505952765592836445195)
              ·
                refine ⟨31967258929148389254667793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21311505952765592836445195 31967258929148389254667793)
                ·
                  refine ⟨23975444196861291941000845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31967258929148389254667793 23975444196861291941000845)
                  ·
                    refine ⟨8990791573822984477875317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23975444196861291941000845 8990791573822984477875317)
                    ·
                      refine ⟨842886710045904794800811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8990791573822984477875317 842886710045904794800811)
                      ·
                        rfl

theorem cell23_1641516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_1641516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641516 prefixEnd_1641516 := by exact prefixLift 1641516
  have htrace : WordTrace (prefixWord ++ tailWord_1641516) baseStart_1641516 baseEnd_1641516 := by
    simpa [prefixWord, tailWord_1641516, baseEnd_1641516] using wordTrace_append hprefix tailTrace_1641516
  have hstable : (prefixWord ++ tailWord_1641516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641516).length < 2 ^ (prefixWord ++ tailWord_1641516).sum := by decide
  have hdescent : baseEnd_1641516 < baseStart_1641516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641523 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 3, 4]
def baseStart_1641523 : Nat := 118140960795 + 1641523 * 2 ^ 59
def prefixEnd_1641523 : Nat := 4983230072969 + 3 ^ 40 * 1641523 * 2
def baseEnd_1641523 : Nat := 280963434803495422471093

theorem tailTrace_1641523 : CollatzResearch.WordTrace tailWord_1641523 prefixEnd_1641523 280963434803495422471093 := by
  unfold tailWord_1641523
  simp only [CollatzResearch.WordTrace]
  refine ⟨59871262432049995653721223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39914174954699997102480815 59871262432049995653721223)
  ·
    refine ⟨89806893648074993480581835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59871262432049995653721223 89806893648074993480581835)
    ·
      refine ⟨134710340472112490220872753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89806893648074993480581835 134710340472112490220872753)
      ·
        refine ⟨101032755354084367665654565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134710340472112490220872753 101032755354084367665654565)
        ·
          refine ⟨18943641628890818937310231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101032755354084367665654565 18943641628890818937310231)
          ·
            refine ⟨28415462443336228405965347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18943641628890818937310231 28415462443336228405965347)
            ·
              refine ⟨42623193665004342608948021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28415462443336228405965347 42623193665004342608948021)
              ·
                refine ⟨3995924406094157119588877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42623193665004342608948021 3995924406094157119588877)
                ·
                  refine ⟨1498471652285308919845829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3995924406094157119588877 1498471652285308919845829)
                  ·
                    refine ⟨280963434803495422471093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1498471652285308919845829 280963434803495422471093)
                    ·
                      rfl

theorem cell23_1641523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 4].length) (baseStart_1641523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641523 prefixEnd_1641523 := by exact prefixLift 1641523
  have htrace : WordTrace (prefixWord ++ tailWord_1641523) baseStart_1641523 baseEnd_1641523 := by
    simpa [prefixWord, tailWord_1641523, baseEnd_1641523] using wordTrace_append hprefix tailTrace_1641523
  have hstable : (prefixWord ++ tailWord_1641523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641523).length < 2 ^ (prefixWord ++ tailWord_1641523).sum := by decide
  have hdescent : baseEnd_1641523 < baseStart_1641523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641557 : List Nat := [1, 3, 2, 2, 1, 2, 4, 3, 1, 4]
def baseStart_1641557 : Nat := 118140960795 + 1641557 * 2 ^ 59
def prefixEnd_1641557 : Nat := 4983230072969 + 3 ^ 40 * 1641557 * 2
def baseEnd_1641557 : Nat := 280969254250913044796041

theorem tailTrace_1641557 : CollatzResearch.WordTrace tailWord_1641557 prefixEnd_1641557 280969254250913044796041 := by
  unfold tailWord_1641557
  simp only [CollatzResearch.WordTrace]
  refine ⟨59872502513926819460458925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39915001675951212973639283 59872502513926819460458925)
  ·
    refine ⟨22452188442722557297672097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59872502513926819460458925 22452188442722557297672097)
    ·
      refine ⟨16839141332041917973254073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22452188442722557297672097 16839141332041917973254073)
      ·
        refine ⟨12629355999031438479940555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16839141332041917973254073 12629355999031438479940555)
        ·
          refine ⟨18944033998547157719910833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12629355999031438479940555 18944033998547157719910833)
          ·
            refine ⟨14208025498910368289933125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18944033998547157719910833 14208025498910368289933125)
            ·
              refine ⟨2664004781045694054362461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14208025498910368289933125 2664004781045694054362461)
              ·
                refine ⟨999001792892135270385923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2664004781045694054362461 999001792892135270385923)
                ·
                  refine ⟨1498502689338202905578885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 999001792892135270385923 1498502689338202905578885)
                  ·
                    refine ⟨280969254250913044796041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1498502689338202905578885 280969254250913044796041)
                    ·
                      rfl

theorem cell23_1641557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_1641557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641557 prefixEnd_1641557 := by exact prefixLift 1641557
  have htrace : WordTrace (prefixWord ++ tailWord_1641557) baseStart_1641557 baseEnd_1641557 := by
    simpa [prefixWord, tailWord_1641557, baseEnd_1641557] using wordTrace_append hprefix tailTrace_1641557
  have hstable : (prefixWord ++ tailWord_1641557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641557).length < 2 ^ (prefixWord ++ tailWord_1641557).sum := by decide
  have hdescent : baseEnd_1641557 < baseStart_1641557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641570 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 8]
def baseStart_1641570 : Nat := 118140960795 + 1641570 * 2 ^ 59
def prefixEnd_1641570 : Nat := 4983230072969 + 3 ^ 40 * 1641570 * 2
def baseEnd_1641570 : Nat := 93657159777916398169507

theorem tailTrace_1641570 : CollatzResearch.WordTrace tailWord_1641570 prefixEnd_1641570 93657159777916398169507 := by
  unfold tailWord_1641570
  simp only [CollatzResearch.WordTrace]
  refine ⟨14968244165719930670170541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39915317775253148453788109 14968244165719930670170541)
  ·
    refine ⟨5613091562144974001313953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14968244165719930670170541 5613091562144974001313953)
    ·
      refine ⟨4209818671608730500985465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5613091562144974001313953 4209818671608730500985465)
      ·
        refine ⟨3157364003706547875739099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4209818671608730500985465 3157364003706547875739099)
        ·
          refine ⟨4736046005559821813608649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157364003706547875739099 4736046005559821813608649)
          ·
            refine ⟨3552034504169866360206487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4736046005559821813608649 3552034504169866360206487)
            ·
              refine ⟨5328051756254799540309731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3552034504169866360206487 5328051756254799540309731)
              ·
                refine ⟨7992077634382199310464597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5328051756254799540309731 7992077634382199310464597)
                ·
                  refine ⟨93657159777916398169507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7992077634382199310464597 93657159777916398169507)
                  ·
                    rfl

theorem cell23_1641570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_1641570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641570 prefixEnd_1641570 := by exact prefixLift 1641570
  have htrace : WordTrace (prefixWord ++ tailWord_1641570) baseStart_1641570 baseEnd_1641570 := by
    simpa [prefixWord, tailWord_1641570, baseEnd_1641570] using wordTrace_append hprefix tailTrace_1641570
  have hstable : (prefixWord ++ tailWord_1641570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641570).length < 2 ^ (prefixWord ++ tailWord_1641570).sum := by decide
  have hdescent : baseEnd_1641570 < baseStart_1641570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641631 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 3, 1, 3]
def baseStart_1641631 : Nat := 118140960795 + 1641631 * 2 ^ 59
def prefixEnd_1641631 : Nat := 4983230072969 + 3 ^ 40 * 1641631 * 2
def baseEnd_1641631 : Nat := 842945760321171844862783

theorem tailTrace_1641631 : CollatzResearch.WordTrace tailWord_1641631 prefixEnd_1641631 842945760321171844862783 := by
  unfold tailWord_1641631
  simp only [CollatzResearch.WordTrace]
  refine ⟨59875201515658730098652747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39916801010439153399101831 59875201515658730098652747)
  ·
    refine ⟨89812802273488095147979121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59875201515658730098652747 89812802273488095147979121)
    ·
      refine ⟨67359601705116071360984341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89812802273488095147979121 67359601705116071360984341)
      ·
        refine ⟨3157481329927315845046141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67359601705116071360984341 3157481329927315845046141)
        ·
          refine ⟨1184055498722743441892303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3157481329927315845046141 1184055498722743441892303)
          ·
            refine ⟨1776083248084115162838455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184055498722743441892303 1776083248084115162838455)
            ·
              refine ⟨2664124872126172744257683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1776083248084115162838455 2664124872126172744257683)
              ·
                refine ⟨3996187308189259116386525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2664124872126172744257683 3996187308189259116386525)
                ·
                  refine ⟨1498570240570972168644947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3996187308189259116386525 1498570240570972168644947)
                  ·
                    refine ⟨2247855360856458252967421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1498570240570972168644947 2247855360856458252967421)
                    ·
                      refine ⟨842945760321171844862783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2247855360856458252967421 842945760321171844862783)
                      ·
                        rfl

theorem cell23_1641631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_1641631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641631 prefixEnd_1641631 := by exact prefixLift 1641631
  have htrace : WordTrace (prefixWord ++ tailWord_1641631) baseStart_1641631 baseEnd_1641631 := by
    simpa [prefixWord, tailWord_1641631, baseEnd_1641631] using wordTrace_append hprefix tailTrace_1641631
  have hstable : (prefixWord ++ tailWord_1641631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641631).length < 2 ^ (prefixWord ++ tailWord_1641631).sum := by decide
  have hdescent : baseEnd_1641631 < baseStart_1641631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641633 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1641633 : Nat := 118140960795 + 1641633 * 2 ^ 59
def prefixEnd_1641633 : Nat := 4983230072969 + 3 ^ 40 * 1641633 * 2
def baseEnd_1641633 : Nat := 842946787282480837037773

theorem tailTrace_1641633 : CollatzResearch.WordTrace tailWord_1641633 prefixEnd_1641633 842946787282480837037773 := by
  unfold tailWord_1641633
  simp only [CollatzResearch.WordTrace]
  refine ⟨59875274461651484440225553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39916849641100989626817035 59875274461651484440225553)
  ·
    refine ⟨44906455846238613330169165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59875274461651484440225553 44906455846238613330169165)
    ·
      refine ⟨16839920942339479998813437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44906455846238613330169165 16839920942339479998813437)
      ·
        refine ⟨6314970353377304999555039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16839920942339479998813437 6314970353377304999555039)
        ·
          refine ⟨9472455530065957499332559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6314970353377304999555039 9472455530065957499332559)
          ·
            refine ⟨14208683295098936248998839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9472455530065957499332559 14208683295098936248998839)
            ·
              refine ⟨21313024942648404373498259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14208683295098936248998839 21313024942648404373498259)
              ·
                refine ⟨31969537413972606560247389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21313024942648404373498259 31969537413972606560247389)
                ·
                  refine ⟨11988576530239727460092771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31969537413972606560247389 11988576530239727460092771)
                  ·
                    refine ⟨17982864795359591190139157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11988576530239727460092771 17982864795359591190139157)
                    ·
                      refine ⟨842946787282480837037773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17982864795359591190139157 842946787282480837037773)
                      ·
                        rfl

theorem cell23_1641633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1641633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641633 prefixEnd_1641633 := by exact prefixLift 1641633
  have htrace : WordTrace (prefixWord ++ tailWord_1641633) baseStart_1641633 baseEnd_1641633 := by
    simpa [prefixWord, tailWord_1641633, baseEnd_1641633] using wordTrace_append hprefix tailTrace_1641633
  have hstable : (prefixWord ++ tailWord_1641633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641633).length < 2 ^ (prefixWord ++ tailWord_1641633).sum := by decide
  have hdescent : baseEnd_1641633 < baseStart_1641633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641647 : List Nat := [1, 1, 2, 1, 2, 3, 6, 1, 2, 4]
def baseStart_1641647 : Nat := 118140960795 + 1641647 * 2 ^ 59
def prefixEnd_1641647 : Nat := 4983230072969 + 3 ^ 40 * 1641647 * 2
def baseEnd_1641647 : Nat := 280984658670547927420903

theorem tailTrace_1641647 : CollatzResearch.WordTrace tailWord_1641647 prefixEnd_1641647 280984658670547927420903 := by
  unfold tailWord_1641647
  simp only [CollatzResearch.WordTrace]
  refine ⟨59875785083600764831235195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39917190055733843220823463 59875785083600764831235195)
  ·
    refine ⟨89813677625401147246852793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59875785083600764831235195 89813677625401147246852793)
    ·
      refine ⟨67360258219050860435139595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89813677625401147246852793 67360258219050860435139595)
      ·
        refine ⟨101040387328576290652709393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67360258219050860435139595 101040387328576290652709393)
        ·
          refine ⟨75780290496432217989532045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101040387328576290652709393 75780290496432217989532045)
          ·
            refine ⟨28417608936162081746074517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75780290496432217989532045 28417608936162081746074517)
            ·
              refine ⟨1332075418882597581847243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28417608936162081746074517 1332075418882597581847243)
              ·
                refine ⟨1998113128323896372770865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332075418882597581847243 1998113128323896372770865)
                ·
                  refine ⟨1498584846242922279578149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1998113128323896372770865 1498584846242922279578149)
                  ·
                    refine ⟨280984658670547927420903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1498584846242922279578149 280984658670547927420903)
                    ·
                      rfl

theorem cell23_1641647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 2, 4].length) (baseStart_1641647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641647 prefixEnd_1641647 := by exact prefixLift 1641647
  have htrace : WordTrace (prefixWord ++ tailWord_1641647) baseStart_1641647 baseEnd_1641647 := by
    simpa [prefixWord, tailWord_1641647, baseEnd_1641647] using wordTrace_append hprefix tailTrace_1641647
  have hstable : (prefixWord ++ tailWord_1641647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641647).length < 2 ^ (prefixWord ++ tailWord_1641647).sum := by decide
  have hdescent : baseEnd_1641647 < baseStart_1641647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641657 : List Nat := [1, 2, 1, 4, 1, 3, 3, 2, 1, 2, 3]
def baseStart_1641657 : Nat := 118140960795 + 1641657 * 2 ^ 59
def prefixEnd_1641657 : Nat := 4983230072969 + 3 ^ 40 * 1641657 * 2
def baseEnd_1641657 : Nat := 842959110818188743137663

theorem tailTrace_1641657 : CollatzResearch.WordTrace tailWord_1641657 prefixEnd_1641657 842959110818188743137663 := by
  unfold tailWord_1641657
  simp only [CollatzResearch.WordTrace]
  refine ⟨59876149813564536539099225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39917433209043024359399483 59876149813564536539099225)
  ·
    refine ⟨44907112360173402404324419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59876149813564536539099225 44907112360173402404324419)
    ·
      refine ⟨67360668540260103606486629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44907112360173402404324419 67360668540260103606486629)
      ·
        refine ⟨12630125351298769426216243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67360668540260103606486629 12630125351298769426216243)
        ·
          refine ⟨18945188026948154139324365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12630125351298769426216243 18945188026948154139324365)
          ·
            refine ⟨7104445510105557802246637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18945188026948154139324365 7104445510105557802246637)
            ·
              refine ⟨2664167066289584175842489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7104445510105557802246637 2664167066289584175842489)
              ·
                refine ⟨1998125299717188131881867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2664167066289584175842489 1998125299717188131881867)
                ·
                  refine ⟨2997187949575782197822801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998125299717188131881867 2997187949575782197822801)
                  ·
                    refine ⟨2247890962181836648367101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2997187949575782197822801 2247890962181836648367101)
                    ·
                      refine ⟨842959110818188743137663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2247890962181836648367101 842959110818188743137663)
                      ·
                        rfl

theorem cell23_1641657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_1641657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641657 prefixEnd_1641657 := by exact prefixLift 1641657
  have htrace : WordTrace (prefixWord ++ tailWord_1641657) baseStart_1641657 baseEnd_1641657 := by
    simpa [prefixWord, tailWord_1641657, baseEnd_1641657] using wordTrace_append hprefix tailTrace_1641657
  have hstable : (prefixWord ++ tailWord_1641657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641657).length < 2 ^ (prefixWord ++ tailWord_1641657).sum := by decide
  have hdescent : baseEnd_1641657 < baseStart_1641657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641674 : List Nat := [3, 1, 2, 1, 3, 3, 3, 1, 1, 2, 3]
def baseStart_1641674 : Nat := 118140960795 + 1641674 * 2 ^ 59
def prefixEnd_1641674 : Nat := 4983230072969 + 3 ^ 40 * 1641674 * 2
def baseEnd_1641674 : Nat := 842967839989315176625085

theorem tailTrace_1641674 : CollatzResearch.WordTrace tailWord_1641674 prefixEnd_1641674 842967839989315176625085 := by
  unfold tailWord_1641674
  simp only [CollatzResearch.WordTrace]
  refine ⟨14969192463625737110617019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39917846569668632294978717 14969192463625737110617019)
  ·
    refine ⟨22453788695438605665925529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14969192463625737110617019 22453788695438605665925529)
    ·
      refine ⟨16840341521578954249444147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22453788695438605665925529 16840341521578954249444147)
      ·
        refine ⟨25260512282368431374166221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16840341521578954249444147 25260512282368431374166221)
        ·
          refine ⟨9472692105888161765312333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25260512282368431374166221 9472692105888161765312333)
          ·
            refine ⟨3552259539708060661992125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9472692105888161765312333 3552259539708060661992125)
            ·
              refine ⟨1332097327390522748247047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3552259539708060661992125 1332097327390522748247047)
              ·
                refine ⟨1998145991085784122370571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332097327390522748247047 1998145991085784122370571)
                ·
                  refine ⟨2997218986628676183555857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998145991085784122370571 2997218986628676183555857)
                  ·
                    refine ⟨2247914239971507137666893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2997218986628676183555857 2247914239971507137666893)
                    ·
                      refine ⟨842967839989315176625085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2247914239971507137666893 842967839989315176625085)
                      ·
                        rfl

theorem cell23_1641674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_1641674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641674 prefixEnd_1641674 := by exact prefixLift 1641674
  have htrace : WordTrace (prefixWord ++ tailWord_1641674) baseStart_1641674 baseEnd_1641674 := by
    simpa [prefixWord, tailWord_1641674, baseEnd_1641674] using wordTrace_append hprefix tailTrace_1641674
  have hstable : (prefixWord ++ tailWord_1641674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641674).length < 2 ^ (prefixWord ++ tailWord_1641674).sum := by decide
  have hdescent : baseEnd_1641674 < baseStart_1641674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641677 : List Nat := [1, 6, 2, 2, 1, 11]
def baseStart_1641677 : Nat := 118140960795 + 1641677 * 2 ^ 59
def prefixEnd_1641677 : Nat := 4983230072969 + 3 ^ 40 * 1641677 * 2
def baseEnd_1641677 : Nat := 3469009796013492448097

theorem tailTrace_1641677 : CollatzResearch.WordTrace tailWord_1641677 prefixEnd_1641677 3469009796013492448097 := by
  unfold tailWord_1641677
  simp only [CollatzResearch.WordTrace]
  refine ⟨59876879273492079954827285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39917919515661386636551523 59876879273492079954827285)
  ·
    refine ⟨2806728715944941247882529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59876879273492079954827285 2806728715944941247882529)
    ·
      refine ⟨2105046536958705935911897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2806728715944941247882529 2105046536958705935911897)
      ·
        refine ⟨1578784902719029451933923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2105046536958705935911897 1578784902719029451933923)
        ·
          refine ⟨2368177354078544177900885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578784902719029451933923 2368177354078544177900885)
          ·
            refine ⟨3469009796013492448097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2368177354078544177900885 3469009796013492448097)
            ·
              rfl

theorem cell23_1641677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 11].length) (baseStart_1641677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641677 prefixEnd_1641677 := by exact prefixLift 1641677
  have htrace : WordTrace (prefixWord ++ tailWord_1641677) baseStart_1641677 baseEnd_1641677 := by
    simpa [prefixWord, tailWord_1641677, baseEnd_1641677] using wordTrace_append hprefix tailTrace_1641677
  have hstable : (prefixWord ++ tailWord_1641677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641677).length < 2 ^ (prefixWord ++ tailWord_1641677).sum := by decide
  have hdescent : baseEnd_1641677 < baseStart_1641677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641687 : List Nat := [1, 1, 3, 2, 1, 2, 3, 4, 2, 1, 3]
def baseStart_1641687 : Nat := 118140960795 + 1641687 * 2 ^ 59
def prefixEnd_1641687 : Nat := 4983230072969 + 3 ^ 40 * 1641687 * 2
def baseEnd_1641687 : Nat := 842974515237823625762525

theorem tailTrace_1641687 : CollatzResearch.WordTrace tailWord_1641687 prefixEnd_1641687 842974515237823625762525 := by
  unfold tailWord_1641687
  simp only [CollatzResearch.WordTrace]
  refine ⟨59877244003455851662691315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39918162668970567775127543 59877244003455851662691315)
  ·
    refine ⟨89815866005183777494036973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59877244003455851662691315 89815866005183777494036973)
    ·
      refine ⟨33680949751943916560263865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89815866005183777494036973 33680949751943916560263865)
      ·
        refine ⟨25260712313957937420197899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33680949751943916560263865 25260712313957937420197899)
        ·
          refine ⟨37891068470936906130296849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25260712313957937420197899 37891068470936906130296849)
          ·
            refine ⟨28418301353202679597722637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37891068470936906130296849 28418301353202679597722637)
            ·
              refine ⟨10656863007451004849145989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28418301353202679597722637 10656863007451004849145989)
              ·
                refine ⟨1998161813897063409214873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10656863007451004849145989 1998161813897063409214873)
                ·
                  refine ⟨1498621360422797556911155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1998161813897063409214873 1498621360422797556911155)
                  ·
                    refine ⟨2247932040634196335366733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1498621360422797556911155 2247932040634196335366733)
                    ·
                      refine ⟨842974515237823625762525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2247932040634196335366733 842974515237823625762525)
                      ·
                        rfl

theorem cell23_1641687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_1641687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641687 prefixEnd_1641687 := by exact prefixLift 1641687
  have htrace : WordTrace (prefixWord ++ tailWord_1641687) baseStart_1641687 baseEnd_1641687 := by
    simpa [prefixWord, tailWord_1641687, baseEnd_1641687] using wordTrace_append hprefix tailTrace_1641687
  have hstable : (prefixWord ++ tailWord_1641687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641687).length < 2 ^ (prefixWord ++ tailWord_1641687).sum := by decide
  have hdescent : baseEnd_1641687 < baseStart_1641687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641697 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 3, 3, 2]
def baseStart_1641697 : Nat := 118140960795 + 1641697 * 2 ^ 59
def prefixEnd_1641697 : Nat := 4983230072969 + 3 ^ 40 * 1641697 * 2
def baseEnd_1641697 : Nat := 842979650044368586637479

theorem tailTrace_1641697 : CollatzResearch.WordTrace tailWord_1641697 prefixEnd_1641697 842979650044368586637479 := by
  unfold tailWord_1641697
  simp only [CollatzResearch.WordTrace]
  refine ⟨59877608733419623370555345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39918405822279748913703563 59877608733419623370555345)
  ·
    refine ⟨44908206550064717527916509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59877608733419623370555345 44908206550064717527916509)
    ·
      refine ⟨16840577456274269072968691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44908206550064717527916509 16840577456274269072968691)
      ·
        refine ⟨25260866184411403609453037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16840577456274269072968691 25260866184411403609453037)
        ·
          refine ⟨9472824819154276353544889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25260866184411403609453037 9472824819154276353544889)
          ·
            refine ⟨7104618614365707265158667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9472824819154276353544889 7104618614365707265158667)
            ·
              refine ⟨10656927921548560897738001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7104618614365707265158667 10656927921548560897738001)
              ·
                refine ⟨7992695941161420673303501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10656927921548560897738001 7992695941161420673303501)
                ·
                  refine ⟨2997260977935532752488813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7992695941161420673303501 2997260977935532752488813)
                  ·
                    refine ⟨1123972866725824782183305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2997260977935532752488813 1123972866725824782183305)
                    ·
                      refine ⟨842979650044368586637479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1123972866725824782183305 842979650044368586637479)
                      ·
                        rfl

theorem cell23_1641697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_1641697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641697 prefixEnd_1641697 := by exact prefixLift 1641697
  have htrace : WordTrace (prefixWord ++ tailWord_1641697) baseStart_1641697 baseEnd_1641697 := by
    simpa [prefixWord, tailWord_1641697, baseEnd_1641697] using wordTrace_append hprefix tailTrace_1641697
  have hstable : (prefixWord ++ tailWord_1641697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641697).length < 2 ^ (prefixWord ++ tailWord_1641697).sum := by decide
  have hdescent : baseEnd_1641697 < baseStart_1641697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641727 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 1, 4, 2]
def baseStart_1641727 : Nat := 118140960795 + 1641727 * 2 ^ 59
def prefixEnd_1641727 : Nat := 4983230072969 + 3 ^ 40 * 1641727 * 2
def baseEnd_1641727 : Nat := 842995054464003469262341

theorem tailTrace_1641727 : CollatzResearch.WordTrace tailWord_1641727 prefixEnd_1641727 842995054464003469262341 := by
  unfold tailWord_1641727
  simp only [CollatzResearch.WordTrace]
  refine ⟨59878702923310938494147435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39919135282207292329431623 59878702923310938494147435)
  ·
    refine ⟨89818054384966407741221153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59878702923310938494147435 89818054384966407741221153)
    ·
      refine ⟨67363540788724805805915865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89818054384966407741221153 67363540788724805805915865)
      ·
        refine ⟨50522655591543604354436899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67363540788724805805915865 50522655591543604354436899)
        ·
          refine ⟨75783983387315406531655349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50522655591543604354436899 75783983387315406531655349)
          ·
            refine ⟨7104748442560819362342689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75783983387315406531655349 7104748442560819362342689)
            ·
              refine ⟨5328561331920614521757017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7104748442560819362342689 5328561331920614521757017)
              ·
                refine ⟨3996420998940460891317763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5328561331920614521757017 3996420998940460891317763)
                ·
                  refine ⟨5994631498410691336976645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996420998940460891317763 5994631498410691336976645)
                  ·
                    refine ⟨1123993405952004625683121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5994631498410691336976645 1123993405952004625683121)
                    ·
                      refine ⟨842995054464003469262341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1123993405952004625683121 842995054464003469262341)
                      ·
                        rfl

theorem cell23_1641727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 4, 2].length) (baseStart_1641727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641727 prefixEnd_1641727 := by exact prefixLift 1641727
  have htrace : WordTrace (prefixWord ++ tailWord_1641727) baseStart_1641727 baseEnd_1641727 := by
    simpa [prefixWord, tailWord_1641727, baseEnd_1641727] using wordTrace_append hprefix tailTrace_1641727
  have hstable : (prefixWord ++ tailWord_1641727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641727).length < 2 ^ (prefixWord ++ tailWord_1641727).sum := by decide
  have hdescent : baseEnd_1641727 < baseStart_1641727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641731 : List Nat := [1, 1, 1, 3, 2, 6, 2, 1, 1, 3, 2]
def baseStart_1641731 : Nat := 118140960795 + 1641731 * 2 ^ 59
def prefixEnd_1641731 : Nat := 4983230072969 + 3 ^ 40 * 1641731 * 2
def baseEnd_1641731 : Nat := 842997108386621453612323

theorem tailTrace_1641731 : CollatzResearch.WordTrace tailWord_1641731 prefixEnd_1641731 842997108386621453612323 := by
  unfold tailWord_1641731
  simp only [CollatzResearch.WordTrace]
  refine ⟨59878848815296447177293047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39919232543530964784862031 59878848815296447177293047)
  ·
    refine ⟨89818273222944670765939571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59878848815296447177293047 89818273222944670765939571)
    ·
      refine ⟨134727409834417006148909357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89818273222944670765939571 134727409834417006148909357)
      ·
        refine ⟨50522778687906377305841009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134727409834417006148909357 50522778687906377305841009)
        ·
          refine ⟨37892084015929782979380757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50522778687906377305841009 37892084015929782979380757)
          ·
            refine ⟨1776191438246708577158473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37892084015929782979380757 1776191438246708577158473)
            ·
              refine ⟨1332143578685031432868855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1776191438246708577158473 1332143578685031432868855)
              ·
                refine ⟨1998215368027547149303283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332143578685031432868855 1998215368027547149303283)
                ·
                  refine ⟨2997323052041320723954925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998215368027547149303283 2997323052041320723954925)
                  ·
                    refine ⟨1123996144515495271483097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2997323052041320723954925 1123996144515495271483097)
                    ·
                      refine ⟨842997108386621453612323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1123996144515495271483097 842997108386621453612323)
                      ·
                        rfl

theorem cell23_1641731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 1, 3, 2].length) (baseStart_1641731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641731 prefixEnd_1641731 := by exact prefixLift 1641731
  have htrace : WordTrace (prefixWord ++ tailWord_1641731) baseStart_1641731 baseEnd_1641731 := by
    simpa [prefixWord, tailWord_1641731, baseEnd_1641731] using wordTrace_append hprefix tailTrace_1641731
  have hstable : (prefixWord ++ tailWord_1641731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641731).length < 2 ^ (prefixWord ++ tailWord_1641731).sum := by decide
  have hdescent : baseEnd_1641731 < baseStart_1641731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641733 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 9]
def baseStart_1641733 : Nat := 118140960795 + 1641733 * 2 ^ 59
def prefixEnd_1641733 : Nat := 4983230072969 + 3 ^ 40 * 1641733 * 2
def baseEnd_1641733 : Nat := 93666459483103382865257

theorem tailTrace_1641733 : CollatzResearch.WordTrace tailWord_1641733 prefixEnd_1641733 93666459483103382865257 := by
  unfold tailWord_1641733
  simp only [CollatzResearch.WordTrace]
  refine ⟨59878921761289201518865853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39919281174192801012577235 59878921761289201518865853)
  ·
    refine ⟨22454595660483450569574695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59878921761289201518865853 22454595660483450569574695)
    ·
      refine ⟨33681893490725175854362043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22454595660483450569574695 33681893490725175854362043)
      ·
        refine ⟨50522840236087763781543065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33681893490725175854362043 50522840236087763781543065)
        ·
          refine ⟨37892130177065822836157299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50522840236087763781543065 37892130177065822836157299)
          ·
            refine ⟨56838195265598734254235949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37892130177065822836157299 56838195265598734254235949)
            ·
              refine ⟨21314323224599525345338481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56838195265598734254235949 21314323224599525345338481)
              ·
                refine ⟨15985742418449644009003861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21314323224599525345338481 15985742418449644009003861)
                ·
                  refine ⟨93666459483103382865257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15985742418449644009003861 93666459483103382865257)
                  ·
                    rfl

theorem cell23_1641733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_1641733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641733 prefixEnd_1641733 := by exact prefixLift 1641733
  have htrace : WordTrace (prefixWord ++ tailWord_1641733) baseStart_1641733 baseEnd_1641733 := by
    simpa [prefixWord, tailWord_1641733, baseEnd_1641733] using wordTrace_append hprefix tailTrace_1641733
  have hstable : (prefixWord ++ tailWord_1641733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641733).length < 2 ^ (prefixWord ++ tailWord_1641733).sum := by decide
  have hdescent : baseEnd_1641733 < baseStart_1641733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641740 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_1641740 : Nat := 118140960795 + 1641740 * 2 ^ 59
def prefixEnd_1641740 : Nat := 4983230072969 + 3 ^ 40 * 1641740 * 2
def baseEnd_1641740 : Nat := 843001729712511918399781

theorem tailTrace_1641740 : CollatzResearch.WordTrace tailWord_1641740 prefixEnd_1641740 843001729712511918399781 := by
  unfold tailWord_1641740
  simp only [CollatzResearch.WordTrace]
  refine ⟨29939588536131920857185337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39919451381509227809580449 29939588536131920857185337)
  ·
    refine ⟨22454691402098940642889003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29939588536131920857185337 22454691402098940642889003)
    ·
      refine ⟨33682037103148410964333505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22454691402098940642889003 33682037103148410964333505)
      ·
        refine ⟨25261527827361308223250129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33682037103148410964333505 25261527827361308223250129)
        ·
          refine ⟨18946145870520981167437597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25261527827361308223250129 18946145870520981167437597)
          ·
            refine ⟨7104804701445367937789099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18946145870520981167437597 7104804701445367937789099)
            ·
              refine ⟨10657207052168051906683649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7104804701445367937789099 10657207052168051906683649)
              ·
                refine ⟨7992905289126038930012737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10657207052168051906683649 7992905289126038930012737)
                ·
                  refine ⟨5994678966844529197509553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7992905289126038930012737 5994678966844529197509553)
                  ·
                    refine ⟨4496009225133396898132165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5994678966844529197509553 4496009225133396898132165)
                    ·
                      refine ⟨843001729712511918399781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4496009225133396898132165 843001729712511918399781)
                      ·
                        rfl

theorem cell23_1641740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_1641740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641740 prefixEnd_1641740 := by exact prefixLift 1641740
  have htrace : WordTrace (prefixWord ++ tailWord_1641740) baseStart_1641740 baseEnd_1641740 := by
    simpa [prefixWord, tailWord_1641740, baseEnd_1641740] using wordTrace_append hprefix tailTrace_1641740
  have hstable : (prefixWord ++ tailWord_1641740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641740).length < 2 ^ (prefixWord ++ tailWord_1641740).sum := by decide
  have hdescent : baseEnd_1641740 < baseStart_1641740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641757 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1641757 : Nat := 118140960795 + 1641757 * 2 ^ 59
def prefixEnd_1641757 : Nat := 4983230072969 + 3 ^ 40 * 1641757 * 2
def baseEnd_1641757 : Nat := 843010458883638351887203

theorem tailTrace_1641757 : CollatzResearch.WordTrace tailWord_1641757 prefixEnd_1641757 843010458883638351887203 := by
  unfold tailWord_1641757
  simp only [CollatzResearch.WordTrace]
  refine ⟨59879797113202253617739525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39919864742134835745159683 59879797113202253617739525)
  ·
    refine ⟨11227461958725422553326161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59879797113202253617739525 11227461958725422553326161)
    ·
      refine ⟨8420596469044066914994621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11227461958725422553326161 8420596469044066914994621)
      ·
        refine ⟨3157723675891525093122983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8420596469044066914994621 3157723675891525093122983)
        ·
          refine ⟨4736585513837287639684475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157723675891525093122983 4736585513837287639684475)
          ·
            refine ⟨7104878270755931459526713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4736585513837287639684475 7104878270755931459526713)
            ·
              refine ⟨5328658703066948594645035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7104878270755931459526713 5328658703066948594645035)
              ·
                refine ⟨7992988054600422891967553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5328658703066948594645035 7992988054600422891967553)
                ·
                  refine ⟨5994741040950317168975665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7992988054600422891967553 5994741040950317168975665)
                  ·
                    refine ⟨4496055780712737876731749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5994741040950317168975665 4496055780712737876731749)
                    ·
                      refine ⟨843010458883638351887203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4496055780712737876731749 843010458883638351887203)
                      ·
                        rfl

theorem cell23_1641757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1641757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641757 prefixEnd_1641757 := by exact prefixLift 1641757
  have htrace : WordTrace (prefixWord ++ tailWord_1641757) baseStart_1641757 baseEnd_1641757 := by
    simpa [prefixWord, tailWord_1641757, baseEnd_1641757] using wordTrace_append hprefix tailTrace_1641757
  have hstable : (prefixWord ++ tailWord_1641757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641757).length < 2 ^ (prefixWord ++ tailWord_1641757).sum := by decide
  have hdescent : baseEnd_1641757 < baseStart_1641757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641817 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 2, 4, 2]
def baseStart_1641817 : Nat := 118140960795 + 1641817 * 2 ^ 59
def prefixEnd_1641817 : Nat := 4983230072969 + 3 ^ 40 * 1641817 * 2
def baseEnd_1641817 : Nat := 843041267722908117136927

theorem tailTrace_1641817 : CollatzResearch.WordTrace tailWord_1641817 prefixEnd_1641817 843041267722908117136927 := by
  unfold tailWord_1641817
  simp only [CollatzResearch.WordTrace]
  refine ⟨59881985492984883864923705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39921323661989922576615803 59881985492984883864923705)
  ·
    refine ⟨44911489119738662898692779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59881985492984883864923705 44911489119738662898692779)
    ·
      refine ⟨67367233679607994348039169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44911489119738662898692779 67367233679607994348039169)
      ·
        refine ⟨50525425259705995761029377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67367233679607994348039169 50525425259705995761029377)
        ·
          refine ⟨37894068944779496820772033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50525425259705995761029377 37894068944779496820772033)
          ·
            refine ⟨28420551708584622615579025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37894068944779496820772033 28420551708584622615579025)
            ·
              refine ⟨21315413781438466961684269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28420551708584622615579025 21315413781438466961684269)
              ·
                refine ⟨7993280168039425110631601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21315413781438466961684269 7993280168039425110631601)
                ·
                  refine ⟨5994960126029568832973701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7993280168039425110631601 5994960126029568832973701)
                  ·
                    refine ⟨1124055023630544156182569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5994960126029568832973701 1124055023630544156182569)
                    ·
                      refine ⟨843041267722908117136927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1124055023630544156182569 843041267722908117136927)
                      ·
                        rfl

theorem cell23_1641817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 4, 2].length) (baseStart_1641817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641817 prefixEnd_1641817 := by exact prefixLift 1641817
  have htrace : WordTrace (prefixWord ++ tailWord_1641817) baseStart_1641817 baseEnd_1641817 := by
    simpa [prefixWord, tailWord_1641817, baseEnd_1641817] using wordTrace_append hprefix tailTrace_1641817
  have hstable : (prefixWord ++ tailWord_1641817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641817).length < 2 ^ (prefixWord ++ tailWord_1641817).sum := by decide
  have hdescent : baseEnd_1641817 < baseStart_1641817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641861 : List Nat := [1, 3, 1, 1, 3, 1, 6, 2, 1, 4]
def baseStart_1641861 : Nat := 118140960795 + 1641861 * 2 ^ 59
def prefixEnd_1641861 : Nat := 4983230072969 + 3 ^ 40 * 1641861 * 2
def baseEnd_1641861 : Nat := 281021286957235314995575

theorem tailTrace_1641861 : CollatzResearch.WordTrace tailWord_1641861 prefixEnd_1641861 281021286957235314995575 := by
  unfold tailWord_1641861
  simp only [CollatzResearch.WordTrace]
  refine ⟨59883590304825479379525437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39922393536550319586350291 59883590304825479379525437)
  ·
    refine ⟨22456346364309554767322039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59883590304825479379525437 22456346364309554767322039)
    ·
      refine ⟨33684519546464332150983059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22456346364309554767322039 33684519546464332150983059)
      ·
        refine ⟨50526779319696498226474589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33684519546464332150983059 50526779319696498226474589)
        ·
          refine ⟨18947542244886186834927971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50526779319696498226474589 18947542244886186834927971)
          ·
            refine ⟨28421313367329280252391957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18947542244886186834927971 28421313367329280252391957)
            ·
              refine ⟨1332249064093560011830873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28421313367329280252391957 1332249064093560011830873)
              ·
                refine ⟨999186798070170008873155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332249064093560011830873 999186798070170008873155)
                ·
                  refine ⟨1498780197105255013309733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 999186798070170008873155 1498780197105255013309733)
                  ·
                    refine ⟨281021286957235314995575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1498780197105255013309733 281021286957235314995575)
                    ·
                      rfl

theorem cell23_1641861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_1641861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641861 prefixEnd_1641861 := by exact prefixLift 1641861
  have htrace : WordTrace (prefixWord ++ tailWord_1641861) baseStart_1641861 baseEnd_1641861 := by
    simpa [prefixWord, tailWord_1641861, baseEnd_1641861] using wordTrace_append hprefix tailTrace_1641861
  have hstable : (prefixWord ++ tailWord_1641861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641861).length < 2 ^ (prefixWord ++ tailWord_1641861).sum := by decide
  have hdescent : baseEnd_1641861 < baseStart_1641861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641887 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 3, 5]
def baseStart_1641887 : Nat := 118140960795 + 1641887 * 2 ^ 59
def prefixEnd_1641887 : Nat := 4983230072969 + 3 ^ 40 * 1641887 * 2
def baseEnd_1641887 : Nat := 281025737122907614420535

theorem tailTrace_1641887 : CollatzResearch.WordTrace tailWord_1641887 prefixEnd_1641887 281025737122907614420535 := by
  unfold tailWord_1641887
  simp only [CollatzResearch.WordTrace]
  refine ⟨59884538602731285819971915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39923025735154190546647943 59884538602731285819971915)
  ·
    refine ⟨89826807904096928729957873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59884538602731285819971915 89826807904096928729957873)
    ·
      refine ⟨67370105928072696547468405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89826807904096928729957873 67370105928072696547468405)
      ·
        refine ⟨6315947430756815301325163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67370105928072696547468405 6315947430756815301325163)
        ·
          refine ⟨9473921146135222951987745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6315947430756815301325163 9473921146135222951987745)
          ·
            refine ⟨7105440859601417213990809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9473921146135222951987745 7105440859601417213990809)
            ·
              refine ⟨5329080644701062910493107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7105440859601417213990809 5329080644701062910493107)
              ·
                refine ⟨7993620967051594365739661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5329080644701062910493107 7993620967051594365739661)
                ·
                  refine ⟨2997607862644347887152373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7993620967051594365739661 2997607862644347887152373)
                  ·
                    refine ⟨281025737122907614420535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2997607862644347887152373 281025737122907614420535)
                    ·
                      rfl

theorem cell23_1641887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 5].length) (baseStart_1641887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641887 prefixEnd_1641887 := by exact prefixLift 1641887
  have htrace : WordTrace (prefixWord ++ tailWord_1641887) baseStart_1641887 baseEnd_1641887 := by
    simpa [prefixWord, tailWord_1641887, baseEnd_1641887] using wordTrace_append hprefix tailTrace_1641887
  have hstable : (prefixWord ++ tailWord_1641887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641887).length < 2 ^ (prefixWord ++ tailWord_1641887).sum := by decide
  have hdescent : baseEnd_1641887 < baseStart_1641887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641907 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 1, 8, 2]
def baseStart_1641907 : Nat := 118140960795 + 1641907 * 2 ^ 59
def prefixEnd_1641907 : Nat := 4983230072969 + 3 ^ 40 * 1641907 * 2
def baseEnd_1641907 : Nat := 843087480981812765011513

theorem tailTrace_1641907 : CollatzResearch.WordTrace tailWord_1641907 prefixEnd_1641907 843087480981812765011513 := by
  unfold tailWord_1641907
  simp only [CollatzResearch.WordTrace]
  refine ⟨59885268062658829235699975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39923512041772552823799983 59885268062658829235699975)
  ·
    refine ⟨89827902093988243853549963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59885268062658829235699975 89827902093988243853549963)
    ·
      refine ⟨134741853140982365780324945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89827902093988243853549963 134741853140982365780324945)
      ·
        refine ⟨101056389855736774335243709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134741853140982365780324945 101056389855736774335243709)
        ·
          refine ⟨37896146195901290375716391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101056389855736774335243709 37896146195901290375716391)
          ·
            refine ⟨56844219293851935563574587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37896146195901290375716391 56844219293851935563574587)
            ·
              refine ⟨85266328940777903345361881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56844219293851935563574587 85266328940777903345361881)
              ·
                refine ⟨63949746705583427509021411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85266328940777903345361881 63949746705583427509021411)
                ·
                  refine ⟨95924620058375141263532117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63949746705583427509021411 95924620058375141263532117)
                  ·
                    refine ⟨1124116641309083686682017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95924620058375141263532117 1124116641309083686682017)
                    ·
                      refine ⟨843087480981812765011513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1124116641309083686682017 843087480981812765011513)
                      ·
                        rfl

theorem cell23_1641907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 8, 2].length) (baseStart_1641907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641907 prefixEnd_1641907 := by exact prefixLift 1641907
  have htrace : WordTrace (prefixWord ++ tailWord_1641907) baseStart_1641907 baseEnd_1641907 := by
    simpa [prefixWord, tailWord_1641907, baseEnd_1641907] using wordTrace_append hprefix tailTrace_1641907
  have hstable : (prefixWord ++ tailWord_1641907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641907).length < 2 ^ (prefixWord ++ tailWord_1641907).sum := by decide
  have hdescent : baseEnd_1641907 < baseStart_1641907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641927 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_1641927 : Nat := 118140960795 + 1641927 * 2 ^ 59
def prefixEnd_1641927 : Nat := 4983230072969 + 3 ^ 40 * 1641927 * 2
def baseEnd_1641927 : Nat := 843097750594902686761421

theorem tailTrace_1641927 : CollatzResearch.WordTrace tailWord_1641927 prefixEnd_1641927 843097750594902686761421 := by
  unfold tailWord_1641927
  simp only [CollatzResearch.WordTrace]
  refine ⟨59885997522586372651428035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39923998348390915100952023 59885997522586372651428035)
  ·
    refine ⟨89828996283879558977142053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59885997522586372651428035 89828996283879558977142053)
    ·
      refine ⟨16842936803227417308214135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89828996283879558977142053 16842936803227417308214135)
      ·
        refine ⟨25264405204841125962321203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16842936803227417308214135 25264405204841125962321203)
        ·
          refine ⟨37896607807261688943481805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25264405204841125962321203 37896607807261688943481805)
          ·
            refine ⟨14211227927723133353805677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37896607807261688943481805 14211227927723133353805677)
            ·
              refine ⟨5329210472896175007677129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14211227927723133353805677 5329210472896175007677129)
              ·
                refine ⟨3996907854672131255757847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5329210472896175007677129 3996907854672131255757847)
                ·
                  refine ⟨5995361782008196883636771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996907854672131255757847 5995361782008196883636771)
                  ·
                    refine ⟨8993042673012295325455157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5995361782008196883636771 8993042673012295325455157)
                    ·
                      refine ⟨843097750594902686761421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8993042673012295325455157 843097750594902686761421)
                      ·
                        rfl

theorem cell23_1641927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_1641927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641927 prefixEnd_1641927 := by exact prefixLift 1641927
  have htrace : WordTrace (prefixWord ++ tailWord_1641927) baseStart_1641927 baseEnd_1641927 := by
    simpa [prefixWord, tailWord_1641927, baseEnd_1641927] using wordTrace_append hprefix tailTrace_1641927
  have hstable : (prefixWord ++ tailWord_1641927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641927).length < 2 ^ (prefixWord ++ tailWord_1641927).sum := by decide
  have hdescent : baseEnd_1641927 < baseStart_1641927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641934 : List Nat := [4, 1, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_1641934 : Nat := 118140960795 + 1641934 * 2 ^ 59
def prefixEnd_1641934 : Nat := 4983230072969 + 3 ^ 40 * 1641934 * 2
def baseEnd_1641934 : Nat := 281033781653161386457963

theorem tailTrace_1641934 : CollatzResearch.WordTrace tailWord_1641934 prefixEnd_1641934 281033781653161386457963 := by
  unfold tailWord_1641934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7485781604195126605866607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39924168555707341897955237 7485781604195126605866607)
  ·
    refine ⟨11228672406292689908799911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7485781604195126605866607 11228672406292689908799911)
    ·
      refine ⟨16843008609439034863199867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11228672406292689908799911 16843008609439034863199867)
      ·
        refine ⟨25264512914158552294799801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16843008609439034863199867 25264512914158552294799801)
        ·
          refine ⟨18948384685618914221099851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25264512914158552294799801 18948384685618914221099851)
          ·
            refine ⟨28422577028428371331649777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18948384685618914221099851 28422577028428371331649777)
            ·
              refine ⟨21316932771321278498737333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28422577028428371331649777 21316932771321278498737333)
              ·
                refine ⟨1998462447311369859256625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21316932771321278498737333 1998462447311369859256625)
                ·
                  refine ⟨1498846835483527394442469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1998462447311369859256625 1498846835483527394442469)
                  ·
                    refine ⟨281033781653161386457963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1498846835483527394442469 281033781653161386457963)
                    ·
                      rfl

theorem cell23_1641934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_1641934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641934 prefixEnd_1641934 := by exact prefixLift 1641934
  have htrace : WordTrace (prefixWord ++ tailWord_1641934) baseStart_1641934 baseEnd_1641934 := by
    simpa [prefixWord, tailWord_1641934, baseEnd_1641934] using wordTrace_append hprefix tailTrace_1641934
  have hstable : (prefixWord ++ tailWord_1641934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641934).length < 2 ^ (prefixWord ++ tailWord_1641934).sum := by decide
  have hdescent : baseEnd_1641934 < baseStart_1641934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641941 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 3, 2, 2]
def baseStart_1641941 : Nat := 118140960795 + 1641941 * 2 ^ 59
def prefixEnd_1641941 : Nat := 4983230072969 + 3 ^ 40 * 1641941 * 2
def baseEnd_1641941 : Nat := 843104939324065631986357

theorem tailTrace_1641941 : CollatzResearch.WordTrace tailWord_1641941 prefixEnd_1641941 843104939324065631986357 := by
  unfold tailWord_1641941
  simp only [CollatzResearch.WordTrace]
  refine ⟨59886508144535653042437677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39924338763023768694958451 59886508144535653042437677)
  ·
    refine ⟨22457440554200869890914129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59886508144535653042437677 22457440554200869890914129)
    ·
      refine ⟨16843080415650652418185597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22457440554200869890914129 16843080415650652418185597)
      ·
        refine ⟨6316155155868994656819599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16843080415650652418185597 6316155155868994656819599)
        ·
          refine ⟨9474232733803491985229399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6316155155868994656819599 9474232733803491985229399)
          ·
            refine ⟨14211349100705237977844099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9474232733803491985229399 14211349100705237977844099)
            ·
              refine ⟨21317023651057856966766149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14211349100705237977844099 21317023651057856966766149)
              ·
                refine ⟨3996941934573348181268653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21317023651057856966766149 3996941934573348181268653)
                ·
                  refine ⟨1498853225465005567975745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3996941934573348181268653 1498853225465005567975745)
                  ·
                    refine ⟨1124139919098754175981809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1498853225465005567975745 1124139919098754175981809)
                    ·
                      refine ⟨843104939324065631986357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1124139919098754175981809 843104939324065631986357)
                      ·
                        rfl

theorem cell23_1641941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_1641941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641941 prefixEnd_1641941 := by exact prefixLift 1641941
  have htrace : WordTrace (prefixWord ++ tailWord_1641941) baseStart_1641941 baseEnd_1641941 := by
    simpa [prefixWord, tailWord_1641941, baseEnd_1641941] using wordTrace_append hprefix tailTrace_1641941
  have hstable : (prefixWord ++ tailWord_1641941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641941).length < 2 ^ (prefixWord ++ tailWord_1641941).sum := by decide
  have hdescent : baseEnd_1641941 < baseStart_1641941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641944 : List Nat := [2, 1, 2, 2, 2, 1, 3, 4, 1, 2, 3]
def baseStart_1641944 : Nat := 118140960795 + 1641944 * 2 ^ 59
def prefixEnd_1641944 : Nat := 4983230072969 + 3 ^ 40 * 1641944 * 2
def baseEnd_1641944 : Nat := 843106479766029120248843

theorem tailTrace_1641944 : CollatzResearch.WordTrace tailWord_1641944 prefixEnd_1641944 843106479766029120248843 := by
  unfold tailWord_1641944
  simp only [CollatzResearch.WordTrace]
  refine ⟨29943308781762392277398443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39924411709016523036531257 29943308781762392277398443)
  ·
    refine ⟨44914963172643588416097665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29943308781762392277398443 44914963172643588416097665)
    ·
      refine ⟨33686222379482691312073249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44914963172643588416097665 33686222379482691312073249)
      ·
        refine ⟨25264666784612018484054937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33686222379482691312073249 25264666784612018484054937)
        ·
          refine ⟨18948500088459013863041203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25264666784612018484054937 18948500088459013863041203)
          ·
            refine ⟨28422750132688520794561805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18948500088459013863041203 28422750132688520794561805)
            ·
              refine ⟨10658531299758195297960677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28422750132688520794561805 10658531299758195297960677)
              ·
                refine ⟨1998474618704661618367627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10658531299758195297960677 1998474618704661618367627)
                ·
                  refine ⟨2997711928056992427551441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998474618704661618367627 2997711928056992427551441)
                  ·
                    refine ⟨2248283946042744320663581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2997711928056992427551441 2248283946042744320663581)
                    ·
                      refine ⟨843106479766029120248843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2248283946042744320663581 843106479766029120248843)
                      ·
                        rfl

theorem cell23_1641944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_1641944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641944 prefixEnd_1641944 := by exact prefixLift 1641944
  have htrace : WordTrace (prefixWord ++ tailWord_1641944) baseStart_1641944 baseEnd_1641944 := by
    simpa [prefixWord, tailWord_1641944, baseEnd_1641944] using wordTrace_append hprefix tailTrace_1641944
  have hstable : (prefixWord ++ tailWord_1641944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641944).length < 2 ^ (prefixWord ++ tailWord_1641944).sum := by decide
  have hdescent : baseEnd_1641944 < baseStart_1641944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1641985 : List Nat := [1, 2, 4, 1, 5, 1, 2, 1, 2, 4]
def baseStart_1641985 : Nat := 118140960795 + 1641985 * 2 ^ 59
def prefixEnd_1641985 : Nat := 4983230072969 + 3 ^ 40 * 1641985 * 2
def baseEnd_1641985 : Nat := 281042510824287819945385

theorem tailTrace_1641985 : CollatzResearch.WordTrace tailWord_1641985 prefixEnd_1641985 281042510824287819945385 := by
  unfold tailWord_1641985
  simp only [CollatzResearch.WordTrace]
  refine ⟨59888112956376248557039409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39925408637584165704692939 59888112956376248557039409)
  ·
    refine ⟨44916084717282186417779557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59888112956376248557039409 44916084717282186417779557)
    ·
      refine ⟨8421765884490409953333667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44916084717282186417779557 8421765884490409953333667)
      ·
        refine ⟨12632648826735614930000501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8421765884490409953333667 12632648826735614930000501)
        ·
          refine ⟨1184310827506463899687547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12632648826735614930000501 1184310827506463899687547)
          ·
            refine ⟨1776466241259695849531321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184310827506463899687547 1776466241259695849531321)
            ·
              refine ⟨1332349680944771887148491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1776466241259695849531321 1332349680944771887148491)
              ·
                refine ⟨1998524521417157830722737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332349680944771887148491 1998524521417157830722737)
                ·
                  refine ⟨1498893391062868373042053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1998524521417157830722737 1498893391062868373042053)
                  ·
                    refine ⟨281042510824287819945385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1498893391062868373042053 281042510824287819945385)
                    ·
                      rfl

theorem cell23_1641985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_1641985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1641985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1641985 prefixEnd_1641985 := by exact prefixLift 1641985
  have htrace : WordTrace (prefixWord ++ tailWord_1641985) baseStart_1641985 baseEnd_1641985 := by
    simpa [prefixWord, tailWord_1641985, baseEnd_1641985] using wordTrace_append hprefix tailTrace_1641985
  have hstable : (prefixWord ++ tailWord_1641985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1641985).length < 2 ^ (prefixWord ++ tailWord_1641985).sum := by decide
  have hdescent : baseEnd_1641985 < baseStart_1641985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1641985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642067 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 8, 5]
def baseStart_1642067 : Nat := 118140960795 + 1642067 * 2 ^ 59
def prefixEnd_1642067 : Nat := 4983230072969 + 3 ^ 40 * 1642067 * 2
def baseEnd_1642067 : Nat := 281056545962177379670259

theorem tailTrace_1642067 : CollatzResearch.WordTrace tailWord_1642067 prefixEnd_1642067 281056545962177379670259 := by
  unfold tailWord_1642067
  simp only [CollatzResearch.WordTrace]
  refine ⟨59891103742079176561524455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39927402494719451041016303 59891103742079176561524455)
  ·
    refine ⟨89836655613118764842286683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59891103742079176561524455 89836655613118764842286683)
    ·
      refine ⟨134754983419678147263430025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89836655613118764842286683 134754983419678147263430025)
      ·
        refine ⟨101066237564758610447572519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134754983419678147263430025 101066237564758610447572519)
        ·
          refine ⟨151599356347137915671358779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101066237564758610447572519 151599356347137915671358779)
          ·
            refine ⟨227399034520706873507038169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151599356347137915671358779 227399034520706873507038169)
            ·
              refine ⟨170549275890530155130278627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227399034520706873507038169 170549275890530155130278627)
              ·
                refine ⟨255823913835795232695417941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170549275890530155130278627 255823913835795232695417941)
                ·
                  refine ⟨2997936490263225383149429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 255823913835795232695417941 2997936490263225383149429)
                  ·
                    refine ⟨281056545962177379670259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2997936490263225383149429 281056545962177379670259)
                    ·
                      rfl

theorem cell23_1642067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 5].length) (baseStart_1642067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642067 prefixEnd_1642067 := by exact prefixLift 1642067
  have htrace : WordTrace (prefixWord ++ tailWord_1642067) baseStart_1642067 baseEnd_1642067 := by
    simpa [prefixWord, tailWord_1642067, baseEnd_1642067] using wordTrace_append hprefix tailTrace_1642067
  have hstable : (prefixWord ++ tailWord_1642067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642067).length < 2 ^ (prefixWord ++ tailWord_1642067).sum := by decide
  have hdescent : baseEnd_1642067 < baseStart_1642067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642071 : List Nat := [1, 1, 3, 2, 2, 4, 2, 3, 5]
def baseStart_1642071 : Nat := 118140960795 + 1642071 * 2 ^ 59
def prefixEnd_1642071 : Nat := 4983230072969 + 3 ^ 40 * 1642071 * 2
def baseEnd_1642071 : Nat := 93685743534350013706751

theorem tailTrace_1642071 : CollatzResearch.WordTrace tailWord_1642071 prefixEnd_1642071 93685743534350013706751 := by
  unfold tailWord_1642071
  simp only [CollatzResearch.WordTrace]
  refine ⟨59891249634064685244670067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39927499756043123496446711 59891249634064685244670067)
  ·
    refine ⟨89836874451097027867005101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59891249634064685244670067 89836874451097027867005101)
    ·
      refine ⟨33688827919161385450126913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89836874451097027867005101 33688827919161385450126913)
      ·
        refine ⟨25266620939371039087595185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33688827919161385450126913 25266620939371039087595185)
        ·
          refine ⟨18949965704528279315696389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25266620939371039087595185 18949965704528279315696389)
          ·
            refine ⟨3553118569599052371693073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18949965704528279315696389 3553118569599052371693073)
            ·
              refine ⟨2664838927199289278769805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3553118569599052371693073 2664838927199289278769805)
              ·
                refine ⟨999314597699733479538677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2664838927199289278769805 999314597699733479538677)
                ·
                  refine ⟨93685743534350013706751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 999314597699733479538677 93685743534350013706751)
                  ·
                    rfl

theorem cell23_1642071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 5].length) (baseStart_1642071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642071 prefixEnd_1642071 := by exact prefixLift 1642071
  have htrace : WordTrace (prefixWord ++ tailWord_1642071) baseStart_1642071 baseEnd_1642071 := by
    simpa [prefixWord, tailWord_1642071, baseEnd_1642071] using wordTrace_append hprefix tailTrace_1642071
  have hstable : (prefixWord ++ tailWord_1642071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642071).length < 2 ^ (prefixWord ++ tailWord_1642071).sum := by decide
  have hdescent : baseEnd_1642071 < baseStart_1642071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642124 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 1, 4, 3]
def baseStart_1642124 : Nat := 118140960795 + 1642124 * 2 ^ 59
def prefixEnd_1642124 : Nat := 4983230072969 + 3 ^ 40 * 1642124 * 2
def baseEnd_1642124 : Nat := 843198906283838415998015

theorem tailTrace_1642124 : CollatzResearch.WordTrace tailWord_1642124 prefixEnd_1642124 843198906283838415998015 := by
  unfold tailWord_1642124
  simp only [CollatzResearch.WordTrace]
  refine ⟨29946591351436337648174713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39928788468581783530899617 29946591351436337648174713)
  ·
    refine ⟨22459943513577253236131035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29946591351436337648174713 22459943513577253236131035)
    ·
      refine ⟨33689915270365879854196553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22459943513577253236131035 33689915270365879854196553)
      ·
        refine ⟨25267436452774409890647415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33689915270365879854196553 25267436452774409890647415)
        ·
          refine ⟨37901154679161614835971123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25267436452774409890647415 37901154679161614835971123)
          ·
            refine ⟨56851732018742422253956685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37901154679161614835971123 56851732018742422253956685)
            ·
              refine ⟨21319399507028408345233757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56851732018742422253956685 21319399507028408345233757)
              ·
                refine ⟨7994774815135653129462659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21319399507028408345233757 7994774815135653129462659)
                ·
                  refine ⟨11992162222703479694193989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7994774815135653129462659 11992162222703479694193989)
                  ·
                    refine ⟨2248530416756902442661373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11992162222703479694193989 2248530416756902442661373)
                    ·
                      refine ⟨843198906283838415998015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2248530416756902442661373 843198906283838415998015)
                      ·
                        rfl

theorem cell23_1642124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_1642124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642124 prefixEnd_1642124 := by exact prefixLift 1642124
  have htrace : WordTrace (prefixWord ++ tailWord_1642124) baseStart_1642124 baseEnd_1642124 := by
    simpa [prefixWord, tailWord_1642124, baseEnd_1642124] using wordTrace_append hprefix tailTrace_1642124
  have hstable : (prefixWord ++ tailWord_1642124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642124).length < 2 ^ (prefixWord ++ tailWord_1642124).sum := by decide
  have hdescent : baseEnd_1642124 < baseStart_1642124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642144 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 8]
def baseStart_1642144 : Nat := 118140960795 + 1642144 * 2 ^ 59
def prefixEnd_1642144 : Nat := 4983230072969 + 3 ^ 40 * 1642144 * 2
def baseEnd_1642144 : Nat := 93689908432992037527547

theorem tailTrace_1642144 : CollatzResearch.WordTrace tailWord_1642144 prefixEnd_1642144 93689908432992037527547 := by
  unfold tailWord_1642144
  simp only [CollatzResearch.WordTrace]
  refine ⟨29946956081400109356038743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39929274775200145808051657 29946956081400109356038743)
  ·
    refine ⟨44920434122100164034058115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29946956081400109356038743 44920434122100164034058115)
    ·
      refine ⟨67380651183150246051087173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44920434122100164034058115 67380651183150246051087173)
      ·
        refine ⟨12633872096840671134578845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67380651183150246051087173 12633872096840671134578845)
        ·
          refine ⟨4737702036315251675467067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12633872096840671134578845 4737702036315251675467067)
          ·
            refine ⟨7106553054472877513200601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4737702036315251675467067 7106553054472877513200601)
            ·
              refine ⟨5329914790854658134900451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7106553054472877513200601 5329914790854658134900451)
              ·
                refine ⟨7994872186281987202350677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5329914790854658134900451 7994872186281987202350677)
                ·
                  refine ⟨93689908432992037527547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7994872186281987202350677 93689908432992037527547)
                  ·
                    rfl

theorem cell23_1642144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 8].length) (baseStart_1642144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642144 prefixEnd_1642144 := by exact prefixLift 1642144
  have htrace : WordTrace (prefixWord ++ tailWord_1642144) baseStart_1642144 baseEnd_1642144 := by
    simpa [prefixWord, tailWord_1642144, baseEnd_1642144] using wordTrace_append hprefix tailTrace_1642144
  have hstable : (prefixWord ++ tailWord_1642144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642144).length < 2 ^ (prefixWord ++ tailWord_1642144).sum := by decide
  have hdescent : baseEnd_1642144 < baseStart_1642144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642148 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_1642148 : Nat := 118140960795 + 1642148 * 2 ^ 59
def prefixEnd_1642148 : Nat := 4983230072969 + 3 ^ 40 * 1642148 * 2
def baseEnd_1642148 : Nat := 281070409939848774032635

theorem tailTrace_1642148 : CollatzResearch.WordTrace tailWord_1642148 prefixEnd_1642148 281070409939848774032635 := by
  unfold tailWord_1642148
  simp only [CollatzResearch.WordTrace]
  refine ⟨29947029027392863697611549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39929372036523818263482065 29947029027392863697611549)
  ·
    refine ⟨11230135885272323886604331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29947029027392863697611549 11230135885272323886604331)
    ·
      refine ⟨16845203827908485829906497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11230135885272323886604331 16845203827908485829906497)
      ·
        refine ⟨12633902870931364372429873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16845203827908485829906497 12633902870931364372429873)
        ·
          refine ⟨9475427153198523279322405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12633902870931364372429873 9475427153198523279322405)
          ·
            refine ⟨1776642591224723114872951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9475427153198523279322405 1776642591224723114872951)
            ·
              refine ⟨2664963886837084672309427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1776642591224723114872951 2664963886837084672309427)
              ·
                refine ⟨3997445830255627008464141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2664963886837084672309427 3997445830255627008464141)
                ·
                  refine ⟨1499042186345860128174053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3997445830255627008464141 1499042186345860128174053)
                  ·
                    refine ⟨281070409939848774032635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1499042186345860128174053 281070409939848774032635)
                    ·
                      rfl

theorem cell23_1642148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_1642148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642148 prefixEnd_1642148 := by exact prefixLift 1642148
  have htrace : WordTrace (prefixWord ++ tailWord_1642148) baseStart_1642148 baseEnd_1642148 := by
    simpa [prefixWord, tailWord_1642148, baseEnd_1642148] using wordTrace_append hprefix tailTrace_1642148
  have hstable : (prefixWord ++ tailWord_1642148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642148).length < 2 ^ (prefixWord ++ tailWord_1642148).sum := by decide
  have hdescent : baseEnd_1642148 < baseStart_1642148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642171 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 3, 1, 3]
def baseStart_1642171 : Nat := 118140960795 + 1642171 * 2 ^ 59
def prefixEnd_1642171 : Nat := 4983230072969 + 3 ^ 40 * 1642171 * 2
def baseEnd_1642171 : Nat := 843223039874599732110299

theorem tailTrace_1642171 : CollatzResearch.WordTrace tailWord_1642171 prefixEnd_1642171 843223039874599732110299 := by
  unfold tailWord_1642171
  simp only [CollatzResearch.WordTrace]
  refine ⟨59894896933702402323310367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39929931289134934882206911 59894896933702402323310367)
  ·
    refine ⟨89842345400553603484965551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59894896933702402323310367 89842345400553603484965551)
    ·
      refine ⟨134763518100830405227448327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89842345400553603484965551 134763518100830405227448327)
      ·
        refine ⟨202145277151245607841172491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134763518100830405227448327 202145277151245607841172491)
        ·
          refine ⟨303217915726868411761758737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202145277151245607841172491 303217915726868411761758737)
          ·
            refine ⟨227413436795151308821319053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303217915726868411761758737 227413436795151308821319053)
            ·
              refine ⟨85280038798181740807994645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227413436795151308821319053 85280038798181740807994645)
              ·
                refine ⟨3997501818664769100374749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85280038798181740807994645 3997501818664769100374749)
                ·
                  refine ⟨1499063181999288412640531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3997501818664769100374749 1499063181999288412640531)
                  ·
                    refine ⟨2248594772998932618960797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1499063181999288412640531 2248594772998932618960797)
                    ·
                      refine ⟨843223039874599732110299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2248594772998932618960797 843223039874599732110299)
                      ·
                        rfl

theorem cell23_1642171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 1, 3].length) (baseStart_1642171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642171 prefixEnd_1642171 := by exact prefixLift 1642171
  have htrace : WordTrace (prefixWord ++ tailWord_1642171) baseStart_1642171 baseEnd_1642171 := by
    simpa [prefixWord, tailWord_1642171, baseEnd_1642171] using wordTrace_append hprefix tailTrace_1642171
  have hstable : (prefixWord ++ tailWord_1642171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642171).length < 2 ^ (prefixWord ++ tailWord_1642171).sum := by decide
  have hdescent : baseEnd_1642171 < baseStart_1642171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642181 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 6, 3, 2]
def baseStart_1642181 : Nat := 118140960795 + 1642181 * 2 ^ 59
def prefixEnd_1642181 : Nat := 4983230072969 + 3 ^ 40 * 1642181 * 2
def baseEnd_1642181 : Nat := 843228174681144692985253

theorem tailTrace_1642181 : CollatzResearch.WordTrace tailWord_1642181 prefixEnd_1642181 843228174681144692985253 := by
  unfold tailWord_1642181
  simp only [CollatzResearch.WordTrace]
  refine ⟨59895261663666174031174397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39930174442444116020782931 59895261663666174031174397)
  ·
    refine ⟨22460723123874815261690399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59895261663666174031174397 22460723123874815261690399)
    ·
      refine ⟨33691084685812222892535599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22460723123874815261690399 33691084685812222892535599)
      ·
        refine ⟨50536627028718334338803399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33691084685812222892535599 50536627028718334338803399)
        ·
          refine ⟨75804940543077501508205099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50536627028718334338803399 75804940543077501508205099)
          ·
            refine ⟨113707410814616252262307649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75804940543077501508205099 113707410814616252262307649)
            ·
              refine ⟨85280558110962189196730737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113707410814616252262307649 85280558110962189196730737)
              ·
                refine ⟨63960418583221641897548053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85280558110962189196730737 63960418583221641897548053)
                ·
                  refine ⟨2998144621088514463947565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63960418583221641897548053 2998144621088514463947565)
                  ·
                    refine ⟨1124304232908192923980337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2998144621088514463947565 1124304232908192923980337)
                    ·
                      refine ⟨843228174681144692985253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1124304232908192923980337 843228174681144692985253)
                      ·
                        rfl

theorem cell23_1642181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 3, 2].length) (baseStart_1642181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642181 prefixEnd_1642181 := by exact prefixLift 1642181
  have htrace : WordTrace (prefixWord ++ tailWord_1642181) baseStart_1642181 baseEnd_1642181 := by
    simpa [prefixWord, tailWord_1642181, baseEnd_1642181] using wordTrace_append hprefix tailTrace_1642181
  have hstable : (prefixWord ++ tailWord_1642181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642181).length < 2 ^ (prefixWord ++ tailWord_1642181).sum := by decide
  have hdescent : baseEnd_1642181 < baseStart_1642181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642221 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1642221 : Nat := 118140960795 + 1642221 * 2 ^ 59
def prefixEnd_1642221 : Nat := 4983230072969 + 3 ^ 40 * 1642221 * 2
def baseEnd_1642221 : Nat := 281082904635774845495023

theorem tailTrace_1642221 : CollatzResearch.WordTrace tailWord_1642221 prefixEnd_1642221 281082904635774845495023 := by
  unfold tailWord_1642221
  simp only [CollatzResearch.WordTrace]
  refine ⟨59896720583521260862630517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39931147055680840575087011 59896720583521260862630517)
  ·
    refine ⟨5615317554705118205871611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59896720583521260862630517 5615317554705118205871611)
    ·
      refine ⟨8422976332057677308807417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5615317554705118205871611 8422976332057677308807417)
      ·
        refine ⟨6317232249043257981605563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8422976332057677308807417 6317232249043257981605563)
        ·
          refine ⟨9475848373564886972408345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6317232249043257981605563 9475848373564886972408345)
          ·
            refine ⟨7106886280173665229306259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9475848373564886972408345 7106886280173665229306259)
            ·
              refine ⟨10660329420260497843959389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7106886280173665229306259 10660329420260497843959389)
              ·
                refine ⟨3997623532597686691484771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10660329420260497843959389 3997623532597686691484771)
                ·
                  refine ⟨5996435298896530037227157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3997623532597686691484771 5996435298896530037227157)
                  ·
                    refine ⟨281082904635774845495023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5996435298896530037227157 281082904635774845495023)
                    ·
                      rfl

theorem cell23_1642221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1642221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642221 prefixEnd_1642221 := by exact prefixLift 1642221
  have htrace : WordTrace (prefixWord ++ tailWord_1642221) baseStart_1642221 baseEnd_1642221 := by
    simpa [prefixWord, tailWord_1642221, baseEnd_1642221] using wordTrace_append hprefix tailTrace_1642221
  have hstable : (prefixWord ++ tailWord_1642221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642221).length < 2 ^ (prefixWord ++ tailWord_1642221).sum := by decide
  have hdescent : baseEnd_1642221 < baseStart_1642221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642231 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 3]
def baseStart_1642231 : Nat := 118140960795 + 1642231 * 2 ^ 59
def prefixEnd_1642231 : Nat := 4983230072969 + 3 ^ 40 * 1642231 * 2
def baseEnd_1642231 : Nat := 843253848713869497360023

theorem tailTrace_1642231 : CollatzResearch.WordTrace tailWord_1642231 prefixEnd_1642231 843253848713869497360023 := by
  unfold tailWord_1642231
  simp only [CollatzResearch.WordTrace]
  refine ⟨59897085313485032570494547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39931390208990021713663031 59897085313485032570494547)
  ·
    refine ⟨89845627970227548855741821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59897085313485032570494547 89845627970227548855741821)
    ·
      refine ⟨33692110488835330820903183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89845627970227548855741821 33692110488835330820903183)
      ·
        refine ⟨50538165733252996231354775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33692110488835330820903183 50538165733252996231354775)
        ·
          refine ⟨75807248599879494347032163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50538165733252996231354775 75807248599879494347032163)
          ·
            refine ⟨113710872899819241520548245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75807248599879494347032163 113710872899819241520548245)
            ·
              refine ⟨5330197167179026946275699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113710872899819241520548245 5330197167179026946275699)
              ·
                refine ⟨7995295750768540419413549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5330197167179026946275699 7995295750768540419413549)
                ·
                  refine ⟨2998235906538202657280081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7995295750768540419413549 2998235906538202657280081)
                  ·
                    refine ⟨2248676929903651992960061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2998235906538202657280081 2248676929903651992960061)
                    ·
                      refine ⟨843253848713869497360023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2248676929903651992960061 843253848713869497360023)
                      ·
                        rfl

theorem cell23_1642231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_1642231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642231 prefixEnd_1642231 := by exact prefixLift 1642231
  have htrace : WordTrace (prefixWord ++ tailWord_1642231) baseStart_1642231 baseEnd_1642231 := by
    simpa [prefixWord, tailWord_1642231, baseEnd_1642231] using wordTrace_append hprefix tailTrace_1642231
  have hstable : (prefixWord ++ tailWord_1642231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642231).length < 2 ^ (prefixWord ++ tailWord_1642231).sum := by decide
  have hdescent : baseEnd_1642231 < baseStart_1642231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642241 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_1642241 : Nat := 118140960795 + 1642241 * 2 ^ 59
def prefixEnd_1642241 : Nat := 4983230072969 + 3 ^ 40 * 1642241 * 2
def baseEnd_1642241 : Nat := 843258983520414458234977

theorem tailTrace_1642241 : CollatzResearch.WordTrace tailWord_1642241 prefixEnd_1642241 843258983520414458234977 := by
  unfold tailWord_1642241
  simp only [CollatzResearch.WordTrace]
  refine ⟨59897450043448804278358577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39931633362299202852239051 59897450043448804278358577)
  ·
    refine ⟨44923087532586603208768933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59897450043448804278358577 44923087532586603208768933)
    ·
      refine ⟨8423078912359988101644175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44923087532586603208768933 8423078912359988101644175)
      ·
        refine ⟨12634618368539982152466263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8423078912359988101644175 12634618368539982152466263)
        ·
          refine ⟨18951927552809973228699395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12634618368539982152466263 18951927552809973228699395)
          ·
            refine ⟨28427891329214959843049093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18951927552809973228699395 28427891329214959843049093)
            ·
              refine ⟨5330229624227804970571705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28427891329214959843049093 5330229624227804970571705)
              ·
                refine ⟨3997672218170853727928779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5330229624227804970571705 3997672218170853727928779)
                ·
                  refine ⟨5996508327256280591893169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3997672218170853727928779 5996508327256280591893169)
                  ·
                    refine ⟨4497381245442210443919877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5996508327256280591893169 4497381245442210443919877)
                    ·
                      refine ⟨843258983520414458234977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4497381245442210443919877 843258983520414458234977)
                      ·
                        rfl

theorem cell23_1642241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_1642241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642241 prefixEnd_1642241 := by exact prefixLift 1642241
  have htrace : WordTrace (prefixWord ++ tailWord_1642241) baseStart_1642241 baseEnd_1642241 := by
    simpa [prefixWord, tailWord_1642241, baseEnd_1642241] using wordTrace_append hprefix tailTrace_1642241
  have hstable : (prefixWord ++ tailWord_1642241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642241).length < 2 ^ (prefixWord ++ tailWord_1642241).sum := by decide
  have hdescent : baseEnd_1642241 < baseStart_1642241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642246 : List Nat := [6, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_1642246 : Nat := 118140960795 + 1642246 * 2 ^ 59
def prefixEnd_1642246 : Nat := 4983230072969 + 3 ^ 40 * 1642246 * 2
def baseEnd_1642246 : Nat := 93695727880409659852495

theorem tailTrace_1642246 : CollatzResearch.WordTrace tailWord_1642246 prefixEnd_1642246 93695727880409659852495 := by
  unfold tailWord_1642246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871801012763459066634081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39931754938953793421527061 1871801012763459066634081)
  ·
    refine ⟨1403850759572594299975561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1871801012763459066634081 1403850759572594299975561)
    ·
      refine ⟨1052888069679445724981671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1403850759572594299975561 1052888069679445724981671)
      ·
        refine ⟨1579332104519168587472507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1052888069679445724981671 1579332104519168587472507)
        ·
          refine ⟨2368998156778752881208761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1579332104519168587472507 2368998156778752881208761)
          ·
            refine ⟨1776748617584064660906571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2368998156778752881208761 1776748617584064660906571)
            ·
              refine ⟨2665122926376096991359857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1776748617584064660906571 2665122926376096991359857)
              ·
                refine ⟨1998842194782072743519893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2665122926376096991359857 1998842194782072743519893)
                ·
                  refine ⟨93695727880409659852495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1998842194782072743519893 93695727880409659852495)
                  ·
                    rfl

theorem cell23_1642246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_1642246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642246 prefixEnd_1642246 := by exact prefixLift 1642246
  have htrace : WordTrace (prefixWord ++ tailWord_1642246) baseStart_1642246 baseEnd_1642246 := by
    simpa [prefixWord, tailWord_1642246, baseEnd_1642246] using wordTrace_append hprefix tailTrace_1642246
  have hstable : (prefixWord ++ tailWord_1642246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642246).length < 2 ^ (prefixWord ++ tailWord_1642246).sum := by decide
  have hdescent : baseEnd_1642246 < baseStart_1642246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642248 : List Nat := [2, 1, 3, 2, 2, 1, 3, 3, 1, 2, 3]
def baseStart_1642248 : Nat := 118140960795 + 1642248 * 2 ^ 59
def prefixEnd_1642248 : Nat := 4983230072969 + 3 ^ 40 * 1642248 * 2
def baseEnd_1642248 : Nat := 843262577884995930847445

theorem tailTrace_1642248 : CollatzResearch.WordTrace tailWord_1642248 prefixEnd_1642248 843262577884995930847445 := by
  unfold tailWord_1642248
  simp only [CollatzResearch.WordTrace]
  refine ⟨29948852677211722236931699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39931803569615629649242265 29948852677211722236931699)
  ·
    refine ⟨44923279015817583355397549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29948852677211722236931699 44923279015817583355397549)
    ·
      refine ⟨16846229630931593758274081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44923279015817583355397549 16846229630931593758274081)
      ·
        refine ⟨12634672223198695318705561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16846229630931593758274081 12634672223198695318705561)
        ·
          refine ⟨9476004167399021489029171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12634672223198695318705561 9476004167399021489029171)
          ·
            refine ⟨14214006251098532233543757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9476004167399021489029171 14214006251098532233543757)
            ·
              refine ⟨5330252344161949587578909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14214006251098532233543757 5330252344161949587578909)
              ·
                refine ⟨1998844629060731095342091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5330252344161949587578909 1998844629060731095342091)
                ·
                  refine ⟨2998266943591096643013137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998844629060731095342091 2998266943591096643013137)
                  ·
                    refine ⟨2248700207693322482259853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2998266943591096643013137 2248700207693322482259853)
                    ·
                      refine ⟨843262577884995930847445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2248700207693322482259853 843262577884995930847445)
                      ·
                        rfl

theorem cell23_1642248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_1642248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642248 prefixEnd_1642248 := by exact prefixLift 1642248
  have htrace : WordTrace (prefixWord ++ tailWord_1642248) baseStart_1642248 baseEnd_1642248 := by
    simpa [prefixWord, tailWord_1642248, baseEnd_1642248] using wordTrace_append hprefix tailTrace_1642248
  have hstable : (prefixWord ++ tailWord_1642248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642248).length < 2 ^ (prefixWord ++ tailWord_1642248).sum := by decide
  have hdescent : baseEnd_1642248 < baseStart_1642248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642264 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 1, 9]
def baseStart_1642264 : Nat := 118140960795 + 1642264 * 2 ^ 59
def prefixEnd_1642264 : Nat := 4983230072969 + 3 ^ 40 * 1642264 * 2
def baseEnd_1642264 : Nat := 281090264525155956082457

theorem tailTrace_1642264 : CollatzResearch.WordTrace tailWord_1642264 prefixEnd_1642264 281090264525155956082457 := by
  unfold tailWord_1642264
  simp only [CollatzResearch.WordTrace]
  refine ⟨29949144461182739603222923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39932192614910319470963897 29949144461182739603222923)
  ·
    refine ⟨44923716691774109404834385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29949144461182739603222923 44923716691774109404834385)
    ·
      refine ⟨33692787518830582053625789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44923716691774109404834385 33692787518830582053625789)
      ·
        refine ⟨12634795319561468270109671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33692787518830582053625789 12634795319561468270109671)
        ·
          refine ⟨18952192979342202405164507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12634795319561468270109671 18952192979342202405164507)
          ·
            refine ⟨28428289469013303607746761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18952192979342202405164507 28428289469013303607746761)
            ·
              refine ⟨21321217101759977705810071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28428289469013303607746761 21321217101759977705810071)
              ·
                refine ⟨31981825652639966558715107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21321217101759977705810071 31981825652639966558715107)
                ·
                  refine ⟨47972738478959949838072661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31981825652639966558715107 47972738478959949838072661)
                  ·
                    refine ⟨281090264525155956082457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 47972738478959949838072661 281090264525155956082457)
                    ·
                      rfl

theorem cell23_1642264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_1642264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642264 prefixEnd_1642264 := by exact prefixLift 1642264
  have htrace : WordTrace (prefixWord ++ tailWord_1642264) baseStart_1642264 baseEnd_1642264 := by
    simpa [prefixWord, tailWord_1642264, baseEnd_1642264] using wordTrace_append hprefix tailTrace_1642264
  have hstable : (prefixWord ++ tailWord_1642264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642264).length < 2 ^ (prefixWord ++ tailWord_1642264).sum := by decide
  have hdescent : baseEnd_1642264 < baseStart_1642264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642338 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1642338 : Nat := 118140960795 + 1642338 * 2 ^ 59
def prefixEnd_1642338 : Nat := 4983230072969 + 3 ^ 40 * 1642338 * 2
def baseEnd_1642338 : Nat := 843308791143900578722031

theorem tailTrace_1642338 : CollatzResearch.WordTrace tailWord_1642338 prefixEnd_1642338 843308791143900578722031 := by
  unfold tailWord_1642338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14975246981024347461159917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39933991949398259896426445 14975246981024347461159917)
  ·
    refine ⟨5615717617884130297934969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14975246981024347461159917 5615717617884130297934969)
    ·
      refine ⟨4211788213413097723451227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5615717617884130297934969 4211788213413097723451227)
      ·
        refine ⟨6317682320119646585176841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4211788213413097723451227 6317682320119646585176841)
        ·
          refine ⟨4738261740089734938882631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6317682320119646585176841 4738261740089734938882631)
          ·
            refine ⟨7107392610134602408323947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4738261740089734938882631 7107392610134602408323947)
            ·
              refine ⟨10661088915201903612485921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7107392610134602408323947 10661088915201903612485921)
              ·
                refine ⟨7995816686401427709364441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10661088915201903612485921 7995816686401427709364441)
                ·
                  refine ⟨5996862514801070782023331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7995816686401427709364441 5996862514801070782023331)
                  ·
                    refine ⟨8995293772201606173034997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5996862514801070782023331 8995293772201606173034997)
                    ·
                      refine ⟨843308791143900578722031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8995293772201606173034997 843308791143900578722031)
                      ·
                        rfl

theorem cell23_1642338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1642338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642338 prefixEnd_1642338 := by exact prefixLift 1642338
  have htrace : WordTrace (prefixWord ++ tailWord_1642338) baseStart_1642338 baseEnd_1642338 := by
    simpa [prefixWord, tailWord_1642338, baseEnd_1642338] using wordTrace_append hprefix tailTrace_1642338
  have hstable : (prefixWord ++ tailWord_1642338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642338).length < 2 ^ (prefixWord ++ tailWord_1642338).sum := by decide
  have hdescent : baseEnd_1642338 < baseStart_1642338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642339 : List Nat := [1, 1, 1, 5, 5, 1, 1, 2, 1, 3, 2]
def baseStart_1642339 : Nat := 118140960795 + 1642339 * 2 ^ 59
def prefixEnd_1642339 : Nat := 4983230072969 + 3 ^ 40 * 1642339 * 2
def baseEnd_1642339 : Nat := 843309304624555074809527

theorem tailTrace_1642339 : CollatzResearch.WordTrace tailWord_1642339 prefixEnd_1642339 843309304624555074809527 := by
  unfold tailWord_1642339
  simp only [CollatzResearch.WordTrace]
  refine ⟨59901024397093767015426071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39934016264729178010284047 59901024397093767015426071)
  ·
    refine ⟨89851536595640650523139107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59901024397093767015426071 89851536595640650523139107)
    ·
      refine ⟨134777304893460975784708661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89851536595640650523139107 134777304893460975784708661)
      ·
        refine ⟨12635372333761966479816437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134777304893460975784708661 12635372333761966479816437)
        ·
          refine ⟨1184566156290184357482791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12635372333761966479816437 1184566156290184357482791)
          ·
            refine ⟨1776849234435276536224187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184566156290184357482791 1776849234435276536224187)
            ·
              refine ⟨2665273851652914804336281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1776849234435276536224187 2665273851652914804336281)
              ·
                refine ⟨1998955388739686103252211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2665273851652914804336281 1998955388739686103252211)
                ·
                  refine ⟨2998433083109529154878317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1998955388739686103252211 2998433083109529154878317)
                  ·
                    refine ⟨1124412406166073433079369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2998433083109529154878317 1124412406166073433079369)
                    ·
                      refine ⟨843309304624555074809527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1124412406166073433079369 843309304624555074809527)
                      ·
                        rfl

theorem cell23_1642339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_1642339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642339 prefixEnd_1642339 := by exact prefixLift 1642339
  have htrace : WordTrace (prefixWord ++ tailWord_1642339) baseStart_1642339 baseEnd_1642339 := by
    simpa [prefixWord, tailWord_1642339, baseEnd_1642339] using wordTrace_append hprefix tailTrace_1642339
  have hstable : (prefixWord ++ tailWord_1642339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642339).length < 2 ^ (prefixWord ++ tailWord_1642339).sum := by decide
  have hdescent : baseEnd_1642339 < baseStart_1642339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642351 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 3]
def baseStart_1642351 : Nat := 118140960795 + 1642351 * 2 ^ 59
def prefixEnd_1642351 : Nat := 4983230072969 + 3 ^ 40 * 1642351 * 2
def baseEnd_1642351 : Nat := 843315466392409027859471

theorem tailTrace_1642351 : CollatzResearch.WordTrace tailWord_1642351 prefixEnd_1642351 843315466392409027859471 := by
  unfold tailWord_1642351
  simp only [CollatzResearch.WordTrace]
  refine ⟨59901462073050293064862907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39934308048700195376575271 59901462073050293064862907)
  ·
    refine ⟨89852193109575439597294361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59901462073050293064862907 89852193109575439597294361)
    ·
      refine ⟨67389144832181579697970771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89852193109575439597294361 67389144832181579697970771)
      ·
        refine ⟨101083717248272369546956157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67389144832181579697970771 101083717248272369546956157)
        ·
          refine ⟨37906393968102138580108559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101083717248272369546956157 37906393968102138580108559)
          ·
            refine ⟨56859590952153207870162839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37906393968102138580108559 56859590952153207870162839)
            ·
              refine ⟨85289386428229811805244259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56859590952153207870162839 85289386428229811805244259)
              ·
                refine ⟨127934079642344717707866389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85289386428229811805244259 127934079642344717707866389)
                ·
                  refine ⟨5996909983234908642556237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127934079642344717707866389 5996909983234908642556237)
                  ·
                    refine ⟨2248841243713090740958589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5996909983234908642556237 2248841243713090740958589)
                    ·
                      refine ⟨843315466392409027859471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2248841243713090740958589 843315466392409027859471)
                      ·
                        rfl

theorem cell23_1642351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 3].length) (baseStart_1642351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642351 prefixEnd_1642351 := by exact prefixLift 1642351
  have htrace : WordTrace (prefixWord ++ tailWord_1642351) baseStart_1642351 baseEnd_1642351 := by
    simpa [prefixWord, tailWord_1642351, baseEnd_1642351] using wordTrace_append hprefix tailTrace_1642351
  have hstable : (prefixWord ++ tailWord_1642351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642351).length < 2 ^ (prefixWord ++ tailWord_1642351).sum := by decide
  have hdescent : baseEnd_1642351 < baseStart_1642351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642375 : List Nat := [1, 1, 4, 2, 4, 1, 1, 4, 5]
def baseStart_1642375 : Nat := 118140960795 + 1642375 * 2 ^ 59
def prefixEnd_1642375 : Nat := 4983230072969 + 3 ^ 40 * 1642375 * 2
def baseEnd_1642375 : Nat := 93703087769790770439929

theorem tailTrace_1642375 : CollatzResearch.WordTrace tailWord_1642375 prefixEnd_1642375 93703087769790770439929 := by
  unfold tailWord_1642375
  simp only [CollatzResearch.WordTrace]
  refine ⟨59902337424963345163736579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39934891616642230109157719 59902337424963345163736579)
  ·
    refine ⟨89853506137445017745604869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59902337424963345163736579 89853506137445017745604869)
    ·
      refine ⟨16847532400770940827300913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89853506137445017745604869 16847532400770940827300913)
      ·
        refine ⟨12635649300578205620475685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16847532400770940827300913 12635649300578205620475685)
        ·
          refine ⟨2369184243858413553839191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12635649300578205620475685 2369184243858413553839191)
          ·
            refine ⟨3553776365787620330758787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369184243858413553839191 3553776365787620330758787)
            ·
              refine ⟨5330664548681430496138181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3553776365787620330758787 5330664548681430496138181)
              ·
                refine ⟨999499602877768218025909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5330664548681430496138181 999499602877768218025909)
                ·
                  refine ⟨93703087769790770439929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 999499602877768218025909 93703087769790770439929)
                  ·
                    rfl

theorem cell23_1642375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 5].length) (baseStart_1642375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642375 prefixEnd_1642375 := by exact prefixLift 1642375
  have htrace : WordTrace (prefixWord ++ tailWord_1642375) baseStart_1642375 baseEnd_1642375 := by
    simpa [prefixWord, tailWord_1642375, baseEnd_1642375] using wordTrace_append hprefix tailTrace_1642375
  have hstable : (prefixWord ++ tailWord_1642375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642375).length < 2 ^ (prefixWord ++ tailWord_1642375).sum := by decide
  have hdescent : baseEnd_1642375 < baseStart_1642375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642431 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 8]
def baseStart_1642431 : Nat := 118140960795 + 1642431 * 2 ^ 59
def prefixEnd_1642431 : Nat := 4983230072969 + 3 ^ 40 * 1642431 * 2
def baseEnd_1642431 : Nat := 93706282760529857206567

theorem tailTrace_1642431 : CollatzResearch.WordTrace tailWord_1642431 prefixEnd_1642431 93706282760529857206567 := by
  unfold tailWord_1642431
  simp only [CollatzResearch.WordTrace]
  refine ⟨59904379912760466727775147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39936253275173644485183431 59904379912760466727775147)
  ·
    refine ⟨89856569869140700091662721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59904379912760466727775147 89856569869140700091662721)
    ·
      refine ⟨67392427401855525068747041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89856569869140700091662721 67392427401855525068747041)
      ·
        refine ⟨50544320551391643801560281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67392427401855525068747041 50544320551391643801560281)
        ·
          refine ⟨37908240413543732851170211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50544320551391643801560281 37908240413543732851170211)
          ·
            refine ⟨56862360620315599276755317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37908240413543732851170211 56862360620315599276755317)
            ·
              refine ⟨5330846308154587432195811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56862360620315599276755317 5330846308154587432195811)
              ·
                refine ⟨7996269462231881148293717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5330846308154587432195811 7996269462231881148293717)
                ·
                  refine ⟨93706282760529857206567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7996269462231881148293717 93706282760529857206567)
                  ·
                    rfl

theorem cell23_1642431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 8].length) (baseStart_1642431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642431 prefixEnd_1642431 := by exact prefixLift 1642431
  have htrace : WordTrace (prefixWord ++ tailWord_1642431) baseStart_1642431 baseEnd_1642431 := by
    simpa [prefixWord, tailWord_1642431, baseEnd_1642431] using wordTrace_append hprefix tailTrace_1642431
  have hstable : (prefixWord ++ tailWord_1642431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642431).length < 2 ^ (prefixWord ++ tailWord_1642431).sum := by decide
  have hdescent : baseEnd_1642431 < baseStart_1642431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642486 : List Nat := [5, 1, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_1642486 : Nat := 118140960795 + 1642486 * 2 ^ 59
def prefixEnd_1642486 : Nat := 4983230072969 + 3 ^ 40 * 1642486 * 2
def baseEnd_1642486 : Nat := 281128262093588666557117

theorem tailTrace_1642486 : CollatzResearch.WordTrace tailWord_1642486 prefixEnd_1642486 281128262093588666557117 := by
  unfold tailWord_1642486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3744149120472575695064207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39937590618374140747351541 3744149120472575695064207)
  ·
    refine ⟨5616223680708863542596311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3744149120472575695064207 5616223680708863542596311)
    ·
      refine ⟨8424335521063295313894467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5616223680708863542596311 8424335521063295313894467)
      ·
        refine ⟨12636503281594942970841701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8424335521063295313894467 12636503281594942970841701)
        ·
          refine ⟨2369344365299051807032819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12636503281594942970841701 2369344365299051807032819)
          ·
            refine ⟨3554016547948577710549229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369344365299051807032819 3554016547948577710549229)
            ·
              refine ⟨1332756205480716641455961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3554016547948577710549229 1332756205480716641455961)
              ·
                refine ⟨999567154110537481091971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332756205480716641455961 999567154110537481091971)
                ·
                  refine ⟨1499350731165806221637957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 999567154110537481091971 1499350731165806221637957)
                  ·
                    refine ⟨281128262093588666557117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1499350731165806221637957 281128262093588666557117)
                    ·
                      rfl

theorem cell23_1642486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_1642486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642486 prefixEnd_1642486 := by exact prefixLift 1642486
  have htrace : WordTrace (prefixWord ++ tailWord_1642486) baseStart_1642486 baseEnd_1642486 := by
    simpa [prefixWord, tailWord_1642486, baseEnd_1642486] using wordTrace_append hprefix tailTrace_1642486
  have hstable : (prefixWord ++ tailWord_1642486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642486).length < 2 ^ (prefixWord ++ tailWord_1642486).sum := by decide
  have hdescent : baseEnd_1642486 < baseStart_1642486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642508 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 1, 6]
def baseStart_1642508 : Nat := 118140960795 + 1642508 * 2 ^ 59
def prefixEnd_1642508 : Nat := 4983230072969 + 3 ^ 40 * 1642508 * 2
def baseEnd_1642508 : Nat := 281132027618388304532083

theorem tailTrace_1642508 : CollatzResearch.WordTrace tailWord_1642508 prefixEnd_1642508 281132027618388304532083 := by
  unfold tailWord_1642508
  simp only [CollatzResearch.WordTrace]
  refine ⟨29953594166740754439164089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39938125555654339252218785 29953594166740754439164089)
  ·
    refine ⟨22465195625055565829373067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29953594166740754439164089 22465195625055565829373067)
    ·
      refine ⟨33697793437583348744059601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22465195625055565829373067 33697793437583348744059601)
      ·
        refine ⟨25273345078187511558044701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33697793437583348744059601 25273345078187511558044701)
        ·
          refine ⟨9477504404320316834266763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25273345078187511558044701 9477504404320316834266763)
          ·
            refine ⟨14216256606480475251400145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9477504404320316834266763 14216256606480475251400145)
            ·
              refine ⟨10662192454860356438550109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14216256606480475251400145 10662192454860356438550109)
              ·
                refine ⟨3998322170572633664456291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10662192454860356438550109 3998322170572633664456291)
                ·
                  refine ⟨5997483255858950496684437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998322170572633664456291 5997483255858950496684437)
                  ·
                    refine ⟨281132027618388304532083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5997483255858950496684437 281132027618388304532083)
                    ·
                      rfl

theorem cell23_1642508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_1642508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642508 prefixEnd_1642508 := by exact prefixLift 1642508
  have htrace : WordTrace (prefixWord ++ tailWord_1642508) baseStart_1642508 baseEnd_1642508 := by
    simpa [prefixWord, tailWord_1642508, baseEnd_1642508] using wordTrace_append hprefix tailTrace_1642508
  have hstable : (prefixWord ++ tailWord_1642508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642508).length < 2 ^ (prefixWord ++ tailWord_1642508).sum := by decide
  have hdescent : baseEnd_1642508 < baseStart_1642508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642515 : List Nat := [1, 1, 1, 2, 1, 4, 5, 2, 1, 1, 4]
def baseStart_1642515 : Nat := 118140960795 + 1642515 * 2 ^ 59
def prefixEnd_1642515 : Nat := 4983230072969 + 3 ^ 40 * 1642515 * 2
def baseEnd_1642515 : Nat := 843399677219746386208717

theorem tailTrace_1642515 : CollatzResearch.WordTrace tailWord_1642515 prefixEnd_1642515 843399677219746386208717 := by
  unfold tailWord_1642515
  simp only [CollatzResearch.WordTrace]
  refine ⟨59907443644456149073832999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39938295762970766049221999 59907443644456149073832999)
  ·
    refine ⟨89861165466684223610749499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59907443644456149073832999 89861165466684223610749499)
    ·
      refine ⟨134791748200026335416124249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89861165466684223610749499 134791748200026335416124249)
      ·
        refine ⟨101093811150019751562093187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134791748200026335416124249 101093811150019751562093187)
        ·
          refine ⟨151640716725029627343139781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101093811150019751562093187 151640716725029627343139781)
          ·
            refine ⟨28432634385943055126838709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151640716725029627343139781 28432634385943055126838709)
            ·
              refine ⟨2665559473682161418141129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28432634385943055126838709 2665559473682161418141129)
              ·
                refine ⟨1999169605261621063605847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2665559473682161418141129 1999169605261621063605847)
                ·
                  refine ⟨2998754407892431595408771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1999169605261621063605847 2998754407892431595408771)
                  ·
                    refine ⟨4498131611838647393113157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2998754407892431595408771 4498131611838647393113157)
                    ·
                      refine ⟨843399677219746386208717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4498131611838647393113157 843399677219746386208717)
                      ·
                        rfl

theorem cell23_1642515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 1, 4].length) (baseStart_1642515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642515 prefixEnd_1642515 := by exact prefixLift 1642515
  have htrace : WordTrace (prefixWord ++ tailWord_1642515) baseStart_1642515 baseEnd_1642515 := by
    simpa [prefixWord, tailWord_1642515, baseEnd_1642515] using wordTrace_append hprefix tailTrace_1642515
  have hstable : (prefixWord ++ tailWord_1642515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642515).length < 2 ^ (prefixWord ++ tailWord_1642515).sum := by decide
  have hdescent : baseEnd_1642515 < baseStart_1642515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642519 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 2, 3, 2]
def baseStart_1642519 : Nat := 118140960795 + 1642519 * 2 ^ 59
def prefixEnd_1642519 : Nat := 4983230072969 + 3 ^ 40 * 1642519 * 2
def baseEnd_1642519 : Nat := 843401731142364370558699

theorem tailTrace_1642519 : CollatzResearch.WordTrace tailWord_1642519 prefixEnd_1642519 843401731142364370558699 := by
  unfold tailWord_1642519
  simp only [CollatzResearch.WordTrace]
  refine ⟨59907589536441657756978611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39938393024294438504652407 59907589536441657756978611)
  ·
    refine ⟨89861384304662486635467917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59907589536441657756978611 89861384304662486635467917)
    ·
      refine ⟨33698019114248432488300469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89861384304662486635467917 33698019114248432488300469)
      ·
        refine ⟨3159189291960790545778169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33698019114248432488300469 3159189291960790545778169)
        ·
          refine ⟨2369391968970592909333627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3159189291960790545778169 2369391968970592909333627)
          ·
            refine ⟨3554087953455889364000441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369391968970592909333627 3554087953455889364000441)
            ·
              refine ⟨2665565965091917023000331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3554087953455889364000441 2665565965091917023000331)
              ·
                refine ⟨3998348947637875534500497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2665565965091917023000331 3998348947637875534500497)
                ·
                  refine ⟨2998761710728406650875373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3998348947637875534500497 2998761710728406650875373)
                  ·
                    refine ⟨1124535641523152494078265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2998761710728406650875373 1124535641523152494078265)
                    ·
                      refine ⟨843401731142364370558699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1124535641523152494078265 843401731142364370558699)
                      ·
                        rfl

theorem cell23_1642519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_1642519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642519 prefixEnd_1642519 := by exact prefixLift 1642519
  have htrace : WordTrace (prefixWord ++ tailWord_1642519) baseStart_1642519 baseEnd_1642519 := by
    simpa [prefixWord, tailWord_1642519, baseEnd_1642519] using wordTrace_append hprefix tailTrace_1642519
  have hstable : (prefixWord ++ tailWord_1642519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642519).length < 2 ^ (prefixWord ++ tailWord_1642519).sum := by decide
  have hdescent : baseEnd_1642519 < baseStart_1642519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642525 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_1642525 : Nat := 118140960795 + 1642525 * 2 ^ 59
def prefixEnd_1642525 : Nat := 4983230072969 + 3 ^ 40 * 1642525 * 2
def baseEnd_1642525 : Nat := 281134937342097115694557

theorem tailTrace_1642525 : CollatzResearch.WordTrace tailWord_1642525 prefixEnd_1642525 281134937342097115694557 := by
  unfold tailWord_1642525
  simp only [CollatzResearch.WordTrace]
  refine ⟨59907808374419920781697029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39938538916279947187798019 59907808374419920781697029)
  ·
    refine ⟨11232714070203735146568193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59907808374419920781697029 11232714070203735146568193)
    ·
      refine ⟨8424535552652801359926145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11232714070203735146568193 8424535552652801359926145)
      ·
        refine ⟨6318401664489601019944609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8424535552652801359926145 6318401664489601019944609)
        ·
          refine ⟨4738801248367200764958457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6318401664489601019944609 4738801248367200764958457)
          ·
            refine ⟨3554100936275400573718843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4738801248367200764958457 3554100936275400573718843)
            ·
              refine ⟨5331151404413100860578265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3554100936275400573718843 5331151404413100860578265)
              ·
                refine ⟨3998363553309825645433699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5331151404413100860578265 3998363553309825645433699)
                ·
                  refine ⟨5997545329964738468150549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998363553309825645433699 5997545329964738468150549)
                  ·
                    refine ⟨281134937342097115694557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5997545329964738468150549 281134937342097115694557)
                    ·
                      rfl

theorem cell23_1642525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_1642525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642525 prefixEnd_1642525 := by exact prefixLift 1642525
  have htrace : WordTrace (prefixWord ++ tailWord_1642525) baseStart_1642525 baseEnd_1642525 := by
    simpa [prefixWord, tailWord_1642525, baseEnd_1642525] using wordTrace_append hprefix tailTrace_1642525
  have hstable : (prefixWord ++ tailWord_1642525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642525).length < 2 ^ (prefixWord ++ tailWord_1642525).sum := by decide
  have hdescent : baseEnd_1642525 < baseStart_1642525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642538 : List Nat := [3, 1, 4, 1, 2, 12]
def baseStart_1642538 : Nat := 118140960795 + 1642538 * 2 ^ 59
def prefixEnd_1642538 : Nat := 4983230072969 + 3 ^ 40 * 1642538 * 2
def baseEnd_1642538 : Nat := 3470829165739916856877

theorem tailTrace_1642538 : CollatzResearch.WordTrace tailWord_1642538 prefixEnd_1642538 3470829165739916856877 := by
  unfold tailWord_1642538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14977070630843206000480067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39938855015581882667946845 14977070630843206000480067)
  ·
    refine ⟨22465605946264809000720101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14977070630843206000480067 22465605946264809000720101)
    ·
      refine ⟨4212301114924651687635019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22465605946264809000720101 4212301114924651687635019)
      ·
        refine ⟨6318451672386977531452529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4212301114924651687635019 6318451672386977531452529)
        ·
          refine ⟨4738838754290233148589397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6318451672386977531452529 4738838754290233148589397)
          ·
            refine ⟨3470829165739916856877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4738838754290233148589397 3470829165739916856877)
            ·
              rfl

theorem cell23_1642538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 12].length) (baseStart_1642538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642538 prefixEnd_1642538 := by exact prefixLift 1642538
  have htrace : WordTrace (prefixWord ++ tailWord_1642538) baseStart_1642538 baseEnd_1642538 := by
    simpa [prefixWord, tailWord_1642538, baseEnd_1642538] using wordTrace_append hprefix tailTrace_1642538
  have hstable : (prefixWord ++ tailWord_1642538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642538).length < 2 ^ (prefixWord ++ tailWord_1642538).sum := by decide
  have hdescent : baseEnd_1642538 < baseStart_1642538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642542 : List Nat := [4, 1, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_1642542 : Nat := 118140960795 + 1642542 * 2 ^ 59
def prefixEnd_1642542 : Nat := 4983230072969 + 3 ^ 40 * 1642542 * 2
def baseEnd_1642542 : Nat := 281137847065805926857031

theorem tailTrace_1642542 : CollatzResearch.WordTrace tailWord_1642542 prefixEnd_1642542 281137847065805926857031 := by
  unfold tailWord_1642542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7488553551919791585633235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39938952276905555123377253 7488553551919791585633235)
  ·
    refine ⟨11232830327879687378449853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7488553551919791585633235 11232830327879687378449853)
    ·
      refine ⟨4212311372954882766918695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11232830327879687378449853 4212311372954882766918695)
      ·
        refine ⟨6318467059432324150378043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4212311372954882766918695 6318467059432324150378043)
        ·
          refine ⟨9477700589148486225567065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6318467059432324150378043 9477700589148486225567065)
          ·
            refine ⟨7108275441861364669175299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9477700589148486225567065 7108275441861364669175299)
            ·
              refine ⟨10662413162792047003762949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7108275441861364669175299 10662413162792047003762949)
              ·
                refine ⟨1999202468023508813205553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10662413162792047003762949 1999202468023508813205553)
                ·
                  refine ⟨1499401851017631609904165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1999202468023508813205553 1499401851017631609904165)
                  ·
                    refine ⟨281137847065805926857031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1499401851017631609904165 281137847065805926857031)
                    ·
                      rfl

theorem cell23_1642542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_1642542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642542 prefixEnd_1642542 := by exact prefixLift 1642542
  have htrace : WordTrace (prefixWord ++ tailWord_1642542) baseStart_1642542 baseEnd_1642542 := by
    simpa [prefixWord, tailWord_1642542, baseEnd_1642542] using wordTrace_append hprefix tailTrace_1642542
  have hstable : (prefixWord ++ tailWord_1642542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642542).length < 2 ^ (prefixWord ++ tailWord_1642542).sum := by decide
  have hdescent : baseEnd_1642542 < baseStart_1642542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642565 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 6, 1, 3]
def baseStart_1642565 : Nat := 118140960795 + 1642565 * 2 ^ 59
def prefixEnd_1642565 : Nat := 4983230072969 + 3 ^ 40 * 1642565 * 2
def baseEnd_1642565 : Nat := 843425351252471190583487

theorem tailTrace_1642565 : CollatzResearch.WordTrace tailWord_1642565 prefixEnd_1642565 843425351252471190583487 := by
  unfold tailWord_1642565
  simp only [CollatzResearch.WordTrace]
  refine ⟨59909267294275007613153149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39939511529516671742102099 59909267294275007613153149)
  ·
    refine ⟨22465975235353127854932431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59909267294275007613153149 22465975235353127854932431)
    ·
      refine ⟨33698962853029691782398647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22465975235353127854932431 33698962853029691782398647)
      ·
        refine ⟨50548444279544537673597971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33698962853029691782398647 50548444279544537673597971)
        ·
          refine ⟨75822666419316806510396957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50548444279544537673597971 75822666419316806510396957)
          ·
            refine ⟨28433499907243802441398859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75822666419316806510396957 28433499907243802441398859)
            ·
              refine ⟨42650249860865703662098289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28433499907243802441398859 42650249860865703662098289)
              ·
                refine ⟨31987687395649277746573717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42650249860865703662098289 31987687395649277746573717)
                ·
                  refine ⟨1499422846671059894370643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31987687395649277746573717 1499422846671059894370643)
                  ·
                    refine ⟨2249134270006589841555965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1499422846671059894370643 2249134270006589841555965)
                    ·
                      refine ⟨843425351252471190583487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2249134270006589841555965 843425351252471190583487)
                      ·
                        rfl

theorem cell23_1642565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_1642565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642565 prefixEnd_1642565 := by exact prefixLift 1642565
  have htrace : WordTrace (prefixWord ++ tailWord_1642565) baseStart_1642565 baseEnd_1642565 := by
    simpa [prefixWord, tailWord_1642565, baseEnd_1642565] using wordTrace_append hprefix tailTrace_1642565
  have hstable : (prefixWord ++ tailWord_1642565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642565).length < 2 ^ (prefixWord ++ tailWord_1642565).sum := by decide
  have hdescent : baseEnd_1642565 < baseStart_1642565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642566 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_1642566 : Nat := 118140960795 + 1642566 * 2 ^ 59
def prefixEnd_1642566 : Nat := 4983230072969 + 3 ^ 40 * 1642566 * 2
def baseEnd_1642566 : Nat := 843425864733125686670983

theorem tailTrace_1642566 : CollatzResearch.WordTrace tailWord_1642566 prefixEnd_1642566 843425864733125686670983 := by
  unfold tailWord_1642566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1872165742727230774498111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39939535844847589855959701 1872165742727230774498111)
  ·
    refine ⟨2808248614090846161747167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1872165742727230774498111 2808248614090846161747167)
    ·
      refine ⟨4212372921136269242620751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2808248614090846161747167 4212372921136269242620751)
      ·
        refine ⟨6318559381704403863931127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4212372921136269242620751 6318559381704403863931127)
        ·
          refine ⟨9477839072556605795896691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6318559381704403863931127 9477839072556605795896691)
          ·
            refine ⟨14216758608834908693845037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9477839072556605795896691 14216758608834908693845037)
            ·
              refine ⟨5331284478313090760191889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14216758608834908693845037 5331284478313090760191889)
              ·
                refine ⟨3998463358734818070143917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5331284478313090760191889 3998463358734818070143917)
                ·
                  refine ⟨1499423759525556776303969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3998463358734818070143917 1499423759525556776303969)
                  ·
                    refine ⟨1124567819644167582227977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1499423759525556776303969 1124567819644167582227977)
                    ·
                      refine ⟨843425864733125686670983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1124567819644167582227977 843425864733125686670983)
                      ·
                        rfl

theorem cell23_1642566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_1642566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642566 prefixEnd_1642566 := by exact prefixLift 1642566
  have htrace : WordTrace (prefixWord ++ tailWord_1642566) baseStart_1642566 baseEnd_1642566 := by
    simpa [prefixWord, tailWord_1642566, baseEnd_1642566] using wordTrace_append hprefix tailTrace_1642566
  have hstable : (prefixWord ++ tailWord_1642566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642566).length < 2 ^ (prefixWord ++ tailWord_1642566).sum := by decide
  have hdescent : baseEnd_1642566 < baseStart_1642566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642692 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1642692 : Nat := 118140960795 + 1642692 * 2 ^ 59
def prefixEnd_1642692 : Nat := 4983230072969 + 3 ^ 40 * 1642692 * 2
def baseEnd_1642692 : Nat := 281163521098530731231801

theorem tailTrace_1642692 : CollatzResearch.WordTrace tailWord_1642692 prefixEnd_1642692 281163521098530731231801 := by
  unfold tailWord_1642692
  simp only [CollatzResearch.WordTrace]
  refine ⟨29956949682407454151513165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39942599576543272202017553 29956949682407454151513165)
  ·
    refine ⟨11233856130902795306817437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29956949682407454151513165 11233856130902795306817437)
    ·
      refine ⟨4212696049088548240056539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11233856130902795306817437 4212696049088548240056539)
      ·
        refine ⟨6319044073632822360084809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4212696049088548240056539 6319044073632822360084809)
        ·
          refine ⟨4739283055224616770063607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6319044073632822360084809 4739283055224616770063607)
          ·
            refine ⟨7108924582836925155095411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4739283055224616770063607 7108924582836925155095411)
            ·
              refine ⟨10663386874255387732643117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7108924582836925155095411 10663386874255387732643117)
              ·
                refine ⟨3998770077845770399741169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10663386874255387732643117 3998770077845770399741169)
                ·
                  refine ⟨2999077558384327799805877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3998770077845770399741169 2999077558384327799805877)
                  ·
                    refine ⟨281163521098530731231801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2999077558384327799805877 281163521098530731231801)
                    ·
                      rfl

theorem cell23_1642692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1642692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642692 prefixEnd_1642692 := by exact prefixLift 1642692
  have htrace : WordTrace (prefixWord ++ tailWord_1642692) baseStart_1642692 baseEnd_1642692 := by
    simpa [prefixWord, tailWord_1642692, baseEnd_1642692] using wordTrace_append hprefix tailTrace_1642692
  have hstable : (prefixWord ++ tailWord_1642692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642692).length < 2 ^ (prefixWord ++ tailWord_1642692).sum := by decide
  have hdescent : baseEnd_1642692 < baseStart_1642692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642712 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 2, 1, 4]
def baseStart_1642712 : Nat := 118140960795 + 1642712 * 2 ^ 59
def prefixEnd_1642712 : Nat := 4983230072969 + 3 ^ 40 * 1642712 * 2
def baseEnd_1642712 : Nat := 843500832908682115445311

theorem tailTrace_1642712 : CollatzResearch.WordTrace tailWord_1642712 prefixEnd_1642712 843500832908682115445311 := by
  unfold tailWord_1642712
  simp only [CollatzResearch.WordTrace]
  refine ⟨29957314412371225859377195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39943085883161634479169593 29957314412371225859377195)
  ·
    refine ⟨44935971618556838789065793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29957314412371225859377195 44935971618556838789065793)
    ·
      refine ⟨33701978713917629091799345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44935971618556838789065793 33701978713917629091799345)
      ·
        refine ⟨25276484035438221818849509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33701978713917629091799345 25276484035438221818849509)
        ·
          refine ⟨4739340756644666591034283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25276484035438221818849509 4739340756644666591034283)
          ·
            refine ⟨7109011134966999886551425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4739340756644666591034283 7109011134966999886551425)
            ·
              refine ⟨5331758351225249914913569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7109011134966999886551425 5331758351225249914913569)
              ·
                refine ⟨3998818763418937436185177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5331758351225249914913569 3998818763418937436185177)
                ·
                  refine ⟨2999114072564203077138883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3998818763418937436185177 2999114072564203077138883)
                  ·
                    refine ⟨4498671108846304615708325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2999114072564203077138883 4498671108846304615708325)
                    ·
                      refine ⟨843500832908682115445311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4498671108846304615708325 843500832908682115445311)
                      ·
                        rfl

theorem cell23_1642712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_1642712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642712 prefixEnd_1642712 := by exact prefixLift 1642712
  have htrace : WordTrace (prefixWord ++ tailWord_1642712) baseStart_1642712 baseEnd_1642712 := by
    simpa [prefixWord, tailWord_1642712, baseEnd_1642712] using wordTrace_append hprefix tailTrace_1642712
  have hstable : (prefixWord ++ tailWord_1642712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642712).length < 2 ^ (prefixWord ++ tailWord_1642712).sum := by decide
  have hdescent : baseEnd_1642712 < baseStart_1642712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642745 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 1, 7, 3]
def baseStart_1642745 : Nat := 118140960795 + 1642745 * 2 ^ 59
def prefixEnd_1642745 : Nat := 4983230072969 + 3 ^ 40 * 1642745 * 2
def baseEnd_1642745 : Nat := 843517777770280486332659

theorem tailTrace_1642745 : CollatzResearch.WordTrace tailWord_1642745 prefixEnd_1642745 843517777770280486332659 := by
  unfold tailWord_1642745
  simp only [CollatzResearch.WordTrace]
  refine ⟨59915832433622898354705689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39943888289081932236470459 59915832433622898354705689)
  ·
    refine ⟨44936874325217173766029267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59915832433622898354705689 44936874325217173766029267)
    ·
      refine ⟨67405311487825760649043901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44936874325217173766029267 67405311487825760649043901)
      ·
        refine ⟨25276991807934660243391463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67405311487825760649043901 25276991807934660243391463)
        ·
          refine ⟨37915487711901990365087195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25276991807934660243391463 37915487711901990365087195)
          ·
            refine ⟨56873231567852985547630793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37915487711901990365087195 56873231567852985547630793)
            ·
              refine ⟨42654923675889739160723095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56873231567852985547630793 42654923675889739160723095)
              ·
                refine ⟨63982385513834608741084643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42654923675889739160723095 63982385513834608741084643)
                ·
                  refine ⟨95973578270751913111626965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63982385513834608741084643 95973578270751913111626965)
                  ·
                    refine ⟨2249380740720747963553757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 95973578270751913111626965 2249380740720747963553757)
                    ·
                      refine ⟨843517777770280486332659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2249380740720747963553757 843517777770280486332659)
                      ·
                        rfl

theorem cell23_1642745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_1642745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642745 prefixEnd_1642745 := by exact prefixLift 1642745
  have htrace : WordTrace (prefixWord ++ tailWord_1642745) baseStart_1642745 baseEnd_1642745 := by
    simpa [prefixWord, tailWord_1642745, baseEnd_1642745] using wordTrace_append hprefix tailTrace_1642745
  have hstable : (prefixWord ++ tailWord_1642745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642745).length < 2 ^ (prefixWord ++ tailWord_1642745).sum := by decide
  have hdescent : baseEnd_1642745 < baseStart_1642745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642812 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 6, 4]
def baseStart_1642812 : Nat := 118140960795 + 1642812 * 2 ^ 59
def prefixEnd_1642812 : Nat := 4983230072969 + 3 ^ 40 * 1642812 * 2
def baseEnd_1642812 : Nat := 281184060324710574731617

theorem tailTrace_1642812 : CollatzResearch.WordTrace tailWord_1642812 prefixEnd_1642812 281184060324710574731617 := by
  unfold tailWord_1642812
  simp only [CollatzResearch.WordTrace]
  refine ⟨29959138062190084398697345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39945517416253445864929793 29959138062190084398697345)
  ·
    refine ⟨22469353546642563299023009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29959138062190084398697345 22469353546642563299023009)
    ·
      refine ⟨16852015159981922474267257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22469353546642563299023009 16852015159981922474267257)
      ·
        refine ⟨12639011369986441855700443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16852015159981922474267257 12639011369986441855700443)
        ·
          refine ⟨18958517054979662783550665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12639011369986441855700443 18958517054979662783550665)
          ·
            refine ⟨14218887791234747087662999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18958517054979662783550665 14218887791234747087662999)
            ·
              refine ⟨21328331686852120631494499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14218887791234747087662999 21328331686852120631494499)
              ·
                refine ⟨31992497530278180947241749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21328331686852120631494499 31992497530278180947241749)
                ·
                  refine ⟨1499648321731789731901957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31992497530278180947241749 1499648321731789731901957)
                  ·
                    refine ⟨281184060324710574731617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1499648321731789731901957 281184060324710574731617)
                    ·
                      rfl

theorem cell23_1642812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_1642812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642812 prefixEnd_1642812 := by exact prefixLift 1642812
  have htrace : WordTrace (prefixWord ++ tailWord_1642812) baseStart_1642812 baseEnd_1642812 := by
    simpa [prefixWord, tailWord_1642812, baseEnd_1642812] using wordTrace_append hprefix tailTrace_1642812
  have hstable : (prefixWord ++ tailWord_1642812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642812).length < 2 ^ (prefixWord ++ tailWord_1642812).sum := by decide
  have hdescent : baseEnd_1642812 < baseStart_1642812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642819 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 5, 2, 2]
def baseStart_1642819 : Nat := 118140960795 + 1642819 * 2 ^ 59
def prefixEnd_1642819 : Nat := 4983230072969 + 3 ^ 40 * 1642819 * 2
def baseEnd_1642819 : Nat := 843555775338713196807319

theorem tailTrace_1642819 : CollatzResearch.WordTrace tailWord_1642819 prefixEnd_1642819 843555775338713196807319 := by
  unfold tailWord_1642819
  simp only [CollatzResearch.WordTrace]
  refine ⟨59918531435354808992899511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39945687623569872661933007 59918531435354808992899511)
  ·
    refine ⟨89877797153032213489349267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59918531435354808992899511 89877797153032213489349267)
    ·
      refine ⟨134816695729548320234023901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89877797153032213489349267 134816695729548320234023901)
      ·
        refine ⟨50556260898580620087758963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134816695729548320234023901 50556260898580620087758963)
        ·
          refine ⟨75834391347870930131638445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50556260898580620087758963 75834391347870930131638445)
          ·
            refine ⟨28437896755451598799364417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75834391347870930131638445 28437896755451598799364417)
            ·
              refine ⟨21328422566588699099523313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28437896755451598799364417 21328422566588699099523313)
              ·
                refine ⟨15996316924941524324642485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21328422566588699099523313 15996316924941524324642485)
                ·
                  refine ⟨1499654711713267905435233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15996316924941524324642485 1499654711713267905435233)
                  ·
                    refine ⟨1124741033784950929076425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1499654711713267905435233 1124741033784950929076425)
                    ·
                      refine ⟨843555775338713196807319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1124741033784950929076425 843555775338713196807319)
                      ·
                        rfl

theorem cell23_1642819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5, 2, 2].length) (baseStart_1642819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642819 prefixEnd_1642819 := by exact prefixLift 1642819
  have htrace : WordTrace (prefixWord ++ tailWord_1642819) baseStart_1642819 baseEnd_1642819 := by
    simpa [prefixWord, tailWord_1642819, baseEnd_1642819] using wordTrace_append hprefix tailTrace_1642819
  have hstable : (prefixWord ++ tailWord_1642819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642819).length < 2 ^ (prefixWord ++ tailWord_1642819).sum := by decide
  have hdescent : baseEnd_1642819 < baseStart_1642819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642856 : List Nat := [2, 1, 4, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_1642856 : Nat := 118140960795 + 1642856 * 2 ^ 59
def prefixEnd_1642856 : Nat := 4983230072969 + 3 ^ 40 * 1642856 * 2
def baseEnd_1642856 : Nat := 843574774122929552044649

theorem tailTrace_1642856 : CollatzResearch.WordTrace tailWord_1642856 prefixEnd_1642856 843574774122929552044649 := by
  unfold tailWord_1642856
  simp only [CollatzResearch.WordTrace]
  refine ⟨29959940468110382155998211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39946587290813842874664281 29959940468110382155998211)
  ·
    refine ⟨44939910702165573233997317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29959940468110382155998211 44939910702165573233997317)
    ·
      refine ⟨8426233256656044981374497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44939910702165573233997317 8426233256656044981374497)
      ·
        refine ⟨6319674942492033736030873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8426233256656044981374497 6319674942492033736030873)
        ·
          refine ⟨4739756206869025302023155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6319674942492033736030873 4739756206869025302023155)
          ·
            refine ⟨7109634310303537953034733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4739756206869025302023155 7109634310303537953034733)
            ·
              refine ⟨2666112866363826732388025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7109634310303537953034733 2666112866363826732388025)
              ·
                refine ⟨1999584649772870049291019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666112866363826732388025 1999584649772870049291019)
                ·
                  refine ⟨2999376974659305073936529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1999584649772870049291019 2999376974659305073936529)
                  ·
                    refine ⟨2249532730994478805452397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2999376974659305073936529 2249532730994478805452397)
                    ·
                      refine ⟨843574774122929552044649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2249532730994478805452397 843574774122929552044649)
                      ·
                        rfl

theorem cell23_1642856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_1642856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642856 prefixEnd_1642856 := by exact prefixLift 1642856
  have htrace : WordTrace (prefixWord ++ tailWord_1642856) baseStart_1642856 baseEnd_1642856 := by
    simpa [prefixWord, tailWord_1642856, baseEnd_1642856] using wordTrace_append hprefix tailTrace_1642856
  have hstable : (prefixWord ++ tailWord_1642856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642856).length < 2 ^ (prefixWord ++ tailWord_1642856).sum := by decide
  have hdescent : baseEnd_1642856 < baseStart_1642856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642869 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1642869 : Nat := 118140960795 + 1642869 * 2 ^ 59
def prefixEnd_1642869 : Nat := 4983230072969 + 3 ^ 40 * 1642869 * 2
def baseEnd_1642869 : Nat := 843581449371438001182089

theorem tailTrace_1642869 : CollatzResearch.WordTrace tailWord_1642869 prefixEnd_1642869 843581449371438001182089 := by
  unfold tailWord_1642869
  simp only [CollatzResearch.WordTrace]
  refine ⟨59920355085173667532219661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39946903390115778354813107 59920355085173667532219661)
  ·
    refine ⟨22470133156940125324582373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59920355085173667532219661 22470133156940125324582373)
    ·
      refine ⟨4213149966926273498359195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22470133156940125324582373 4213149966926273498359195)
      ·
        refine ⟨6319724950389410247538793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4213149966926273498359195 6319724950389410247538793)
        ·
          refine ⟨4739793712792057685654095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6319724950389410247538793 4739793712792057685654095)
          ·
            refine ⟨7109690569188086528481143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4739793712792057685654095 7109690569188086528481143)
            ·
              refine ⟨10664535853782129792721715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7109690569188086528481143 10664535853782129792721715)
              ·
                refine ⟨15996803780673194689082573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10664535853782129792721715 15996803780673194689082573)
                ·
                  refine ⟨5998801417752448008405965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15996803780673194689082573 5998801417752448008405965)
                  ·
                    refine ⟨2249550531657168003152237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5998801417752448008405965 2249550531657168003152237)
                    ·
                      refine ⟨843581449371438001182089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2249550531657168003152237 843581449371438001182089)
                      ·
                        rfl

theorem cell23_1642869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1642869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642869 prefixEnd_1642869 := by exact prefixLift 1642869
  have htrace : WordTrace (prefixWord ++ tailWord_1642869) baseStart_1642869 baseEnd_1642869 := by
    simpa [prefixWord, tailWord_1642869, baseEnd_1642869] using wordTrace_append hprefix tailTrace_1642869
  have hstable : (prefixWord ++ tailWord_1642869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642869).length < 2 ^ (prefixWord ++ tailWord_1642869).sum := by decide
  have hdescent : baseEnd_1642869 < baseStart_1642869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642870 : List Nat := [5, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1642870 : Nat := 118140960795 + 1642870 * 2 ^ 59
def prefixEnd_1642870 : Nat := 4983230072969 + 3 ^ 40 * 1642870 * 2
def baseEnd_1642870 : Nat := 843581962852092497269585

theorem tailTrace_1642870 : CollatzResearch.WordTrace tailWord_1642870 prefixEnd_1642870 843581962852092497269585 := by
  unfold tailWord_1642870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745024472385627793937879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39946927705446696468670709 3745024472385627793937879)
  ·
    refine ⟨5617536708578441690906819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3745024472385627793937879 5617536708578441690906819)
    ·
      refine ⟨8426305062867662536360229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5617536708578441690906819 8426305062867662536360229)
      ·
        refine ⟨1579932199287686725567543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8426305062867662536360229 1579932199287686725567543)
        ·
          refine ⟨2369898298931530088351315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1579932199287686725567543 2369898298931530088351315)
          ·
            refine ⟨3554847448397295132526973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369898298931530088351315 3554847448397295132526973)
            ·
              refine ⟨1333067793148985674697615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3554847448397295132526973 1333067793148985674697615)
              ·
                refine ⟨1999601689723478512046423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1333067793148985674697615 1999601689723478512046423)
                ·
                  refine ⟨2999402534585217768069635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1999601689723478512046423 2999402534585217768069635)
                  ·
                    refine ⟨4499103801877826652104453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2999402534585217768069635 4499103801877826652104453)
                    ·
                      refine ⟨843581962852092497269585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4499103801877826652104453 843581962852092497269585)
                      ·
                        rfl

theorem cell23_1642870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1642870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642870 prefixEnd_1642870 := by exact prefixLift 1642870
  have htrace : WordTrace (prefixWord ++ tailWord_1642870) baseStart_1642870 baseEnd_1642870 := by
    simpa [prefixWord, tailWord_1642870, baseEnd_1642870] using wordTrace_append hprefix tailTrace_1642870
  have hstable : (prefixWord ++ tailWord_1642870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642870).length < 2 ^ (prefixWord ++ tailWord_1642870).sum := by decide
  have hdescent : baseEnd_1642870 < baseStart_1642870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1642892 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_1642892 : Nat := 118140960795 + 1642892 * 2 ^ 59
def prefixEnd_1642892 : Nat := 4983230072969 + 3 ^ 40 * 1642892 * 2
def baseEnd_1642892 : Nat := 843593259426491411194483

theorem tailTrace_1642892 : CollatzResearch.WordTrace tailWord_1642892 prefixEnd_1642892 843593259426491411194483 := by
  unfold tailWord_1642892
  simp only [CollatzResearch.WordTrace]
  refine ⟨29960596982045171230153465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39947462642726894973537953 29960596982045171230153465)
  ·
    refine ⟨22470447736533878422615099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29960596982045171230153465 22470447736533878422615099)
    ·
      refine ⟨33705671604800817633922649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22470447736533878422615099 33705671604800817633922649)
      ·
        refine ⟨25279253703600613225441987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33705671604800817633922649 25279253703600613225441987)
        ·
          refine ⟨37918880555400919838162981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25279253703600613225441987 37918880555400919838162981)
          ·
            refine ⟨7109790104137672469655559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37918880555400919838162981 7109790104137672469655559)
            ·
              refine ⟨10664685156206508704483339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7109790104137672469655559 10664685156206508704483339)
              ·
                refine ⟨15997027734309763056725009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10664685156206508704483339 15997027734309763056725009)
                ·
                  refine ⟨11997770800732322292543757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15997027734309763056725009 11997770800732322292543757)
                  ·
                    refine ⟨4499164050274620859703909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11997770800732322292543757 4499164050274620859703909)
                    ·
                      refine ⟨843593259426491411194483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4499164050274620859703909 843593259426491411194483)
                      ·
                        rfl

theorem cell23_1642892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_1642892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1642892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1642892 prefixEnd_1642892 := by exact prefixLift 1642892
  have htrace : WordTrace (prefixWord ++ tailWord_1642892) baseStart_1642892 baseEnd_1642892 := by
    simpa [prefixWord, tailWord_1642892, baseEnd_1642892] using wordTrace_append hprefix tailTrace_1642892
  have hstable : (prefixWord ++ tailWord_1642892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1642892).length < 2 ^ (prefixWord ++ tailWord_1642892).sum := by decide
  have hdescent : baseEnd_1642892 < baseStart_1642892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1642892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643002 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_1643002 : Nat := 118140960795 + 1643002 * 2 ^ 59
def prefixEnd_1643002 : Nat := 4983230072969 + 3 ^ 40 * 1643002 * 2
def baseEnd_1643002 : Nat := 843649742298485980818977

theorem tailTrace_1643002 : CollatzResearch.WordTrace tailWord_1643002 prefixEnd_1643002 843649742298485980818977 := by
  unfold tailWord_1643002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14981301498422957811702815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39950137329127887497874173 14981301498422957811702815)
  ·
    refine ⟨22471952247634436717554223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14981301498422957811702815 22471952247634436717554223)
    ·
      refine ⟨33707928371451655076331335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22471952247634436717554223 33707928371451655076331335)
      ·
        refine ⟨50561892557177482614497003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33707928371451655076331335 50561892557177482614497003)
        ·
          refine ⟨75842838835766223921745505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50561892557177482614497003 75842838835766223921745505)
          ·
            refine ⟨56882129126824667941309129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75842838835766223921745505 56882129126824667941309129)
            ·
              refine ⟨42661596845118500955981847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56882129126824667941309129 42661596845118500955981847)
              ·
                refine ⟨63992395267677751433972771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42661596845118500955981847 63992395267677751433972771)
                ·
                  refine ⟨95988592901516627150959157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63992395267677751433972771 95988592901516627150959157)
                  ·
                    refine ⟨8998930584517183795402421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95988592901516627150959157 8998930584517183795402421)
                    ·
                      refine ⟨843649742298485980818977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8998930584517183795402421 843649742298485980818977)
                      ·
                        rfl

theorem cell23_1643002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_1643002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643002 prefixEnd_1643002 := by exact prefixLift 1643002
  have htrace : WordTrace (prefixWord ++ tailWord_1643002) baseStart_1643002 baseEnd_1643002 := by
    simpa [prefixWord, tailWord_1643002, baseEnd_1643002] using wordTrace_append hprefix tailTrace_1643002
  have hstable : (prefixWord ++ tailWord_1643002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643002).length < 2 ^ (prefixWord ++ tailWord_1643002).sum := by decide
  have hdescent : baseEnd_1643002 < baseStart_1643002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643036 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_1643036 : Nat := 118140960795 + 1643036 * 2 ^ 59
def prefixEnd_1643036 : Nat := 4983230072969 + 3 ^ 40 * 1643036 * 2
def baseEnd_1643036 : Nat := 843667200640738847793821

theorem tailTrace_1643036 : CollatzResearch.WordTrace tailWord_1643036 prefixEnd_1643036 843667200640738847793821 := by
  unfold tailWord_1643036
  simp only [CollatzResearch.WordTrace]
  refine ⟨29963223037784327526774481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39950964050379103369032641 29963223037784327526774481)
  ·
    refine ⟨22472417278338245645080861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29963223037784327526774481 22472417278338245645080861)
    ·
      refine ⟨8427156479376842116905323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22472417278338245645080861 8427156479376842116905323)
      ·
        refine ⟨12640734719065263175357985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8427156479376842116905323 12640734719065263175357985)
        ·
          refine ⟨9480551039298947381518489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12640734719065263175357985 9480551039298947381518489)
          ·
            refine ⟨7110413279474210536138867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9480551039298947381518489 7110413279474210536138867)
            ·
              refine ⟨10665619919211315804208301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7110413279474210536138867 10665619919211315804208301)
              ·
                refine ⟨3999607469704243426578113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10665619919211315804208301 3999607469704243426578113)
                ·
                  refine ⟨2999705602278182569933585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3999607469704243426578113 2999705602278182569933585)
                  ·
                    refine ⟨2249779201708636927450189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2999705602278182569933585 2249779201708636927450189)
                    ·
                      refine ⟨843667200640738847793821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2249779201708636927450189 843667200640738847793821)
                      ·
                        rfl

theorem cell23_1643036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_1643036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643036 prefixEnd_1643036 := by exact prefixLift 1643036
  have htrace : WordTrace (prefixWord ++ tailWord_1643036) baseStart_1643036 baseEnd_1643036 := by
    simpa [prefixWord, tailWord_1643036, baseEnd_1643036] using wordTrace_append hprefix tailTrace_1643036
  have hstable : (prefixWord ++ tailWord_1643036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643036).length < 2 ^ (prefixWord ++ tailWord_1643036).sum := by decide
  have hdescent : baseEnd_1643036 < baseStart_1643036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643093 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 2, 3, 2]
def baseStart_1643093 : Nat := 118140960795 + 1643093 * 2 ^ 59
def prefixEnd_1643093 : Nat := 4983230072969 + 3 ^ 40 * 1643093 * 2
def baseEnd_1643093 : Nat := 843696469038045124781059

theorem tailTrace_1643093 : CollatzResearch.WordTrace tailWord_1643093 prefixEnd_1643093 843696469038045124781059 := by
  unfold tailWord_1643093
  simp only [CollatzResearch.WordTrace]
  refine ⟨59928525036362153788373933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39952350024241435858915955 59928525036362153788373933)
  ·
    refine ⟨22473196888635807670640225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59928525036362153788373933 22473196888635807670640225)
    ·
      refine ⟨16854897666476855752980169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22473196888635807670640225 16854897666476855752980169)
      ·
        refine ⟨12641173249857641814735127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16854897666476855752980169 12641173249857641814735127)
        ·
          refine ⟨18961759874786462722102691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12641173249857641814735127 18961759874786462722102691)
          ·
            refine ⟨28442639812179694083154037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18961759874786462722102691 28442639812179694083154037)
            ·
              refine ⟨2666497482391846320295691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28442639812179694083154037 2666497482391846320295691)
              ·
                refine ⟨3999746223587769480443537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2666497482391846320295691 3999746223587769480443537)
                ·
                  refine ⟨2999809667690827110332653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3999746223587769480443537 2999809667690827110332653)
                  ·
                    refine ⟨1124928625384060166374745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2999809667690827110332653 1124928625384060166374745)
                    ·
                      refine ⟨843696469038045124781059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1124928625384060166374745 843696469038045124781059)
                      ·
                        rfl

theorem cell23_1643093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_1643093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643093 prefixEnd_1643093 := by exact prefixLift 1643093
  have htrace : WordTrace (prefixWord ++ tailWord_1643093) baseStart_1643093 baseEnd_1643093 := by
    simpa [prefixWord, tailWord_1643093, baseEnd_1643093] using wordTrace_append hprefix tailTrace_1643093
  have hstable : (prefixWord ++ tailWord_1643093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643093).length < 2 ^ (prefixWord ++ tailWord_1643093).sum := by decide
  have hdescent : baseEnd_1643093 < baseStart_1643093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643119 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 4]
def baseStart_1643119 : Nat := 118140960795 + 1643119 * 2 ^ 59
def prefixEnd_1643119 : Nat := 4983230072969 + 3 ^ 40 * 1643119 * 2
def baseEnd_1643119 : Nat := 843709819535062023055939

theorem tailTrace_1643119 : CollatzResearch.WordTrace tailWord_1643119 prefixEnd_1643119 843709819535062023055939 := by
  unfold tailWord_1643119
  simp only [CollatzResearch.WordTrace]
  refine ⟨59929473334267960228820411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39952982222845306819213607 59929473334267960228820411)
  ·
    refine ⟨89894210001401940343230617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59929473334267960228820411 89894210001401940343230617)
    ·
      refine ⟨67420657501051455257422963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89894210001401940343230617 67420657501051455257422963)
      ·
        refine ⟨101130986251577182886134445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67420657501051455257422963 101130986251577182886134445)
        ·
          refine ⟨37924119844341443582300417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101130986251577182886134445 37924119844341443582300417)
          ·
            refine ⟨28443089883256082686725313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37924119844341443582300417 28443089883256082686725313)
            ·
              refine ⟨21332317412442062015043985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28443089883256082686725313 21332317412442062015043985)
              ·
                refine ⟨15999238059331546511282989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21332317412442062015043985 15999238059331546511282989)
                ·
                  refine ⟨5999714272249329941731121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15999238059331546511282989 5999714272249329941731121)
                  ·
                    refine ⟨4499785704186997456298341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5999714272249329941731121 4499785704186997456298341)
                    ·
                      refine ⟨843709819535062023055939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4499785704186997456298341 843709819535062023055939)
                      ·
                        rfl

theorem cell23_1643119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_1643119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643119 prefixEnd_1643119 := by exact prefixLift 1643119
  have htrace : WordTrace (prefixWord ++ tailWord_1643119) baseStart_1643119 baseEnd_1643119 := by
    simpa [prefixWord, tailWord_1643119, baseEnd_1643119] using wordTrace_append hprefix tailTrace_1643119
  have hstable : (prefixWord ++ tailWord_1643119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643119).length < 2 ^ (prefixWord ++ tailWord_1643119).sum := by decide
  have hdescent : baseEnd_1643119 < baseStart_1643119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643133 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_1643133 : Nat := 118140960795 + 1643133 * 2 ^ 59
def prefixEnd_1643133 : Nat := 4983230072969 + 3 ^ 40 * 1643133 * 2
def baseEnd_1643133 : Nat := 281239002754741656093625

theorem tailTrace_1643133 : CollatzResearch.WordTrace tailWord_1643133 prefixEnd_1643133 281239002754741656093625 := by
  unfold tailWord_1643133
  simp only [CollatzResearch.WordTrace]
  refine ⟨59929983956217240619830053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39953322637478160413220035 59929983956217240619830053)
  ·
    refine ⟨11236871991790732616218135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59929983956217240619830053 11236871991790732616218135)
    ·
      refine ⟨16855307987686098924327203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11236871991790732616218135 16855307987686098924327203)
      ·
        refine ⟨25282961981529148386490805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16855307987686098924327203 25282961981529148386490805)
        ·
          refine ⟨2370277685768357661233513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25282961981529148386490805 2370277685768357661233513)
          ·
            refine ⟨1777708264326268245925135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2370277685768357661233513 1777708264326268245925135)
            ·
              refine ⟨2666562396489402368887703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1777708264326268245925135 2666562396489402368887703)
              ·
                refine ⟨3999843594734103553331555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2666562396489402368887703 3999843594734103553331555)
                ·
                  refine ⟨5999765392101155329997333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3999843594734103553331555 5999765392101155329997333)
                  ·
                    refine ⟨281239002754741656093625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5999765392101155329997333 281239002754741656093625)
                    ·
                      rfl

theorem cell23_1643133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_1643133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643133 prefixEnd_1643133 := by exact prefixLift 1643133
  have htrace : WordTrace (prefixWord ++ tailWord_1643133) baseStart_1643133 baseEnd_1643133 := by
    simpa [prefixWord, tailWord_1643133, baseEnd_1643133] using wordTrace_append hprefix tailTrace_1643133
  have hstable : (prefixWord ++ tailWord_1643133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643133).length < 2 ^ (prefixWord ++ tailWord_1643133).sum := by decide
  have hdescent : baseEnd_1643133 < baseStart_1643133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643136 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 4]
def baseStart_1643136 : Nat := 118140960795 + 1643136 * 2 ^ 59
def prefixEnd_1643136 : Nat := 4983230072969 + 3 ^ 40 * 1643136 * 2
def baseEnd_1643136 : Nat := 843718548706188456543361

theorem tailTrace_1643136 : CollatzResearch.WordTrace tailWord_1643136 prefixEnd_1643136 843718548706188456543361 := by
  unfold tailWord_1643136
  simp only [CollatzResearch.WordTrace]
  refine ⟨29965046687603186066094631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39953395583470914754792841 29965046687603186066094631)
  ·
    refine ⟨44947570031404779099141947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29965046687603186066094631 44947570031404779099141947)
    ·
      refine ⟨67421355047107168648712921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44947570031404779099141947 67421355047107168648712921)
      ·
        refine ⟨50566016285330376486534691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67421355047107168648712921 50566016285330376486534691)
        ·
          refine ⟨75849024427995564729802037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50566016285330376486534691 75849024427995564729802037)
          ·
            refine ⟨7110846040124584193418941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75849024427995564729802037 7110846040124584193418941)
            ·
              refine ⟨2666567265046719072532103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7110846040124584193418941 2666567265046719072532103)
              ·
                refine ⟨3999850897570078608798155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2666567265046719072532103 3999850897570078608798155)
                ·
                  refine ⟨5999776346355117913197233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3999850897570078608798155 5999776346355117913197233)
                  ·
                    refine ⟨4499832259766338434897925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5999776346355117913197233 4499832259766338434897925)
                    ·
                      refine ⟨843718548706188456543361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4499832259766338434897925 843718548706188456543361)
                      ·
                        rfl

theorem cell23_1643136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_1643136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643136 prefixEnd_1643136 := by exact prefixLift 1643136
  have htrace : WordTrace (prefixWord ++ tailWord_1643136) baseStart_1643136 baseEnd_1643136 := by
    simpa [prefixWord, tailWord_1643136, baseEnd_1643136] using wordTrace_append hprefix tailTrace_1643136
  have hstable : (prefixWord ++ tailWord_1643136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643136).length < 2 ^ (prefixWord ++ tailWord_1643136).sum := by decide
  have hdescent : baseEnd_1643136 < baseStart_1643136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643140 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_1643140 : Nat := 118140960795 + 1643140 * 2 ^ 59
def prefixEnd_1643140 : Nat := 4983230072969 + 3 ^ 40 * 1643140 * 2
def baseEnd_1643140 : Nat := 843720602628806440893343

theorem tailTrace_1643140 : CollatzResearch.WordTrace tailWord_1643140 prefixEnd_1643140 843720602628806440893343 := by
  unfold tailWord_1643140
  simp only [CollatzResearch.WordTrace]
  refine ⟨29965119633595940407667437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39953492844794587210223249 29965119633595940407667437)
  ·
    refine ⟨11236919862598477652875289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29965119633595940407667437 11236919862598477652875289)
    ·
      refine ⟨8427689896948858239656467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11236919862598477652875289 8427689896948858239656467)
      ·
        refine ⟨12641534845423287359484701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8427689896948858239656467 12641534845423287359484701)
        ·
          refine ⟨4740575567033732759806763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12641534845423287359484701 4740575567033732759806763)
          ·
            refine ⟨7110863350550599139710145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4740575567033732759806763 7110863350550599139710145)
            ·
              refine ⟨5333147512912949354782609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7110863350550599139710145 5333147512912949354782609)
              ·
                refine ⟨3999860634684712016086957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5333147512912949354782609 3999860634684712016086957)
                ·
                  refine ⟨1499947738006767006032609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3999860634684712016086957 1499947738006767006032609)
                  ·
                    refine ⟨1124960803505075254524457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1499947738006767006032609 1124960803505075254524457)
                    ·
                      refine ⟨843720602628806440893343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1124960803505075254524457 843720602628806440893343)
                      ·
                        rfl

theorem cell23_1643140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_1643140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643140 prefixEnd_1643140 := by exact prefixLift 1643140
  have htrace : WordTrace (prefixWord ++ tailWord_1643140) baseStart_1643140 baseEnd_1643140 := by
    simpa [prefixWord, tailWord_1643140, baseEnd_1643140] using wordTrace_append hprefix tailTrace_1643140
  have hstable : (prefixWord ++ tailWord_1643140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643140).length < 2 ^ (prefixWord ++ tailWord_1643140).sum := by decide
  have hdescent : baseEnd_1643140 < baseStart_1643140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643143 : List Nat := [1, 1, 4, 2, 1, 2, 4, 2, 1, 2, 3]
def baseStart_1643143 : Nat := 118140960795 + 1643143 * 2 ^ 59
def prefixEnd_1643143 : Nat := 4983230072969 + 3 ^ 40 * 1643143 * 2
def baseEnd_1643143 : Nat := 843722143070769929155829

theorem tailTrace_1643143 : CollatzResearch.WordTrace tailWord_1643143 prefixEnd_1643143 843722143070769929155829 := by
  unfold tailWord_1643143
  simp only [CollatzResearch.WordTrace]
  refine ⟨59930348686181012327694083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39953565790787341551796055 59930348686181012327694083)
  ·
    refine ⟨89895523029271518491541125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59930348686181012327694083 89895523029271518491541125)
    ·
      refine ⟨16855410567988409717163961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89895523029271518491541125 16855410567988409717163961)
      ·
        refine ⟨12641557925991307287872971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16855410567988409717163961 12641557925991307287872971)
        ·
          refine ⟨18962336888986960931809457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12641557925991307287872971 18962336888986960931809457)
          ·
            refine ⟨14221752666740220698857093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18962336888986960931809457 14221752666740220698857093)
            ·
              refine ⟨2666578625013791381035705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14221752666740220698857093 2666578625013791381035705)
              ·
                refine ⟨1999933968760343535776779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666578625013791381035705 1999933968760343535776779)
                ·
                  refine ⟨2999900953140515303665169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1999933968760343535776779 2999900953140515303665169)
                  ·
                    refine ⟨2249925714855386477748877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2999900953140515303665169 2249925714855386477748877)
                    ·
                      refine ⟨843722143070769929155829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2249925714855386477748877 843722143070769929155829)
                      ·
                        rfl

theorem cell23_1643143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_1643143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643143 prefixEnd_1643143 := by exact prefixLift 1643143
  have htrace : WordTrace (prefixWord ++ tailWord_1643143) baseStart_1643143 baseEnd_1643143 := by
    simpa [prefixWord, tailWord_1643143, baseEnd_1643143] using wordTrace_append hprefix tailTrace_1643143
  have hstable : (prefixWord ++ tailWord_1643143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643143).length < 2 ^ (prefixWord ++ tailWord_1643143).sum := by decide
  have hdescent : baseEnd_1643143 < baseStart_1643143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643146 : List Nat := [3, 1, 2, 3, 3, 1, 1, 9]
def baseStart_1643146 : Nat := 118140960795 + 1643146 * 2 ^ 59
def prefixEnd_1643146 : Nat := 4983230072969 + 3 ^ 40 * 1643146 * 2
def baseEnd_1643146 : Nat := 31249025315286422867345

theorem tailTrace_1643146 : CollatzResearch.WordTrace tailWord_1643146 prefixEnd_1643146 31249025315286422867345 := by
  unfold tailWord_1643146
  simp only [CollatzResearch.WordTrace]
  refine ⟨14982614526292535960013323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39953638736780095893368861 14982614526292535960013323)
  ·
    refine ⟨22473921789438803940019985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14982614526292535960013323 22473921789438803940019985)
    ·
      refine ⟨16855441342079102955014989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22473921789438803940019985 16855441342079102955014989)
      ·
        refine ⟨6320790503279663608130621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16855441342079102955014989 6320790503279663608130621)
        ·
          refine ⟨2370296438729873853048983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6320790503279663608130621 2370296438729873853048983)
          ·
            refine ⟨3555444658094810779573475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370296438729873853048983 3555444658094810779573475)
            ·
              refine ⟨5333166987142216169360213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3555444658094810779573475 5333166987142216169360213)
              ·
                refine ⟨31249025315286422867345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5333166987142216169360213 31249025315286422867345)
                ·
                  rfl

theorem cell23_1643146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 9].length) (baseStart_1643146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643146 prefixEnd_1643146 := by exact prefixLift 1643146
  have htrace : WordTrace (prefixWord ++ tailWord_1643146) baseStart_1643146 baseEnd_1643146 := by
    simpa [prefixWord, tailWord_1643146, baseEnd_1643146] using wordTrace_append hprefix tailTrace_1643146
  have hstable : (prefixWord ++ tailWord_1643146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643146).length < 2 ^ (prefixWord ++ tailWord_1643146).sum := by decide
  have hdescent : baseEnd_1643146 < baseStart_1643146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643173 : List Nat := [1, 3, 1, 2, 1, 2, 1, 6, 2, 1, 3]
def baseStart_1643173 : Nat := 118140960795 + 1643173 * 2 ^ 59
def prefixEnd_1643173 : Nat := 4983230072969 + 3 ^ 40 * 1643173 * 2
def baseEnd_1643173 : Nat := 843737547490404811780691

theorem tailTrace_1643173 : CollatzResearch.WordTrace tailWord_1643173 prefixEnd_1643173 843737547490404811780691 := by
  unfold tailWord_1643173
  simp only [CollatzResearch.WordTrace]
  refine ⟨59931442876072327451286173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39954295250714884967524115 59931442876072327451286173)
  ·
    refine ⟨22474291078527122794232315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59931442876072327451286173 22474291078527122794232315)
    ·
      refine ⟨33711436617790684191348473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22474291078527122794232315 33711436617790684191348473)
      ·
        refine ⟨25283577463343013143511355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33711436617790684191348473 25283577463343013143511355)
        ·
          refine ⟨37925366195014519715267033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25283577463343013143511355 37925366195014519715267033)
          ·
            refine ⟨28444024646260889786450275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37925366195014519715267033 28444024646260889786450275)
            ·
              refine ⟨42666036969391334679675413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28444024646260889786450275 42666036969391334679675413)
              ·
                refine ⟨1999970482940218813109785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42666036969391334679675413 1999970482940218813109785)
                ·
                  refine ⟨1499977862205164109832339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1999970482940218813109785 1499977862205164109832339)
                  ·
                    refine ⟨2249966793307746164748509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1499977862205164109832339 2249966793307746164748509)
                    ·
                      refine ⟨843737547490404811780691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2249966793307746164748509 843737547490404811780691)
                      ·
                        rfl

theorem cell23_1643173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_1643173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643173 prefixEnd_1643173 := by exact prefixLift 1643173
  have htrace : WordTrace (prefixWord ++ tailWord_1643173) baseStart_1643173 baseEnd_1643173 := by
    simpa [prefixWord, tailWord_1643173, baseEnd_1643173] using wordTrace_append hprefix tailTrace_1643173
  have hstable : (prefixWord ++ tailWord_1643173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643173).length < 2 ^ (prefixWord ++ tailWord_1643173).sum := by decide
  have hdescent : baseEnd_1643173 < baseStart_1643173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643200 : List Nat := [2, 1, 1, 2, 4, 2, 3, 2, 1, 3, 2]
def baseStart_1643200 : Nat := 118140960795 + 1643200 * 2 ^ 59
def prefixEnd_1643200 : Nat := 4983230072969 + 3 ^ 40 * 1643200 * 2
def baseEnd_1643200 : Nat := 843751411468076206143067

theorem tailTrace_1643200 : CollatzResearch.WordTrace tailWord_1643200 prefixEnd_1643200 843751411468076206143067 := by
  unfold tailWord_1643200
  simp only [CollatzResearch.WordTrace]
  refine ⟨29966213823487255531259527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39954951764649674041679369 29966213823487255531259527)
  ·
    refine ⟨44949320735230883296889291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29966213823487255531259527 44949320735230883296889291)
    ·
      refine ⟨67423981102846324945333937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44949320735230883296889291 67423981102846324945333937)
      ·
        refine ⟨50567985827134743709000453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67423981102846324945333937 50567985827134743709000453)
        ·
          refine ⟨9481497342587764445437585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50567985827134743709000453 9481497342587764445437585)
          ·
            refine ⟨7111123006940823334078189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9481497342587764445437585 7111123006940823334078189)
            ·
              refine ⟨2666671127602808750279321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7111123006940823334078189 2666671127602808750279321)
              ·
                refine ⟨2000003345702106562709491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666671127602808750279321 2000003345702106562709491)
                ·
                  refine ⟨3000005018553159844064237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000003345702106562709491 3000005018553159844064237)
                  ·
                    refine ⟨1125001881957434941524089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3000005018553159844064237 1125001881957434941524089)
                    ·
                      refine ⟨843751411468076206143067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125001881957434941524089 843751411468076206143067)
                      ·
                        rfl

theorem cell23_1643200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 1, 3, 2].length) (baseStart_1643200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643200 prefixEnd_1643200 := by exact prefixLift 1643200
  have htrace : WordTrace (prefixWord ++ tailWord_1643200) baseStart_1643200 baseEnd_1643200 := by
    simpa [prefixWord, tailWord_1643200, baseEnd_1643200] using wordTrace_append hprefix tailTrace_1643200
  have hstable : (prefixWord ++ tailWord_1643200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643200).length < 2 ^ (prefixWord ++ tailWord_1643200).sum := by decide
  have hdescent : baseEnd_1643200 < baseStart_1643200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643226 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_1643226 : Nat := 118140960795 + 1643226 * 2 ^ 59
def prefixEnd_1643226 : Nat := 4983230072969 + 3 ^ 40 * 1643226 * 2
def baseEnd_1643226 : Nat := 843764761965093104417947

theorem tailTrace_1643226 : CollatzResearch.WordTrace tailWord_1643226 prefixEnd_1643226 843764761965093104417947 := by
  unfold tailWord_1643226
  simp only [CollatzResearch.WordTrace]
  refine ⟨14983343986220079375741383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39955583963253545001977021 14983343986220079375741383)
  ·
    refine ⟨22475015979330119063612075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14983343986220079375741383 22475015979330119063612075)
    ·
      refine ⟨33712523968995178595418113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22475015979330119063612075 33712523968995178595418113)
      ·
        refine ⟨25284392976746383946563585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33712523968995178595418113 25284392976746383946563585)
        ·
          refine ⟨18963294732559787959922689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25284392976746383946563585 18963294732559787959922689)
          ·
            refine ⟨14222471049419840969942017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18963294732559787959922689 14222471049419840969942017)
            ·
              refine ⟨10666853287064880727456513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14222471049419840969942017 10666853287064880727456513)
              ·
                refine ⟨8000139965298660545592385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10666853287064880727456513 8000139965298660545592385)
                ·
                  refine ⟨6000104973973995409194289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8000139965298660545592385 6000104973973995409194289)
                  ·
                    refine ⟨4500078730480496556895717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6000104973973995409194289 4500078730480496556895717)
                    ·
                      refine ⟨843764761965093104417947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4500078730480496556895717 843764761965093104417947)
                      ·
                        rfl

theorem cell23_1643226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_1643226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643226 prefixEnd_1643226 := by exact prefixLift 1643226
  have htrace : WordTrace (prefixWord ++ tailWord_1643226) baseStart_1643226 baseEnd_1643226 := by
    simpa [prefixWord, tailWord_1643226, baseEnd_1643226] using wordTrace_append hprefix tailTrace_1643226
  have hstable : (prefixWord ++ tailWord_1643226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643226).length < 2 ^ (prefixWord ++ tailWord_1643226).sum := by decide
  have hdescent : baseEnd_1643226 < baseStart_1643226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643313 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 3, 4]
def baseStart_1643313 : Nat := 118140960795 + 1643313 * 2 ^ 59
def prefixEnd_1643313 : Nat := 4983230072969 + 3 ^ 40 * 1643313 * 2
def baseEnd_1643313 : Nat := 281269811594011421343349

theorem tailTrace_1643313 : CollatzResearch.WordTrace tailWord_1643313 prefixEnd_1643313 281269811594011421343349 := by
  unfold tailWord_1643313
  simp only [CollatzResearch.WordTrace]
  refine ⟨59936549095565131361382593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39957699397043420907588395 59936549095565131361382593)
  ·
    refine ⟨44952411821673848521036945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59936549095565131361382593 44952411821673848521036945)
    ·
      refine ⟨33714308866255386390777709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44952411821673848521036945 33714308866255386390777709)
      ·
        refine ⟨12642865824845769896541641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33714308866255386390777709 12642865824845769896541641)
        ·
          refine ⟨9482149368634327422406231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12642865824845769896541641 9482149368634327422406231)
          ·
            refine ⟨14223224052951491133609347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9482149368634327422406231 14223224052951491133609347)
            ·
              refine ⟨21334836079427236700414021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14223224052951491133609347 21334836079427236700414021)
              ·
                refine ⟨4000281764892606881327629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21334836079427236700414021 4000281764892606881327629)
                ·
                  refine ⟨1500105661834727580497861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4000281764892606881327629 1500105661834727580497861)
                  ·
                    refine ⟨281269811594011421343349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1500105661834727580497861 281269811594011421343349)
                    ·
                      rfl

theorem cell23_1643313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_1643313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643313 prefixEnd_1643313 := by exact prefixLift 1643313
  have htrace : WordTrace (prefixWord ++ tailWord_1643313) baseStart_1643313 baseEnd_1643313 := by
    simpa [prefixWord, tailWord_1643313, baseEnd_1643313] using wordTrace_append hprefix tailTrace_1643313
  have hstable : (prefixWord ++ tailWord_1643313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643313).length < 2 ^ (prefixWord ++ tailWord_1643313).sum := by decide
  have hdescent : baseEnd_1643313 < baseStart_1643313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643340 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 2, 2, 3]
def baseStart_1643340 : Nat := 118140960795 + 1643340 * 2 ^ 59
def prefixEnd_1643340 : Nat := 4983230072969 + 3 ^ 40 * 1643340 * 2
def baseEnd_1643340 : Nat := 843823298759705658392423

theorem tailTrace_1643340 : CollatzResearch.WordTrace tailWord_1643340 prefixEnd_1643340 843823298759705658392423 := by
  unfold tailWord_1643340
  simp only [CollatzResearch.WordTrace]
  refine ⟨29968766933233657486307737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39958355910978209981743649 29968766933233657486307737)
  ·
    refine ⟨22476575199925243114730803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29968766933233657486307737 22476575199925243114730803)
    ·
      refine ⟨33714862799887864672096205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22476575199925243114730803 33714862799887864672096205)
      ·
        refine ⟨12643073549957949252036077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33714862799887864672096205 12643073549957949252036077)
        ·
          refine ⟨4741152581234230969513529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12643073549957949252036077 4741152581234230969513529)
          ·
            refine ⟨3555864435925673227135147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4741152581234230969513529 3555864435925673227135147)
            ·
              refine ⟨5333796653888509840702721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3555864435925673227135147 5333796653888509840702721)
              ·
                refine ⟨4000347490416382380527041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5333796653888509840702721 4000347490416382380527041)
                ·
                  refine ⟨3000260617812286785395281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4000347490416382380527041 3000260617812286785395281)
                  ·
                    refine ⟨2250195463359215089046461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3000260617812286785395281 2250195463359215089046461)
                    ·
                      refine ⟨843823298759705658392423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2250195463359215089046461 843823298759705658392423)
                      ·
                        rfl

theorem cell23_1643340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_1643340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643340 prefixEnd_1643340 := by exact prefixLift 1643340
  have htrace : WordTrace (prefixWord ++ tailWord_1643340) baseStart_1643340 baseEnd_1643340 := by
    simpa [prefixWord, tailWord_1643340, baseEnd_1643340] using wordTrace_append hprefix tailTrace_1643340
  have hstable : (prefixWord ++ tailWord_1643340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643340).length < 2 ^ (prefixWord ++ tailWord_1643340).sum := by decide
  have hdescent : baseEnd_1643340 < baseStart_1643340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643394 : List Nat := [3, 4, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1643394 : Nat := 118140960795 + 1643394 * 2 ^ 59
def prefixEnd_1643394 : Nat := 4983230072969 + 3 ^ 40 * 1643394 * 2
def baseEnd_1643394 : Nat := 93761225190560938568575

theorem tailTrace_1643394 : CollatzResearch.WordTrace tailWord_1643394 prefixEnd_1643394 93761225190560938568575 := by
  unfold tailWord_1643394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14984875852067920548770309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39959668938847788130054157 14984875852067920548770309)
  ·
    refine ⟨2809664222262735102894433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14984875852067920548770309 2809664222262735102894433)
    ·
      refine ⟨2107248166697051327170825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2809664222262735102894433 2107248166697051327170825)
      ·
        refine ⟨1580436125022788495378119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2107248166697051327170825 1580436125022788495378119)
        ·
          refine ⟨2370654187534182743067179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580436125022788495378119 2370654187534182743067179)
          ·
            refine ⟨3555981281301274114600769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370654187534182743067179 3555981281301274114600769)
            ·
              refine ⟨2666985960975955585950577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3555981281301274114600769 2666985960975955585950577)
              ·
                refine ⟨2000239470731966689462933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666985960975955585950577 2000239470731966689462933)
                ·
                  refine ⟨93761225190560938568575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2000239470731966689462933 93761225190560938568575)
                  ·
                    rfl

theorem cell23_1643394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1643394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643394 prefixEnd_1643394 := by exact prefixLift 1643394
  have htrace : WordTrace (prefixWord ++ tailWord_1643394) baseStart_1643394 baseEnd_1643394 := by
    simpa [prefixWord, tailWord_1643394, baseEnd_1643394] using wordTrace_append hprefix tailTrace_1643394
  have hstable : (prefixWord ++ tailWord_1643394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643394).length < 2 ^ (prefixWord ++ tailWord_1643394).sum := by decide
  have hdescent : baseEnd_1643394 < baseStart_1643394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643403 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 4, 4]
def baseStart_1643403 : Nat := 118140960795 + 1643403 * 2 ^ 59
def prefixEnd_1643403 : Nat := 4983230072969 + 3 ^ 40 * 1643403 * 2
def baseEnd_1643403 : Nat := 281285216013646303968211

theorem tailTrace_1643403 : CollatzResearch.WordTrace tailWord_1643403 prefixEnd_1643403 281285216013646303968211 := by
  unfold tailWord_1643403
  simp only [CollatzResearch.WordTrace]
  refine ⟨59939831665239076732158863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39959887776826051154772575 59939831665239076732158863)
  ·
    refine ⟨89909747497858615098238295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59939831665239076732158863 89909747497858615098238295)
    ·
      refine ⟨134864621246787922647357443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89909747497858615098238295 134864621246787922647357443)
      ·
        refine ⟨202296931870181883971036165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134864621246787922647357443 202296931870181883971036165)
        ·
          refine ⟨37930674725659103244569281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202296931870181883971036165 37930674725659103244569281)
          ·
            refine ⟨28448006044244327433426961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37930674725659103244569281 28448006044244327433426961)
            ·
              refine ⟨21336004533183245575070221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28448006044244327433426961 21336004533183245575070221)
              ·
                refine ⟨8001001699943717090651333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21336004533183245575070221 8001001699943717090651333)
                ·
                  refine ⟨1500187818739446954497125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8001001699943717090651333 1500187818739446954497125)
                  ·
                    refine ⟨281285216013646303968211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1500187818739446954497125 281285216013646303968211)
                    ·
                      rfl

theorem cell23_1643403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 4].length) (baseStart_1643403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643403 prefixEnd_1643403 := by exact prefixLift 1643403
  have htrace : WordTrace (prefixWord ++ tailWord_1643403) baseStart_1643403 baseEnd_1643403 := by
    simpa [prefixWord, tailWord_1643403, baseEnd_1643403] using wordTrace_append hprefix tailTrace_1643403
  have hstable : (prefixWord ++ tailWord_1643403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643403).length < 2 ^ (prefixWord ++ tailWord_1643403).sum := by decide
  have hdescent : baseEnd_1643403 < baseStart_1643403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643404 : List Nat := [2, 2, 1, 2, 1, 2, 6, 2, 1, 1, 3]
def baseStart_1643404 : Nat := 118140960795 + 1643404 * 2 ^ 59
def prefixEnd_1643404 : Nat := 4983230072969 + 3 ^ 40 * 1643404 * 2
def baseEnd_1643404 : Nat := 843856161521593407992129

theorem tailTrace_1643404 : CollatzResearch.WordTrace tailWord_1643404 prefixEnd_1643404 843856161521593407992129 := by
  unfold tailWord_1643404
  simp only [CollatzResearch.WordTrace]
  refine ⟨29969934069117726951472633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39959912092156969268630177 29969934069117726951472633)
  ·
    refine ⟨22477450551838295213604475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29969934069117726951472633 22477450551838295213604475)
    ·
      refine ⟨33716175827757442820406713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22477450551838295213604475 33716175827757442820406713)
      ·
        refine ⟨25287131870818082115305035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33716175827757442820406713 25287131870818082115305035)
        ·
          refine ⟨37930697806227123172957553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25287131870818082115305035 37930697806227123172957553)
          ·
            refine ⟨28448023354670342379718165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37930697806227123172957553 28448023354670342379718165)
            ·
              refine ⟨1333501094750172299049289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28448023354670342379718165 1333501094750172299049289)
              ·
                refine ⟨1000125821062629224286967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1333501094750172299049289 1000125821062629224286967)
                ·
                  refine ⟨1500188731593943836430451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1000125821062629224286967 1500188731593943836430451)
                  ·
                    refine ⟨2250283097390915754645677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1500188731593943836430451 2250283097390915754645677)
                    ·
                      refine ⟨843856161521593407992129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2250283097390915754645677 843856161521593407992129)
                      ·
                        rfl

theorem cell23_1643404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_1643404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643404 prefixEnd_1643404 := by exact prefixLift 1643404
  have htrace : WordTrace (prefixWord ++ tailWord_1643404) baseStart_1643404 baseEnd_1643404 := by
    simpa [prefixWord, tailWord_1643404, baseEnd_1643404] using wordTrace_append hprefix tailTrace_1643404
  have hstable : (prefixWord ++ tailWord_1643404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643404).length < 2 ^ (prefixWord ++ tailWord_1643404).sum := by decide
  have hdescent : baseEnd_1643404 < baseStart_1643404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643431 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_1643431 : Nat := 118140960795 + 1643431 * 2 ^ 59
def prefixEnd_1643431 : Nat := 4983230072969 + 3 ^ 40 * 1643431 * 2
def baseEnd_1643431 : Nat := 843870025499264802354505

theorem tailTrace_1643431 : CollatzResearch.WordTrace tailWord_1643431 prefixEnd_1643431 843870025499264802354505 := by
  unfold tailWord_1643431
  simp only [CollatzResearch.WordTrace]
  refine ⟨59940852909137637514178147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39960568606091758342785431 59940852909137637514178147)
  ·
    refine ⟨89911279363706456271267221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59940852909137637514178147 89911279363706456271267221)
    ·
      refine ⟨4214591220173740137715651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89911279363706456271267221 4214591220173740137715651)
      ·
        refine ⟨6321886830260610206573477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4214591220173740137715651 6321886830260610206573477)
        ·
          refine ⟨1185353780673864413732527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6321886830260610206573477 1185353780673864413732527)
          ·
            refine ⟨1778030671010796620598791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185353780673864413732527 1778030671010796620598791)
            ·
              refine ⟨2667046006516194930898187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1778030671010796620598791 2667046006516194930898187)
              ·
                refine ⟨4000569009774292396347281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667046006516194930898187 4000569009774292396347281)
                ·
                  refine ⟨3000426757330719297260461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4000569009774292396347281 3000426757330719297260461)
                  ·
                    refine ⟨1125160033999019736472673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3000426757330719297260461 1125160033999019736472673)
                    ·
                      refine ⟨843870025499264802354505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125160033999019736472673 843870025499264802354505)
                      ·
                        rfl

theorem cell23_1643431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_1643431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643431 prefixEnd_1643431 := by exact prefixLift 1643431
  have htrace : WordTrace (prefixWord ++ tailWord_1643431) baseStart_1643431 baseEnd_1643431 := by
    simpa [prefixWord, tailWord_1643431, baseEnd_1643431] using wordTrace_append hprefix tailTrace_1643431
  have hstable : (prefixWord ++ tailWord_1643431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643431).length < 2 ^ (prefixWord ++ tailWord_1643431).sum := by decide
  have hdescent : baseEnd_1643431 < baseStart_1643431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643433 : List Nat := [1, 2, 1, 1, 1, 1, 9, 7]
def baseStart_1643433 : Nat := 118140960795 + 1643433 * 2 ^ 59
def prefixEnd_1643433 : Nat := 4983230072969 + 3 ^ 40 * 1643433 * 2
def baseEnd_1643433 : Nat := 31254483424465696093685

theorem tailTrace_1643433 : CollatzResearch.WordTrace tailWord_1643433 prefixEnd_1643433 31254483424465696093685 := by
  unfold tailWord_1643433
  simp only [CollatzResearch.WordTrace]
  refine ⟨59940925855130391855750953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39960617236753594570500635 59940925855130391855750953)
  ·
    refine ⟨44955694391347793891813215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59940925855130391855750953 44955694391347793891813215)
    ·
      refine ⟨67433541587021690837719823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44955694391347793891813215 67433541587021690837719823)
      ·
        refine ⟨101150312380532536256579735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67433541587021690837719823 101150312380532536256579735)
        ·
          refine ⟨151725468570798804384869603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101150312380532536256579735 151725468570798804384869603)
          ·
            refine ⟨227588202856198206577304405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151725468570798804384869603 227588202856198206577304405)
            ·
              refine ⟨1333524626110536366663893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 227588202856198206577304405 1333524626110536366663893)
              ·
                refine ⟨31254483424465696093685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1333524626110536366663893 31254483424465696093685)
                ·
                  rfl

theorem cell23_1643433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 7].length) (baseStart_1643433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643433 prefixEnd_1643433 := by exact prefixLift 1643433
  have htrace : WordTrace (prefixWord ++ tailWord_1643433) baseStart_1643433 baseEnd_1643433 := by
    simpa [prefixWord, tailWord_1643433, baseEnd_1643433] using wordTrace_append hprefix tailTrace_1643433
  have hstable : (prefixWord ++ tailWord_1643433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643433).length < 2 ^ (prefixWord ++ tailWord_1643433).sum := by decide
  have hdescent : baseEnd_1643433 < baseStart_1643433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643443 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 3]
def baseStart_1643443 : Nat := 118140960795 + 1643443 * 2 ^ 59
def prefixEnd_1643443 : Nat := 4983230072969 + 3 ^ 40 * 1643443 * 2
def baseEnd_1643443 : Nat := 843876187267118755404449

theorem tailTrace_1643443 : CollatzResearch.WordTrace tailWord_1643443 prefixEnd_1643443 843876187267118755404449 := by
  unfold tailWord_1643443
  simp only [CollatzResearch.WordTrace]
  refine ⟨59941290585094163563614983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39960860390062775709076655 59941290585094163563614983)
  ·
    refine ⟨89911935877641245345422475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59941290585094163563614983 89911935877641245345422475)
    ·
      refine ⟨134867903816461868018133713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89911935877641245345422475 134867903816461868018133713)
      ·
        refine ⟨101150927862346401013600285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134867903816461868018133713 101150927862346401013600285)
        ·
          refine ⟨37931597948379900380100107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101150927862346401013600285 37931597948379900380100107)
          ·
            refine ⟨56897396922569850570150161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37931597948379900380100107 56897396922569850570150161)
            ·
              refine ⟨42673047691927387927612621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56897396922569850570150161 42673047691927387927612621)
              ·
                refine ⟨16002392884472770472854733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42673047691927387927612621 16002392884472770472854733)
                ·
                  refine ⟨6000897331677288927320525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16002392884472770472854733 6000897331677288927320525)
                  ·
                    refine ⟨2250336499378983347745197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6000897331677288927320525 2250336499378983347745197)
                    ·
                      refine ⟨843876187267118755404449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2250336499378983347745197 843876187267118755404449)
                      ·
                        rfl

theorem cell23_1643443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 3].length) (baseStart_1643443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643443 prefixEnd_1643443 := by exact prefixLift 1643443
  have htrace : WordTrace (prefixWord ++ tailWord_1643443) baseStart_1643443 baseEnd_1643443 := by
    simpa [prefixWord, tailWord_1643443, baseEnd_1643443] using wordTrace_append hprefix tailTrace_1643443
  have hstable : (prefixWord ++ tailWord_1643443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643443).length < 2 ^ (prefixWord ++ tailWord_1643443).sum := by decide
  have hdescent : baseEnd_1643443 < baseStart_1643443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643444 : List Nat := [2, 5, 2, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_1643444 : Nat := 118140960795 + 1643444 * 2 ^ 59
def prefixEnd_1643444 : Nat := 4983230072969 + 3 ^ 40 * 1643444 * 2
def baseEnd_1643444 : Nat := 843876700747773251491945

theorem tailTrace_1643444 : CollatzResearch.WordTrace tailWord_1643444 prefixEnd_1643444 843876700747773251491945 := by
  unfold tailWord_1643444
  simp only [CollatzResearch.WordTrace]
  refine ⟨29970663529045270367200693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39960884705393693822934257 29970663529045270367200693)
  ·
    refine ⟨2809749705847994096925065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29970663529045270367200693 2809749705847994096925065)
    ·
      refine ⟨2107312279385995572693799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2809749705847994096925065 2107312279385995572693799)
      ·
        refine ⟨3160968419078993359040699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2107312279385995572693799 3160968419078993359040699)
        ·
          refine ⟨4741452628618490038561049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3160968419078993359040699 4741452628618490038561049)
          ·
            refine ⟨3556089471463867528920787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4741452628618490038561049 3556089471463867528920787)
            ·
              refine ⟨5334134207195801293381181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3556089471463867528920787 5334134207195801293381181)
              ·
                refine ⟨2000300327698425485017943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5334134207195801293381181 2000300327698425485017943)
                ·
                  refine ⟨3000450491547638227526915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000300327698425485017943 3000450491547638227526915)
                  ·
                    refine ⟨4500675737321457341290373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3000450491547638227526915 4500675737321457341290373)
                    ·
                      refine ⟨843876700747773251491945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4500675737321457341290373 843876700747773251491945)
                      ·
                        rfl

theorem cell23_1643444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_1643444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643444 prefixEnd_1643444 := by exact prefixLift 1643444
  have htrace : WordTrace (prefixWord ++ tailWord_1643444) baseStart_1643444 baseEnd_1643444 := by
    simpa [prefixWord, tailWord_1643444, baseEnd_1643444] using wordTrace_append hprefix tailTrace_1643444
  have hstable : (prefixWord ++ tailWord_1643444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643444).length < 2 ^ (prefixWord ++ tailWord_1643444).sum := by decide
  have hdescent : baseEnd_1643444 < baseStart_1643444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643447 : List Nat := [1, 1, 3, 1, 3, 1, 6, 1, 1, 2, 3]
def baseStart_1643447 : Nat := 118140960795 + 1643447 * 2 ^ 59
def prefixEnd_1643447 : Nat := 4983230072969 + 3 ^ 40 * 1643447 * 2
def baseEnd_1643447 : Nat := 843878241189736739754431

theorem tailTrace_1643447 : CollatzResearch.WordTrace tailWord_1643447 prefixEnd_1643447 843878241189736739754431 := by
  unfold tailWord_1643447
  simp only [CollatzResearch.WordTrace]
  refine ⟨59941436477079672246760595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39960957651386448164507063 59941436477079672246760595)
  ·
    refine ⟨89912154715619508370140893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59941436477079672246760595 89912154715619508370140893)
    ·
      refine ⟨33717058018357315638802835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89912154715619508370140893 33717058018357315638802835)
      ·
        refine ⟨50575587027535973458204253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33717058018357315638802835 50575587027535973458204253)
        ·
          refine ⟨18965845135325990046826595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50575587027535973458204253 18965845135325990046826595)
          ·
            refine ⟨28448767702988985070239893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18965845135325990046826595 28448767702988985070239893)
            ·
              refine ⟨1333535986077608675167495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28448767702988985070239893 1333535986077608675167495)
              ·
                refine ⟨2000303979116413012751243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1333535986077608675167495 2000303979116413012751243)
                ·
                  refine ⟨3000455968674619519126865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000303979116413012751243 3000455968674619519126865)
                  ·
                    refine ⟨2250341976505964639345149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3000455968674619519126865 2250341976505964639345149)
                    ·
                      refine ⟨843878241189736739754431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2250341976505964639345149 843878241189736739754431)
                      ·
                        rfl

theorem cell23_1643447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 1, 2, 3].length) (baseStart_1643447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643447 prefixEnd_1643447 := by exact prefixLift 1643447
  have htrace : WordTrace (prefixWord ++ tailWord_1643447) baseStart_1643447 baseEnd_1643447 := by
    simpa [prefixWord, tailWord_1643447, baseEnd_1643447] using wordTrace_append hprefix tailTrace_1643447
  have hstable : (prefixWord ++ tailWord_1643447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643447).length < 2 ^ (prefixWord ++ tailWord_1643447).sum := by decide
  have hdescent : baseEnd_1643447 < baseStart_1643447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643503 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 5]
def baseStart_1643503 : Nat := 118140960795 + 1643503 * 2 ^ 59
def prefixEnd_1643503 : Nat := 4983230072969 + 3 ^ 40 * 1643503 * 2
def baseEnd_1643503 : Nat := 843906996106388520654173

theorem tailTrace_1643503 : CollatzResearch.WordTrace tailWord_1643503 prefixEnd_1643503 843906996106388520654173 := by
  unfold tailWord_1643503
  simp only [CollatzResearch.WordTrace]
  refine ⟨59943478964876793810799163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39962319309917862540532775 59943478964876793810799163)
  ·
    refine ⟨89915218447315190716198745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59943478964876793810799163 89915218447315190716198745)
    ·
      refine ⟨67436413835486393037149059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89915218447315190716198745 67436413835486393037149059)
      ·
        refine ⟨101154620753229589555723589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67436413835486393037149059 101154620753229589555723589)
        ·
          refine ⟨18966491391230548041698173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101154620753229589555723589 18966491391230548041698173)
          ·
            refine ⟨7112434271711455515636815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18966491391230548041698173 7112434271711455515636815)
            ·
              refine ⟨10668651407567183273455223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7112434271711455515636815 10668651407567183273455223)
              ·
                refine ⟨16002977111350774910182835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10668651407567183273455223 16002977111350774910182835)
                ·
                  refine ⟨24004465667026162365274253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16002977111350774910182835 24004465667026162365274253)
                  ·
                    refine ⟨9001674625134810886977845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24004465667026162365274253 9001674625134810886977845)
                    ·
                      refine ⟨843906996106388520654173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9001674625134810886977845 843906996106388520654173)
                      ·
                        rfl

theorem cell23_1643503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_1643503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643503 prefixEnd_1643503 := by exact prefixLift 1643503
  have htrace : WordTrace (prefixWord ++ tailWord_1643503) baseStart_1643503 baseEnd_1643503 := by
    simpa [prefixWord, tailWord_1643503, baseEnd_1643503] using wordTrace_append hprefix tailTrace_1643503
  have hstable : (prefixWord ++ tailWord_1643503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643503).length < 2 ^ (prefixWord ++ tailWord_1643503).sum := by decide
  have hdescent : baseEnd_1643503 < baseStart_1643503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643538 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_1643538 : Nat := 118140960795 + 1643538 * 2 ^ 59
def prefixEnd_1643538 : Nat := 4983230072969 + 3 ^ 40 * 1643538 * 2
def baseEnd_1643538 : Nat := 843924967929295883716513

theorem tailTrace_1643538 : CollatzResearch.WordTrace tailWord_1643538 prefixEnd_1643538 843924967929295883716513 := by
  unfold tailWord_1643538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14986188879937498697080817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39963170346499996525548845 14986188879937498697080817)
  ·
    refine ⟨11239641659953124022810613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14986188879937498697080817 11239641659953124022810613)
    ·
      refine ⟨1053716405620605377138495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11239641659953124022810613 1053716405620605377138495)
      ·
        refine ⟨1580574608430908065707743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053716405620605377138495 1580574608430908065707743)
        ·
          refine ⟨2370861912646362098561615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580574608430908065707743 2370861912646362098561615)
          ·
            refine ⟨3556292868969543147842423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370861912646362098561615 3556292868969543147842423)
            ·
              refine ⟨5334439303454314721763635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3556292868969543147842423 5334439303454314721763635)
              ·
                refine ⟨8001658955181472082645453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334439303454314721763635 8001658955181472082645453)
                ·
                  refine ⟨3000622108193052030992045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8001658955181472082645453 3000622108193052030992045)
                  ·
                    refine ⟨1125233290572394511622017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3000622108193052030992045 1125233290572394511622017)
                    ·
                      refine ⟨843924967929295883716513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125233290572394511622017 843924967929295883716513)
                      ·
                        rfl

theorem cell23_1643538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_1643538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643538 prefixEnd_1643538 := by exact prefixLift 1643538
  have htrace : WordTrace (prefixWord ++ tailWord_1643538) baseStart_1643538 baseEnd_1643538 := by
    simpa [prefixWord, tailWord_1643538, baseEnd_1643538] using wordTrace_append hprefix tailTrace_1643538
  have hstable : (prefixWord ++ tailWord_1643538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643538).length < 2 ^ (prefixWord ++ tailWord_1643538).sum := by decide
  have hdescent : baseEnd_1643538 < baseStart_1643538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643563 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 5]
def baseStart_1643563 : Nat := 118140960795 + 1643563 * 2 ^ 59
def prefixEnd_1643563 : Nat := 4983230072969 + 3 ^ 40 * 1643563 * 2
def baseEnd_1643563 : Nat := 843937804945658285903897

theorem tailTrace_1643563 : CollatzResearch.WordTrace tailWord_1643563 prefixEnd_1643563 843937804945658285903897 := by
  unfold tailWord_1643563
  simp only [CollatzResearch.WordTrace]
  refine ⟨59945667344659424057983343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39963778229772949371988895 59945667344659424057983343)
  ·
    refine ⟨89918501016989136086975015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59945667344659424057983343 89918501016989136086975015)
    ·
      refine ⟨134877751525483704130462523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89918501016989136086975015 134877751525483704130462523)
      ·
        refine ⟨202316627288225556195693785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134877751525483704130462523 202316627288225556195693785)
        ·
          refine ⟨151737470466169167146770339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202316627288225556195693785 151737470466169167146770339)
          ·
            refine ⟨227606205699253750720155509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151737470466169167146770339 227606205699253750720155509)
            ·
              refine ⟨21338081784305039130014579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227606205699253750720155509 21338081784305039130014579)
              ·
                refine ⟨32007122676457558695021869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21338081784305039130014579 32007122676457558695021869)
                ·
                  refine ⟨12002671003671584510633201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32007122676457558695021869 12002671003671584510633201)
                  ·
                    refine ⟨9002003252753688382974901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12002671003671584510633201 9002003252753688382974901)
                    ·
                      refine ⟨843937804945658285903897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9002003252753688382974901 843937804945658285903897)
                      ·
                        rfl

theorem cell23_1643563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 5].length) (baseStart_1643563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643563 prefixEnd_1643563 := by exact prefixLift 1643563
  have htrace : WordTrace (prefixWord ++ tailWord_1643563) baseStart_1643563 baseEnd_1643563 := by
    simpa [prefixWord, tailWord_1643563, baseEnd_1643563] using wordTrace_append hprefix tailTrace_1643563
  have hstable : (prefixWord ++ tailWord_1643563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643563).length < 2 ^ (prefixWord ++ tailWord_1643563).sum := by decide
  have hdescent : baseEnd_1643563 < baseStart_1643563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643570 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_1643570 : Nat := 118140960795 + 1643570 * 2 ^ 59
def prefixEnd_1643570 : Nat := 4983230072969 + 3 ^ 40 * 1643570 * 2
def baseEnd_1643570 : Nat := 281313799770079919505455

theorem tailTrace_1643570 : CollatzResearch.WordTrace tailWord_1643570 prefixEnd_1643570 281313799770079919505455 := by
  unfold tailWord_1643570
  simp only [CollatzResearch.WordTrace]
  refine ⟨14986480663908516063372041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39963948437089376168992109 14986480663908516063372041)
  ·
    refine ⟨11239860497931387047529031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14986480663908516063372041 11239860497931387047529031)
    ·
      refine ⟨16859790746897080571293547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11239860497931387047529031 16859790746897080571293547)
      ·
        refine ⟨25289686120345620856940321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16859790746897080571293547 25289686120345620856940321)
        ·
          refine ⟨18967264590259215642705241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25289686120345620856940321 18967264590259215642705241)
          ·
            refine ⟨14225448442694411732028931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18967264590259215642705241 14225448442694411732028931)
            ·
              refine ⟨21338172664041617598043397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14225448442694411732028931 21338172664041617598043397)
              ·
                refine ⟨4000907374507803299633137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21338172664041617598043397 4000907374507803299633137)
                ·
                  refine ⟨3000680530880852474724853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4000907374507803299633137 3000680530880852474724853)
                  ·
                    refine ⟨281313799770079919505455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3000680530880852474724853 281313799770079919505455)
                    ·
                      rfl

theorem cell23_1643570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_1643570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643570 prefixEnd_1643570 := by exact prefixLift 1643570
  have htrace : WordTrace (prefixWord ++ tailWord_1643570) baseStart_1643570 baseEnd_1643570 := by
    simpa [prefixWord, tailWord_1643570, baseEnd_1643570] using wordTrace_append hprefix tailTrace_1643570
  have hstable : (prefixWord ++ tailWord_1643570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643570).length < 2 ^ (prefixWord ++ tailWord_1643570).sum := by decide
  have hdescent : baseEnd_1643570 < baseStart_1643570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643574 : List Nat := [5, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_1643574 : Nat := 118140960795 + 1643574 * 2 ^ 59
def prefixEnd_1643574 : Nat := 4983230072969 + 3 ^ 40 * 1643574 * 2
def baseEnd_1643574 : Nat := 93771494803650860318483

theorem tailTrace_1643574 : CollatzResearch.WordTrace tailWord_1643574 prefixEnd_1643574 93771494803650860318483 := by
  unfold tailWord_1643574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3746629284226223308539611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39964045698413048624422517 3746629284226223308539611)
  ·
    refine ⟨5619943926339334962809417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3746629284226223308539611 5619943926339334962809417)
    ·
      refine ⟨4214957944754501222107063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5619943926339334962809417 4214957944754501222107063)
      ·
        refine ⟨6322436917131751833160595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4214957944754501222107063 6322436917131751833160595)
        ·
          refine ⟨9483655375697627749740893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6322436917131751833160595 9483655375697627749740893)
          ·
            refine ⟨3556370765886610406152835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9483655375697627749740893 3556370765886610406152835)
            ·
              refine ⟨5334556148829915609229253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3556370765886610406152835 5334556148829915609229253)
              ·
                refine ⟨1000229277905609176730485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5334556148829915609229253 1000229277905609176730485)
                ·
                  refine ⟨93771494803650860318483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1000229277905609176730485 93771494803650860318483)
                  ·
                    rfl

theorem cell23_1643574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_1643574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643574 prefixEnd_1643574 := by exact prefixLift 1643574
  have htrace : WordTrace (prefixWord ++ tailWord_1643574) baseStart_1643574 baseEnd_1643574 := by
    simpa [prefixWord, tailWord_1643574, baseEnd_1643574] using wordTrace_append hprefix tailTrace_1643574
  have hstable : (prefixWord ++ tailWord_1643574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643574).length < 2 ^ (prefixWord ++ tailWord_1643574).sum := by decide
  have hdescent : baseEnd_1643574 < baseStart_1643574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643577 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 2, 5, 2]
def baseStart_1643577 : Nat := 118140960795 + 1643577 * 2 ^ 59
def prefixEnd_1643577 : Nat := 4983230072969 + 3 ^ 40 * 1643577 * 2
def baseEnd_1643577 : Nat := 843944993674821231128833

theorem tailTrace_1643577 : CollatzResearch.WordTrace tailWord_1643577 prefixEnd_1643577 843944993674821231128833 := by
  unfold tailWord_1643577
  simp only [CollatzResearch.WordTrace]
  refine ⟨59946177966608704448992985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39964118644405802965995323 59946177966608704448992985)
  ·
    refine ⟨44959633474956528336744739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59946177966608704448992985 44959633474956528336744739)
    ·
      refine ⟨67439450212434792505117109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44959633474956528336744739 67439450212434792505117109)
      ·
        refine ⟨6322448457415761797354729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67439450212434792505117109 6322448457415761797354729)
        ·
          refine ⟨4741836343061821348016047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6322448457415761797354729 4741836343061821348016047)
          ·
            refine ⟨7112754514592732022024071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4741836343061821348016047 7112754514592732022024071)
            ·
              refine ⟨10669131771889098033036107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7112754514592732022024071 10669131771889098033036107)
              ·
                refine ⟨16003697657833647049554161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10669131771889098033036107 16003697657833647049554161)
                ·
                  refine ⟨12002773243375235287165621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16003697657833647049554161 12002773243375235287165621)
                  ·
                    refine ⟨1125259991566428308171777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12002773243375235287165621 1125259991566428308171777)
                    ·
                      refine ⟨843944993674821231128833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125259991566428308171777 843944993674821231128833)
                      ·
                        rfl

theorem cell23_1643577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_1643577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643577 prefixEnd_1643577 := by exact prefixLift 1643577
  have htrace : WordTrace (prefixWord ++ tailWord_1643577) baseStart_1643577 baseEnd_1643577 := by
    simpa [prefixWord, tailWord_1643577, baseEnd_1643577] using wordTrace_append hprefix tailTrace_1643577
  have hstable : (prefixWord ++ tailWord_1643577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643577).length < 2 ^ (prefixWord ++ tailWord_1643577).sum := by decide
  have hdescent : baseEnd_1643577 < baseStart_1643577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643580 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_1643580 : Nat := 118140960795 + 1643580 * 2 ^ 59
def prefixEnd_1643580 : Nat := 4983230072969 + 3 ^ 40 * 1643580 * 2
def baseEnd_1643580 : Nat := 843946534116784719391319

theorem tailTrace_1643580 : CollatzResearch.WordTrace tailWord_1643580 prefixEnd_1643580 843946534116784719391319 := by
  unfold tailWord_1643580
  simp only [CollatzResearch.WordTrace]
  refine ⟨29973143692798917980676097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39964191590398557307568129 29973143692798917980676097)
  ·
    refine ⟨22479857769599188485507073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29973143692798917980676097 22479857769599188485507073)
    ·
      refine ⟨16859893327199391364130305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22479857769599188485507073 16859893327199391364130305)
      ·
        refine ⟨12644919995399543523097729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16859893327199391364130305 12644919995399543523097729)
        ·
          refine ⟨9483689996549657642323297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12644919995399543523097729 9483689996549657642323297)
          ·
            refine ⟨7112767497412243231742473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9483689996549657642323297 7112767497412243231742473)
            ·
              refine ⟨5334575623059182423806855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7112767497412243231742473 5334575623059182423806855)
              ·
                refine ⟨8001863434588773635710283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334575623059182423806855 8001863434588773635710283)
                ·
                  refine ⟨12002795151883160453565425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8001863434588773635710283 12002795151883160453565425)
                  ·
                    refine ⟨9002096363912370340174069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12002795151883160453565425 9002096363912370340174069)
                    ·
                      refine ⟨843946534116784719391319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9002096363912370340174069 843946534116784719391319)
                      ·
                        rfl

theorem cell23_1643580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_1643580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643580 prefixEnd_1643580 := by exact prefixLift 1643580
  have htrace : WordTrace (prefixWord ++ tailWord_1643580) baseStart_1643580 baseEnd_1643580 := by
    simpa [prefixWord, tailWord_1643580, baseEnd_1643580] using wordTrace_append hprefix tailTrace_1643580
  have hstable : (prefixWord ++ tailWord_1643580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643580).length < 2 ^ (prefixWord ++ tailWord_1643580).sum := by decide
  have hdescent : baseEnd_1643580 < baseStart_1643580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643583 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 2, 8]
def baseStart_1643583 : Nat := 118140960795 + 1643583 * 2 ^ 59
def prefixEnd_1643583 : Nat := 4983230072969 + 3 ^ 40 * 1643583 * 2
def baseEnd_1643583 : Nat := 281316024852916069217935

theorem tailTrace_1643583 : CollatzResearch.WordTrace tailWord_1643583 prefixEnd_1643583 281316024852916069217935 := by
  unfold tailWord_1643583
  simp only [CollatzResearch.WordTrace]
  refine ⟨59946396804586967473711403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39964264536391311649140935 59946396804586967473711403)
  ·
    refine ⟨89919595206880451210567105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59946396804586967473711403 89919595206880451210567105)
    ·
      refine ⟨67439696405160338407925329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89919595206880451210567105 67439696405160338407925329)
      ·
        refine ⟨50579772303870253805943997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67439696405160338407925329 50579772303870253805943997)
        ·
          refine ⟨18967414613951345177228999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50579772303870253805943997 18967414613951345177228999)
          ·
            refine ⟨28451121920927017765843499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18967414613951345177228999 28451121920927017765843499)
            ·
              refine ⟨42676682881390526648765249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28451121920927017765843499 42676682881390526648765249)
              ·
                refine ⟨32007512161042894986573937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42676682881390526648765249 32007512161042894986573937)
                ·
                  refine ⟨24005634120782171239930453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32007512161042894986573937 24005634120782171239930453)
                  ·
                    refine ⟨281316024852916069217935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24005634120782171239930453 281316024852916069217935)
                    ·
                      rfl

theorem cell23_1643583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_1643583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643583 prefixEnd_1643583 := by exact prefixLift 1643583
  have htrace : WordTrace (prefixWord ++ tailWord_1643583) baseStart_1643583 baseEnd_1643583 := by
    simpa [prefixWord, tailWord_1643583, baseEnd_1643583] using wordTrace_append hprefix tailTrace_1643583
  have hstable : (prefixWord ++ tailWord_1643583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643583).length < 2 ^ (prefixWord ++ tailWord_1643583).sum := by decide
  have hdescent : baseEnd_1643583 < baseStart_1643583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643603 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 6]
def baseStart_1643603 : Nat := 118140960795 + 1643603 * 2 ^ 59
def prefixEnd_1643603 : Nat := 4983230072969 + 3 ^ 40 * 1643603 * 2
def baseEnd_1643603 : Nat := 843958344171838129403713

theorem tailTrace_1643603 : CollatzResearch.WordTrace tailWord_1643603 prefixEnd_1643603 843958344171838129403713 := by
  unfold tailWord_1643603
  simp only [CollatzResearch.WordTrace]
  refine ⟨59947126264514510889439463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39964750843009673926292975 59947126264514510889439463)
  ·
    refine ⟨89920689396771766334159195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59947126264514510889439463 89920689396771766334159195)
    ·
      refine ⟨134881034095157649501238793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89920689396771766334159195 134881034095157649501238793)
      ·
        refine ⟨101160775571368237125929095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134881034095157649501238793 101160775571368237125929095)
        ·
          refine ⟨151741163357052355688893643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101160775571368237125929095 151741163357052355688893643)
          ·
            refine ⟨227611745035578533533340465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151741163357052355688893643 227611745035578533533340465)
            ·
              refine ⟨170708808776683900150005349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227611745035578533533340465 170708808776683900150005349)
              ·
                refine ⟨32007901645628231278126003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170708808776683900150005349 32007901645628231278126003)
                ·
                  refine ⟨48011852468442346917189005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32007901645628231278126003 48011852468442346917189005)
                  ·
                    refine ⟨18004444675665880093945877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48011852468442346917189005 18004444675665880093945877)
                    ·
                      refine ⟨843958344171838129403713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18004444675665880093945877 843958344171838129403713)
                      ·
                        rfl

theorem cell23_1643603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_1643603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643603 prefixEnd_1643603 := by exact prefixLift 1643603
  have htrace : WordTrace (prefixWord ++ tailWord_1643603) baseStart_1643603 baseEnd_1643603 := by
    simpa [prefixWord, tailWord_1643603, baseEnd_1643603] using wordTrace_append hprefix tailTrace_1643603
  have hstable : (prefixWord ++ tailWord_1643603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643603).length < 2 ^ (prefixWord ++ tailWord_1643603).sum := by decide
  have hdescent : baseEnd_1643603 < baseStart_1643603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643634 : List Nat := [3, 2, 1, 2, 2, 1, 1, 6, 1, 4]
def baseStart_1643634 : Nat := 118140960795 + 1643634 * 2 ^ 59
def prefixEnd_1643634 : Nat := 4983230072969 + 3 ^ 40 * 1643634 * 2
def baseEnd_1643634 : Nat := 281324754024042502705357

theorem tailTrace_1643634 : CollatzResearch.WordTrace tailWord_1643634 prefixEnd_1643634 281324754024042502705357 := by
  unfold tailWord_1643634
  simp only [CollatzResearch.WordTrace]
  refine ⟨14987064231850550795954489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39965504618268135455878637 14987064231850550795954489)
  ·
    refine ⟨11240298173887913096965867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14987064231850550795954489 11240298173887913096965867)
    ·
      refine ⟨16860447260831869645448801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11240298173887913096965867 16860447260831869645448801)
      ·
        refine ⟨12645335445623902234086601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16860447260831869645448801 12645335445623902234086601)
        ·
          refine ⟨9484001584217926675564951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12645335445623902234086601 9484001584217926675564951)
          ·
            refine ⟨14226002376326890013347427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9484001584217926675564951 14226002376326890013347427)
            ·
              refine ⟨21339003564490335020021141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14226002376326890013347427 21339003564490335020021141)
              ·
                refine ⟨1000265792085484454063491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21339003564490335020021141 1000265792085484454063491)
                ·
                  refine ⟨1500398688128226681095237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1000265792085484454063491 1500398688128226681095237)
                  ·
                    refine ⟨281324754024042502705357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1500398688128226681095237 281324754024042502705357)
                    ·
                      rfl

theorem cell23_1643634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_1643634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643634 prefixEnd_1643634 := by exact prefixLift 1643634
  have htrace : WordTrace (prefixWord ++ tailWord_1643634) baseStart_1643634 baseEnd_1643634 := by
    simpa [prefixWord, tailWord_1643634, baseEnd_1643634] using wordTrace_append hprefix tailTrace_1643634
  have hstable : (prefixWord ++ tailWord_1643634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643634).length < 2 ^ (prefixWord ++ tailWord_1643634).sum := by decide
  have hdescent : baseEnd_1643634 < baseStart_1643634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643660 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 3, 5]
def baseStart_1643660 : Nat := 118140960795 + 1643660 * 2 ^ 59
def prefixEnd_1643660 : Nat := 4983230072969 + 3 ^ 40 * 1643660 * 2
def baseEnd_1643660 : Nat := 281329204189714802130317

theorem tailTrace_1643660 : CollatzResearch.WordTrace tailWord_1643660 prefixEnd_1643660 281329204189714802130317 := by
  unfold tailWord_1643660
  simp only [CollatzResearch.WordTrace]
  refine ⟨29974602612654004812132217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39966136816872006416176289 29974602612654004812132217)
  ·
    refine ⟨22480951959490503609099163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29974602612654004812132217 22480951959490503609099163)
    ·
      refine ⟨33721427939235755413648745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22480951959490503609099163 33721427939235755413648745)
      ·
        refine ⟨25291070954426816560236559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33721427939235755413648745 25291070954426816560236559)
        ·
          refine ⟨37936606431640224840354839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25291070954426816560236559 37936606431640224840354839)
          ·
            refine ⟨56904909647460337260532259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37936606431640224840354839 56904909647460337260532259)
            ·
              refine ⟨85357364471190505890798389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56904909647460337260532259 85357364471190505890798389)
              ·
                refine ⟨8002252919174109927262349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85357364471190505890798389 8002252919174109927262349)
                ·
                  refine ⟨3000844844690291222723381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8002252919174109927262349 3000844844690291222723381)
                  ·
                    refine ⟨281329204189714802130317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3000844844690291222723381 281329204189714802130317)
                    ·
                      rfl

theorem cell23_1643660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_1643660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643660 prefixEnd_1643660 := by exact prefixLift 1643660
  have htrace : WordTrace (prefixWord ++ tailWord_1643660) baseStart_1643660 baseEnd_1643660 := by
    simpa [prefixWord, tailWord_1643660, baseEnd_1643660] using wordTrace_append hprefix tailTrace_1643660
  have hstable : (prefixWord ++ tailWord_1643660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643660).length < 2 ^ (prefixWord ++ tailWord_1643660).sum := by decide
  have hdescent : baseEnd_1643660 < baseStart_1643660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643667 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 1, 5, 2]
def baseStart_1643667 : Nat := 118140960795 + 1643667 * 2 ^ 59
def prefixEnd_1643667 : Nat := 4983230072969 + 3 ^ 40 * 1643667 * 2
def baseEnd_1643667 : Nat := 843991206933725879003419

theorem tailTrace_1643667 : CollatzResearch.WordTrace tailWord_1643667 prefixEnd_1643667 843991206933725879003419 := by
  unfold tailWord_1643667
  simp only [CollatzResearch.WordTrace]
  refine ⟨59949460536282649819769255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39966307024188433213179503 59949460536282649819769255)
  ·
    refine ⟨89924190804423974729653883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59949460536282649819769255 89924190804423974729653883)
    ·
      refine ⟨134886286206635962094480825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89924190804423974729653883 134886286206635962094480825)
      ·
        refine ⟨101164714654976971570860619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134886286206635962094480825 101164714654976971570860619)
        ·
          refine ⟨151747071982465457356290929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101164714654976971570860619 151747071982465457356290929)
          ·
            refine ⟨113810303986849093017218197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151747071982465457356290929 113810303986849093017218197)
            ·
              refine ⟨5334857999383551235182103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113810303986849093017218197 5334857999383551235182103)
              ·
                refine ⟨8002286999075326852773155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334857999383551235182103 8002286999075326852773155)
                ·
                  refine ⟨12003430498612990279159733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8002286999075326852773155 12003430498612990279159733)
                  ·
                    refine ⟨1125321609244967838671225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12003430498612990279159733 1125321609244967838671225)
                    ·
                      refine ⟨843991206933725879003419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125321609244967838671225 843991206933725879003419)
                      ·
                        rfl

theorem cell23_1643667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 5, 2].length) (baseStart_1643667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643667 prefixEnd_1643667 := by exact prefixLift 1643667
  have htrace : WordTrace (prefixWord ++ tailWord_1643667) baseStart_1643667 baseEnd_1643667 := by
    simpa [prefixWord, tailWord_1643667, baseEnd_1643667] using wordTrace_append hprefix tailTrace_1643667
  have hstable : (prefixWord ++ tailWord_1643667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643667).length < 2 ^ (prefixWord ++ tailWord_1643667).sum := by decide
  have hdescent : baseEnd_1643667 < baseStart_1643667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643677 : List Nat := [1, 4, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_1643677 : Nat := 118140960795 + 1643677 * 2 ^ 59
def prefixEnd_1643677 : Nat := 4983230072969 + 3 ^ 40 * 1643677 * 2
def baseEnd_1643677 : Nat := 281332113913423613292791

theorem tailTrace_1643677 : CollatzResearch.WordTrace tailWord_1643677 prefixEnd_1643677 281332113913423613292791 := by
  unfold tailWord_1643677
  simp only [CollatzResearch.WordTrace]
  refine ⟨59949825266246421527633285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39966550177497614351755523 59949825266246421527633285)
  ·
    refine ⟨11240592237421204036431241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59949825266246421527633285 11240592237421204036431241)
    ·
      refine ⟨8430444178065903027323431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11240592237421204036431241 8430444178065903027323431)
      ·
        refine ⟨12645666267098854540985147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8430444178065903027323431 12645666267098854540985147)
        ·
          refine ⟨18968499400648281811477721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12645666267098854540985147 18968499400648281811477721)
          ·
            refine ⟨14226374550486211358608291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18968499400648281811477721 14226374550486211358608291)
            ·
              refine ⟨21339561825729317037912437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14226374550486211358608291 21339561825729317037912437)
              ·
                refine ⟨2000583921162123472304291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21339561825729317037912437 2000583921162123472304291)
                ·
                  refine ⟨3000875881743185208456437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000583921162123472304291 3000875881743185208456437)
                  ·
                    refine ⟨281332113913423613292791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3000875881743185208456437 281332113913423613292791)
                    ·
                      rfl

theorem cell23_1643677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_1643677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643677 prefixEnd_1643677 := by exact prefixLift 1643677
  have htrace : WordTrace (prefixWord ++ tailWord_1643677) baseStart_1643677 baseEnd_1643677 := by
    simpa [prefixWord, tailWord_1643677, baseEnd_1643677] using wordTrace_append hprefix tailTrace_1643677
  have hstable : (prefixWord ++ tailWord_1643677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643677).length < 2 ^ (prefixWord ++ tailWord_1643677).sum := by decide
  have hdescent : baseEnd_1643677 < baseStart_1643677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643684 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 4, 3, 2]
def baseStart_1643684 : Nat := 118140960795 + 1643684 * 2 ^ 59
def prefixEnd_1643684 : Nat := 4983230072969 + 3 ^ 40 * 1643684 * 2
def baseEnd_1643684 : Nat := 843999936104852312490841

theorem tailTrace_1643684 : CollatzResearch.WordTrace tailWord_1643684 prefixEnd_1643684 843999936104852312490841 := by
  unfold tailWord_1643684
  simp only [CollatzResearch.WordTrace]
  refine ⟨29975040288610530861569053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39966720384814041148758737 29975040288610530861569053)
  ·
    refine ⟨11240640108228949073088395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29975040288610530861569053 11240640108228949073088395)
    ·
      refine ⟨16860960162343423609632593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11240640108228949073088395 16860960162343423609632593)
      ·
        refine ⟨12645720121757567707224445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16860960162343423609632593 12645720121757567707224445)
        ·
          refine ⟨4742145045659087890209167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12645720121757567707224445 4742145045659087890209167)
          ·
            refine ⟨7113217568488631835313751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4742145045659087890209167 7113217568488631835313751)
            ·
              refine ⟨10669826352732947752970627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7113217568488631835313751 10669826352732947752970627)
              ·
                refine ⟨16004739529099421629455941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10669826352732947752970627 16004739529099421629455941)
                ·
                  refine ⟨3000888661706141555522989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16004739529099421629455941 3000888661706141555522989)
                  ·
                    refine ⟨1125333248139803083321121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3000888661706141555522989 1125333248139803083321121)
                    ·
                      refine ⟨843999936104852312490841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125333248139803083321121 843999936104852312490841)
                      ·
                        rfl

theorem cell23_1643684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_1643684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643684 prefixEnd_1643684 := by exact prefixLift 1643684
  have htrace : WordTrace (prefixWord ++ tailWord_1643684) baseStart_1643684 baseEnd_1643684 := by
    simpa [prefixWord, tailWord_1643684, baseEnd_1643684] using wordTrace_append hprefix tailTrace_1643684
  have hstable : (prefixWord ++ tailWord_1643684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643684).length < 2 ^ (prefixWord ++ tailWord_1643684).sum := by decide
  have hdescent : baseEnd_1643684 < baseStart_1643684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643720 : List Nat := [2, 1, 3, 1, 2, 1, 4, 9]
def baseStart_1643720 : Nat := 118140960795 + 1643720 * 2 ^ 59
def prefixEnd_1643720 : Nat := 4983230072969 + 3 ^ 40 * 1643720 * 2
def baseEnd_1643720 : Nat := 31259941533644969320025

theorem tailTrace_1643720 : CollatzResearch.WordTrace tailWord_1643720 prefixEnd_1643720 31259941533644969320025 := by
  unfold tailWord_1643720
  simp only [CollatzResearch.WordTrace]
  refine ⟨29975696802545319935724307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39967595736727093247632409 29975696802545319935724307)
  ·
    refine ⟨44963545203817979903586461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29975696802545319935724307 44963545203817979903586461)
    ·
      refine ⟨16861329451431742463844923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44963545203817979903586461 16861329451431742463844923)
      ·
        refine ⟨25291994177147613695767385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16861329451431742463844923 25291994177147613695767385)
        ·
          refine ⟨18968995632860710271825539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25291994177147613695767385 18968995632860710271825539)
          ·
            refine ⟨28453493449291065407738309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18968995632860710271825539 28453493449291065407738309)
            ·
              refine ⟨5335030021742074763950933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28453493449291065407738309 5335030021742074763950933)
              ·
                refine ⟨31259941533644969320025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5335030021742074763950933 31259941533644969320025)
                ·
                  rfl

theorem cell23_1643720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 9].length) (baseStart_1643720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643720 prefixEnd_1643720 := by exact prefixLift 1643720
  have htrace : WordTrace (prefixWord ++ tailWord_1643720) baseStart_1643720 baseEnd_1643720 := by
    simpa [prefixWord, tailWord_1643720, baseEnd_1643720] using wordTrace_append hprefix tailTrace_1643720
  have hstable : (prefixWord ++ tailWord_1643720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643720).length < 2 ^ (prefixWord ++ tailWord_1643720).sum := by decide
  have hdescent : baseEnd_1643720 < baseStart_1643720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643760 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 5]
def baseStart_1643760 : Nat := 118140960795 + 1643760 * 2 ^ 59
def prefixEnd_1643760 : Nat := 4983230072969 + 3 ^ 40 * 1643760 * 2
def baseEnd_1643760 : Nat := 844038960634594015140491

theorem tailTrace_1643760 : CollatzResearch.WordTrace tailWord_1643760 prefixEnd_1643760 844038960634594015140491 := by
  unfold tailWord_1643760
  simp only [CollatzResearch.WordTrace]
  refine ⟨29976426262472863351452367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39968568349963817801936489 29976426262472863351452367)
  ·
    refine ⟨44964639393709295027178551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29976426262472863351452367 44964639393709295027178551)
    ·
      refine ⟨67446959090563942540767827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44964639393709295027178551 67446959090563942540767827)
      ·
        refine ⟨101170438635845913811151741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67446959090563942540767827 101170438635845913811151741)
        ·
          refine ⟨37938914488442217679181903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101170438635845913811151741 37938914488442217679181903)
          ·
            refine ⟨56908371732663326518772855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37938914488442217679181903 56908371732663326518772855)
            ·
              refine ⟨85362557598994989778159283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56908371732663326518772855 85362557598994989778159283)
              ·
                refine ⟨128043836398492484667238925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85362557598994989778159283 128043836398492484667238925)
                ·
                  refine ⟨48016438649434681750214597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128043836398492484667238925 48016438649434681750214597)
                  ·
                    refine ⟨9003082246769002828165237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48016438649434681750214597 9003082246769002828165237)
                    ·
                      refine ⟨844038960634594015140491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9003082246769002828165237 844038960634594015140491)
                      ·
                        rfl

theorem cell23_1643760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_1643760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643760 prefixEnd_1643760 := by exact prefixLift 1643760
  have htrace : WordTrace (prefixWord ++ tailWord_1643760) baseStart_1643760 baseEnd_1643760 := by
    simpa [prefixWord, tailWord_1643760, baseEnd_1643760] using wordTrace_append hprefix tailTrace_1643760
  have hstable : (prefixWord ++ tailWord_1643760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643760).length < 2 ^ (prefixWord ++ tailWord_1643760).sum := by decide
  have hdescent : baseEnd_1643760 < baseStart_1643760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643804 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_1643804 : Nat := 118140960795 + 1643804 * 2 ^ 59
def prefixEnd_1643804 : Nat := 4983230072969 + 3 ^ 40 * 1643804 * 2
def baseEnd_1643804 : Nat := 844061553783391842990289

theorem tailTrace_1643804 : CollatzResearch.WordTrace tailWord_1643804 prefixEnd_1643804 844061553783391842990289 := by
  unfold tailWord_1643804
  simp only [CollatzResearch.WordTrace]
  refine ⟨29977228668393161108753233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39969638224524214811670977 29977228668393161108753233)
  ·
    refine ⟨22482921501294870831564925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29977228668393161108753233 22482921501294870831564925)
    ·
      refine ⟨8431095562985576561836847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22482921501294870831564925 8431095562985576561836847)
      ·
        refine ⟨12646643344478364842755271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8431095562985576561836847 12646643344478364842755271)
        ·
          refine ⟨18969965016717547264132907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12646643344478364842755271 18969965016717547264132907)
          ·
            refine ⟨28454947525076320896199361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18969965016717547264132907 28454947525076320896199361)
            ·
              refine ⟨21341210643807240672149521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28454947525076320896199361 21341210643807240672149521)
              ·
                refine ⟨16005907982855430504112141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21341210643807240672149521 16005907982855430504112141)
                ·
                  refine ⟨6002215493570786439042053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16005907982855430504112141 6002215493570786439042053)
                  ·
                    refine ⟨1125415405044522457320385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6002215493570786439042053 1125415405044522457320385)
                    ·
                      refine ⟨844061553783391842990289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125415405044522457320385 844061553783391842990289)
                      ·
                        rfl

theorem cell23_1643804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_1643804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643804 prefixEnd_1643804 := by exact prefixLift 1643804
  have htrace : WordTrace (prefixWord ++ tailWord_1643804) baseStart_1643804 baseEnd_1643804 := by
    simpa [prefixWord, tailWord_1643804, baseEnd_1643804] using wordTrace_append hprefix tailTrace_1643804
  have hstable : (prefixWord ++ tailWord_1643804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643804).length < 2 ^ (prefixWord ++ tailWord_1643804).sum := by decide
  have hdescent : baseEnd_1643804 < baseStart_1643804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643827 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 7]
def baseStart_1643827 : Nat := 118140960795 + 1643827 * 2 ^ 59
def prefixEnd_1643827 : Nat := 4983230072969 + 3 ^ 40 * 1643827 * 2
def baseEnd_1643827 : Nat := 93785929315382805889187

theorem tailTrace_1643827 : CollatzResearch.WordTrace tailWord_1643827 prefixEnd_1643827 93785929315382805889187 := by
  unfold tailWord_1643827
  simp only [CollatzResearch.WordTrace]
  refine ⟨59955296215702997145593735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39970197477135331430395823 59955296215702997145593735)
  ·
    refine ⟨89932944323554495718390603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59955296215702997145593735 89932944323554495718390603)
    ·
      refine ⟨134899416485331743577585905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89932944323554495718390603 134899416485331743577585905)
      ·
        refine ⟨101174562363998807683189429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134899416485331743577585905 101174562363998807683189429)
        ·
          refine ⟨9485115221624888220299009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101174562363998807683189429 9485115221624888220299009)
          ·
            refine ⟨7113836416218666165224257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9485115221624888220299009 7113836416218666165224257)
            ·
              refine ⟨5335377312163999623918193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7113836416218666165224257 5335377312163999623918193)
              ·
                refine ⟨4001532984122999717938645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5335377312163999623918193 4001532984122999717938645)
                ·
                  refine ⟨93785929315382805889187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4001532984122999717938645 93785929315382805889187)
                  ·
                    rfl

theorem cell23_1643827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 7].length) (baseStart_1643827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643827 prefixEnd_1643827 := by exact prefixLift 1643827
  have htrace : WordTrace (prefixWord ++ tailWord_1643827) baseStart_1643827 baseEnd_1643827 := by
    simpa [prefixWord, tailWord_1643827, baseEnd_1643827] using wordTrace_append hprefix tailTrace_1643827
  have hstable : (prefixWord ++ tailWord_1643827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643827).length < 2 ^ (prefixWord ++ tailWord_1643827).sum := by decide
  have hdescent : baseEnd_1643827 < baseStart_1643827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643864 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 2, 5, 2]
def baseStart_1643864 : Nat := 118140960795 + 1643864 * 2 ^ 59
def prefixEnd_1643864 : Nat := 4983230072969 + 3 ^ 40 * 1643864 * 2
def baseEnd_1643864 : Nat := 844092362622661608240013

theorem tailTrace_1643864 : CollatzResearch.WordTrace tailWord_1643864 prefixEnd_1643864 844092362622661608240013 := by
  unfold tailWord_1643864
  simp only [CollatzResearch.WordTrace]
  refine ⟨29978322858284476232345323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39971097144379301643127097 29978322858284476232345323)
  ·
    refine ⟨44967484287426714348517985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29978322858284476232345323 44967484287426714348517985)
    ·
      refine ⟨33725613215570035761388489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44967484287426714348517985 33725613215570035761388489)
      ·
        refine ⟨25294209911677526821041367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33725613215570035761388489 25294209911677526821041367)
        ·
          refine ⟨37941314867516290231562051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25294209911677526821041367 37941314867516290231562051)
          ·
            refine ⟨56911972301274435347343077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37941314867516290231562051 56911972301274435347343077)
            ·
              refine ⟨10670994806488956627626827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56911972301274435347343077 10670994806488956627626827)
              ·
                refine ⟨16006492209733434941440241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10670994806488956627626827 16006492209733434941440241)
                ·
                  refine ⟨12004869157300076206080181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16006492209733434941440241 12004869157300076206080181)
                  ·
                    refine ⟨1125456483496882144320017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12004869157300076206080181 1125456483496882144320017)
                    ·
                      refine ⟨844092362622661608240013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125456483496882144320017 844092362622661608240013)
                      ·
                        rfl

theorem cell23_1643864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_1643864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643864 prefixEnd_1643864 := by exact prefixLift 1643864
  have htrace : WordTrace (prefixWord ++ tailWord_1643864) baseStart_1643864 baseEnd_1643864 := by
    simpa [prefixWord, tailWord_1643864, baseEnd_1643864] using wordTrace_append hprefix tailTrace_1643864
  have hstable : (prefixWord ++ tailWord_1643864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643864).length < 2 ^ (prefixWord ++ tailWord_1643864).sum := by decide
  have hdescent : baseEnd_1643864 < baseStart_1643864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643874 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_1643874 : Nat := 118140960795 + 1643874 * 2 ^ 59
def prefixEnd_1643874 : Nat := 4983230072969 + 3 ^ 40 * 1643874 * 2
def baseEnd_1643874 : Nat := 281365832476402189704989

theorem tailTrace_1643874 : CollatzResearch.WordTrace tailWord_1643874 prefixEnd_1643874 281365832476402189704989 := by
  unfold tailWord_1643874
  simp only [CollatzResearch.WordTrace]
  refine ⟨14989252611633181043138669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39971340297688482781703117 14989252611633181043138669)
  ·
    refine ⟨5620969729362442891177001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14989252611633181043138669 5620969729362442891177001)
    ·
      refine ⟨4215727297021832168382751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5620969729362442891177001 4215727297021832168382751)
      ·
        refine ⟨6323590945532748252574127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4215727297021832168382751 6323590945532748252574127)
        ·
          refine ⟨9485386418299122378861191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6323590945532748252574127 9485386418299122378861191)
          ·
            refine ⟨14228079627448683568291787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9485386418299122378861191 14228079627448683568291787)
            ·
              refine ⟨21342119441173025352437681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14228079627448683568291787 21342119441173025352437681)
              ·
                refine ⟨16006589580879769014328261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21342119441173025352437681 16006589580879769014328261)
                ·
                  refine ⟨3001235546414956690186549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16006589580879769014328261 3001235546414956690186549)
                  ·
                    refine ⟨281365832476402189704989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3001235546414956690186549 281365832476402189704989)
                    ·
                      rfl

theorem cell23_1643874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_1643874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643874 prefixEnd_1643874 := by exact prefixLift 1643874
  have htrace : WordTrace (prefixWord ++ tailWord_1643874) baseStart_1643874 baseEnd_1643874 := by
    simpa [prefixWord, tailWord_1643874, baseEnd_1643874] using wordTrace_append hprefix tailTrace_1643874
  have hstable : (prefixWord ++ tailWord_1643874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643874).length < 2 ^ (prefixWord ++ tailWord_1643874).sum := by decide
  have hdescent : baseEnd_1643874 < baseStart_1643874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643921 : List Nat := [1, 2, 2, 1, 1, 1, 2, 8, 1, 4]
def baseStart_1643921 : Nat := 118140960795 + 1643921 * 2 ^ 59
def prefixEnd_1643921 : Nat := 4983230072969 + 3 ^ 40 * 1643921 * 2
def baseEnd_1643921 : Nat := 281373877006655961742417

theorem tailTrace_1643921 : CollatzResearch.WordTrace tailWord_1643921 prefixEnd_1643921 281373877006655961742417 := by
  unfold tailWord_1643921
  simp only [CollatzResearch.WordTrace]
  refine ⟨59958724677362451199515617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39972483118241634133010411 59958724677362451199515617)
  ·
    refine ⟨44969043508021838399636713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59958724677362451199515617 44969043508021838399636713)
    ·
      refine ⟨33726782631016378799727535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44969043508021838399636713 33726782631016378799727535)
      ·
        refine ⟨50590173946524568199591303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33726782631016378799727535 50590173946524568199591303)
        ·
          refine ⟨75885260919786852299386955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50590173946524568199591303 75885260919786852299386955)
          ·
            refine ⟨113827891379680278449080433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75885260919786852299386955 113827891379680278449080433)
            ·
              refine ⟨85370918534760208836810325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113827891379680278449080433 85370918534760208836810325)
              ·
                refine ⟨1000440451579221197306371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 85370918534760208836810325 1000440451579221197306371)
                ·
                  refine ⟨1500660677368831795959557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1000440451579221197306371 1500660677368831795959557)
                  ·
                    refine ⟨281373877006655961742417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1500660677368831795959557 281373877006655961742417)
                    ·
                      rfl

theorem cell23_1643921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_1643921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643921 prefixEnd_1643921 := by exact prefixLift 1643921
  have htrace : WordTrace (prefixWord ++ tailWord_1643921) baseStart_1643921 baseEnd_1643921 := by
    simpa [prefixWord, tailWord_1643921, baseEnd_1643921] using wordTrace_append hprefix tailTrace_1643921
  have hstable : (prefixWord ++ tailWord_1643921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643921).length < 2 ^ (prefixWord ++ tailWord_1643921).sum := by decide
  have hdescent : baseEnd_1643921 < baseStart_1643921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643928 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 2, 4, 2]
def baseStart_1643928 : Nat := 118140960795 + 1643928 * 2 ^ 59
def prefixEnd_1643928 : Nat := 4983230072969 + 3 ^ 40 * 1643928 * 2
def baseEnd_1643928 : Nat := 844125225384549357839719

theorem tailTrace_1643928 : CollatzResearch.WordTrace tailWord_1643928 prefixEnd_1643928 844125225384549357839719 := by
  unfold tailWord_1643928
  simp only [CollatzResearch.WordTrace]
  refine ⟨29979489994168545697510219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39972653325558060930013625 29979489994168545697510219)
  ·
    refine ⟨44969234991252818546265329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29979489994168545697510219 44969234991252818546265329)
    ·
      refine ⟨33726926243439613909698997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44969234991252818546265329 33726926243439613909698997)
      ·
        refine ⟨3161899335322463804034281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33726926243439613909698997 3161899335322463804034281)
        ·
          refine ⟨2371424501491847853025711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3161899335322463804034281 2371424501491847853025711)
          ·
            refine ⟨3557136752237771779538567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2371424501491847853025711 3557136752237771779538567)
            ·
              refine ⟨5335705128356657669307851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3557136752237771779538567 5335705128356657669307851)
              ·
                refine ⟨8003557692534986503961777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5335705128356657669307851 8003557692534986503961777)
                ·
                  refine ⟨6002668269401239877971333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8003557692534986503961777 6002668269401239877971333)
                  ·
                    refine ⟨1125500300512732477119625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6002668269401239877971333 1125500300512732477119625)
                    ·
                      refine ⟨844125225384549357839719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125500300512732477119625 844125225384549357839719)
                      ·
                        rfl

theorem cell23_1643928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_1643928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643928 prefixEnd_1643928 := by exact prefixLift 1643928
  have htrace : WordTrace (prefixWord ++ tailWord_1643928) baseStart_1643928 baseEnd_1643928 := by
    simpa [prefixWord, tailWord_1643928, baseEnd_1643928] using wordTrace_append hprefix tailTrace_1643928
  have hstable : (prefixWord ++ tailWord_1643928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643928).length < 2 ^ (prefixWord ++ tailWord_1643928).sum := by decide
  have hdescent : baseEnd_1643928 < baseStart_1643928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643971 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 2, 3, 2]
def baseStart_1643971 : Nat := 118140960795 + 1643971 * 2 ^ 59
def prefixEnd_1643971 : Nat := 4983230072969 + 3 ^ 40 * 1643971 * 2
def baseEnd_1643971 : Nat := 844147305052692689602021

theorem tailTrace_1643971 : CollatzResearch.WordTrace tailWord_1643971 prefixEnd_1643971 844147305052692689602021 := by
  unfold tailWord_1643971
  simp only [CollatzResearch.WordTrace]
  refine ⟨59960548327181309738835767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39973698884787539825890511 59960548327181309738835767)
  ·
    refine ⟨89940822490771964608253651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59960548327181309738835767 89940822490771964608253651)
    ·
      refine ⟨134911233736157946912380477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89940822490771964608253651 134911233736157946912380477)
      ·
        refine ⟨50591712651059230092142679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134911233736157946912380477 50591712651059230092142679)
        ·
          refine ⟨75887568976588845138214019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50591712651059230092142679 75887568976588845138214019)
          ·
            refine ⟨113831353464883267707321029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75887568976588845138214019 113831353464883267707321029)
            ·
              refine ⟨21343378774665612695122693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113831353464883267707321029 21343378774665612695122693)
              ·
                refine ⟨4001883520249802380335505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21343378774665612695122693 4001883520249802380335505)
                ·
                  refine ⟨3001412640187351785251629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4001883520249802380335505 3001412640187351785251629)
                  ·
                    refine ⟨1125529740070256919469361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3001412640187351785251629 1125529740070256919469361)
                    ·
                      refine ⟨844147305052692689602021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125529740070256919469361 844147305052692689602021)
                      ·
                        rfl

theorem cell23_1643971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 3, 2].length) (baseStart_1643971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643971 prefixEnd_1643971 := by exact prefixLift 1643971
  have htrace : WordTrace (prefixWord ++ tailWord_1643971) baseStart_1643971 baseEnd_1643971 := by
    simpa [prefixWord, tailWord_1643971, baseEnd_1643971] using wordTrace_append hprefix tailTrace_1643971
  have hstable : (prefixWord ++ tailWord_1643971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643971).length < 2 ^ (prefixWord ++ tailWord_1643971).sum := by decide
  have hdescent : baseEnd_1643971 < baseStart_1643971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1643978 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 3, 1, 3]
def baseStart_1643978 : Nat := 118140960795 + 1643978 * 2 ^ 59
def prefixEnd_1643978 : Nat := 4983230072969 + 3 ^ 40 * 1643978 * 2
def baseEnd_1643978 : Nat := 844150899417274162214489

theorem tailTrace_1643978 : CollatzResearch.WordTrace tailWord_1643978 prefixEnd_1643978 844150899417274162214489 := by
  unfold tailWord_1643978
  simp only [CollatzResearch.WordTrace]
  refine ⟨14990200909538987483585147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39973869092103966622893725 14990200909538987483585147)
  ·
    refine ⟨22485301364308481225377721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14990200909538987483585147 22485301364308481225377721)
    ·
      refine ⟨16863976023231360919033291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22485301364308481225377721 16863976023231360919033291)
      ·
        refine ⟨25295964034847041378549937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16863976023231360919033291 25295964034847041378549937)
        ·
          refine ⟨18971973026135281033912453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25295964034847041378549937 18971973026135281033912453)
          ·
            refine ⟨3557244942400365193858585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18971973026135281033912453 3557244942400365193858585)
            ·
              refine ⟨2667933706800273895393939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3557244942400365193858585 2667933706800273895393939)
              ·
                refine ⟨4001900560200410843090909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667933706800273895393939 4001900560200410843090909)
                ·
                  refine ⟨1500712710075154066159091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4001900560200410843090909 1500712710075154066159091)
                  ·
                    refine ⟨2251069065112731099238637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1500712710075154066159091 2251069065112731099238637)
                    ·
                      refine ⟨844150899417274162214489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2251069065112731099238637 844150899417274162214489)
                      ·
                        rfl

theorem cell23_1643978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_1643978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1643978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1643978 prefixEnd_1643978 := by exact prefixLift 1643978
  have htrace : WordTrace (prefixWord ++ tailWord_1643978) baseStart_1643978 baseEnd_1643978 := by
    simpa [prefixWord, tailWord_1643978, baseEnd_1643978] using wordTrace_append hprefix tailTrace_1643978
  have hstable : (prefixWord ++ tailWord_1643978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1643978).length < 2 ^ (prefixWord ++ tailWord_1643978).sum := by decide
  have hdescent : baseEnd_1643978 < baseStart_1643978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1643978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644001 : List Nat := [1, 2, 3, 1, 2, 3, 1, 4, 1, 1, 4]
def baseStart_1644001 : Nat := 118140960795 + 1644001 * 2 ^ 59
def prefixEnd_1644001 : Nat := 4983230072969 + 3 ^ 40 * 1644001 * 2
def baseEnd_1644001 : Nat := 844162709472327572226883

theorem tailTrace_1644001 : CollatzResearch.WordTrace tailWord_1644001 prefixEnd_1644001 844162709472327572226883 := by
  unfold tailWord_1644001
  simp only [CollatzResearch.WordTrace]
  refine ⟨59961642517072624862427857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39974428344715083241618571 59961642517072624862427857)
  ·
    refine ⟨44971231887804468646820893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59961642517072624862427857 44971231887804468646820893)
    ·
      refine ⟨16864211957926675742557835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44971231887804468646820893 16864211957926675742557835)
      ·
        refine ⟨25296317936890013613836753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16864211957926675742557835 25296317936890013613836753)
        ·
          refine ⟨18972238452667510210377565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25296317936890013613836753 18972238452667510210377565)
          ·
            refine ⟨7114589419750316328891587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18972238452667510210377565 7114589419750316328891587)
            ·
              refine ⟨10671884129625474493337381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7114589419750316328891587 10671884129625474493337381)
              ·
                refine ⟨2000978274304776467500759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10671884129625474493337381 2000978274304776467500759)
                ·
                  refine ⟨3001467411457164701251139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000978274304776467500759 3001467411457164701251139)
                  ·
                    refine ⟨4502201117185747051876709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3001467411457164701251139 4502201117185747051876709)
                    ·
                      refine ⟨844162709472327572226883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4502201117185747051876709 844162709472327572226883)
                      ·
                        rfl

theorem cell23_1644001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_1644001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644001 prefixEnd_1644001 := by exact prefixLift 1644001
  have htrace : WordTrace (prefixWord ++ tailWord_1644001) baseStart_1644001 baseEnd_1644001 := by
    simpa [prefixWord, tailWord_1644001, baseEnd_1644001] using wordTrace_append hprefix tailTrace_1644001
  have hstable : (prefixWord ++ tailWord_1644001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644001).length < 2 ^ (prefixWord ++ tailWord_1644001).sum := by decide
  have hdescent : baseEnd_1644001 < baseStart_1644001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644004 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_1644004 : Nat := 118140960795 + 1644004 * 2 ^ 59
def prefixEnd_1644004 : Nat := 4983230072969 + 3 ^ 40 * 1644004 * 2
def baseEnd_1644004 : Nat := 844164249914291060489369

theorem tailTrace_1644004 : CollatzResearch.WordTrace tailWord_1644004 prefixEnd_1644004 844164249914291060489369 := by
  unfold tailWord_1644004
  simp only [CollatzResearch.WordTrace]
  refine ⟨29980875968030878187393533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39974501290707837583191377 29980875968030878187393533)
  ·
    refine ⟨11242828488011579320272575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29980875968030878187393533 11242828488011579320272575)
    ·
      refine ⟨16864242732017368980408863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11242828488011579320272575 16864242732017368980408863)
      ·
        refine ⟨25296364098026053470613295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16864242732017368980408863 25296364098026053470613295)
        ·
          refine ⟨37944546147039080205919943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25296364098026053470613295 37944546147039080205919943)
          ·
            refine ⟨56916819220558620308879915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37944546147039080205919943 56916819220558620308879915)
            ·
              refine ⟨85375228830837930463319873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56916819220558620308879915 85375228830837930463319873)
              ·
                refine ⟨64031421623128447847489905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85375228830837930463319873 64031421623128447847489905)
                ·
                  refine ⟨48023566217346335885617429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64031421623128447847489905 48023566217346335885617429)
                  ·
                    refine ⟨2251104666438109494638317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48023566217346335885617429 2251104666438109494638317)
                    ·
                      refine ⟨844164249914291060489369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2251104666438109494638317 844164249914291060489369)
                      ·
                        rfl

theorem cell23_1644004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_1644004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644004 prefixEnd_1644004 := by exact prefixLift 1644004
  have htrace : WordTrace (prefixWord ++ tailWord_1644004) baseStart_1644004 baseEnd_1644004 := by
    simpa [prefixWord, tailWord_1644004, baseEnd_1644004] using wordTrace_append hprefix tailTrace_1644004
  have hstable : (prefixWord ++ tailWord_1644004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644004).length < 2 ^ (prefixWord ++ tailWord_1644004).sum := by decide
  have hdescent : baseEnd_1644004 < baseStart_1644004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644018 : List Nat := [3, 2, 1, 4, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1644018 : Nat := 118140960795 + 1644018 * 2 ^ 59
def prefixEnd_1644018 : Nat := 4983230072969 + 3 ^ 40 * 1644018 * 2
def baseEnd_1644018 : Nat := 844171438643454005714305

theorem tailTrace_1644018 : CollatzResearch.WordTrace tailWord_1644018 prefixEnd_1644018 844171438643454005714305 := by
  unfold tailWord_1644018
  simp only [CollatzResearch.WordTrace]
  refine ⟨14990565639502759191449177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39974841705340691177197805 14990565639502759191449177)
  ·
    refine ⟨11242924229627069393586883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14990565639502759191449177 11242924229627069393586883)
    ·
      refine ⟨16864386344440604090380325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11242924229627069393586883 16864386344440604090380325)
      ·
        refine ⟨3162072439582613266946311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16864386344440604090380325 3162072439582613266946311)
        ·
          refine ⟨4743108659373919900419467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3162072439582613266946311 4743108659373919900419467)
          ·
            refine ⟨7114662989060879850629201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4743108659373919900419467 7114662989060879850629201)
            ·
              refine ⟨5335997241795659887971901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7114662989060879850629201 5335997241795659887971901)
              ·
                refine ⟨2000998965673372457989463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5335997241795659887971901 2000998965673372457989463)
                ·
                  refine ⟨3001498448510058686984195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2000998965673372457989463 3001498448510058686984195)
                  ·
                    refine ⟨4502247672765088030476293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3001498448510058686984195 4502247672765088030476293)
                    ·
                      refine ⟨844171438643454005714305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4502247672765088030476293 844171438643454005714305)
                      ·
                        rfl

theorem cell23_1644018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1644018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644018 prefixEnd_1644018 := by exact prefixLift 1644018
  have htrace : WordTrace (prefixWord ++ tailWord_1644018) baseStart_1644018 baseEnd_1644018 := by
    simpa [prefixWord, tailWord_1644018, baseEnd_1644018] using wordTrace_append hprefix tailTrace_1644018
  have hstable : (prefixWord ++ tailWord_1644018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644018).length < 2 ^ (prefixWord ++ tailWord_1644018).sum := by decide
  have hdescent : baseEnd_1644018 < baseStart_1644018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644024 : List Nat := [2, 1, 2, 1, 1, 7, 9]
def baseStart_1644024 : Nat := 118140960795 + 1644024 * 2 ^ 59
def prefixEnd_1644024 : Nat := 4983230072969 + 3 ^ 40 * 1644024 * 2
def baseEnd_1644024 : Nat := 10421907648486184965917

theorem tailTrace_1644024 : CollatzResearch.WordTrace tailWord_1644024 prefixEnd_1644024 10421907648486184965917 := by
  unfold tailWord_1644024
  simp only [CollatzResearch.WordTrace]
  refine ⟨29981240697994649895257563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39974987597326199860343417 29981240697994649895257563)
  ·
    refine ⟨44971861046991974842886345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29981240697994649895257563 44971861046991974842886345)
    ·
      refine ⟨33728895785243981132164759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44971861046991974842886345 33728895785243981132164759)
      ·
        refine ⟨50593343677865971698247139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33728895785243981132164759 50593343677865971698247139)
        ·
          refine ⟨75890015516798957547370709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50593343677865971698247139 75890015516798957547370709)
          ·
            refine ⟨1778672238674975567516501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 75890015516798957547370709 1778672238674975567516501)
            ·
              refine ⟨10421907648486184965917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1778672238674975567516501 10421907648486184965917)
              ·
                rfl

theorem cell23_1644024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 9].length) (baseStart_1644024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644024 prefixEnd_1644024 := by exact prefixLift 1644024
  have htrace : WordTrace (prefixWord ++ tailWord_1644024) baseStart_1644024 baseEnd_1644024 := by
    simpa [prefixWord, tailWord_1644024, baseEnd_1644024] using wordTrace_append hprefix tailTrace_1644024
  have hstable : (prefixWord ++ tailWord_1644024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644024).length < 2 ^ (prefixWord ++ tailWord_1644024).sum := by decide
  have hdescent : baseEnd_1644024 < baseStart_1644024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644052 : List Nat := [2, 4, 3, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_1644052 : Nat := 118140960795 + 1644052 * 2 ^ 59
def prefixEnd_1644052 : Nat := 4983230072969 + 3 ^ 40 * 1644052 * 2
def baseEnd_1644052 : Nat := 844188896985706872689149

theorem tailTrace_1644052 : CollatzResearch.WordTrace tailWord_1644052 prefixEnd_1644052 844188896985706872689149 := by
  unfold tailWord_1644052
  simp only [CollatzResearch.WordTrace]
  refine ⟨29981751319943930286267205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39975668426591907048356273 29981751319943930286267205)
  ·
    refine ⟨5621578372489486928675101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29981751319943930286267205 5621578372489486928675101)
    ·
      refine ⟨2108091889683557598253163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5621578372489486928675101 2108091889683557598253163)
      ·
        refine ⟨3162137834525336397379745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2108091889683557598253163 3162137834525336397379745)
        ·
          refine ⟨2371603375894002298034809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3162137834525336397379745 2371603375894002298034809)
          ·
            refine ⟨1778702531920501723526107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2371603375894002298034809 1778702531920501723526107)
            ·
              refine ⟨2668053797880752585289161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1778702531920501723526107 2668053797880752585289161)
              ·
                refine ⟨2001040348410564438966871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2668053797880752585289161 2001040348410564438966871)
                ·
                  refine ⟨3001560522615846658450307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001040348410564438966871 3001560522615846658450307)
                  ·
                    refine ⟨4502340783923769987675461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3001560522615846658450307 4502340783923769987675461)
                    ·
                      refine ⟨844188896985706872689149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4502340783923769987675461 844188896985706872689149)
                      ·
                        rfl

theorem cell23_1644052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_1644052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644052 prefixEnd_1644052 := by exact prefixLift 1644052
  have htrace : WordTrace (prefixWord ++ tailWord_1644052) baseStart_1644052 baseEnd_1644052 := by
    simpa [prefixWord, tailWord_1644052, baseEnd_1644052] using wordTrace_append hprefix tailTrace_1644052
  have hstable : (prefixWord ++ tailWord_1644052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644052).length < 2 ^ (prefixWord ++ tailWord_1644052).sum := by decide
  have hdescent : baseEnd_1644052 < baseStart_1644052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644062 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1644062 : Nat := 118140960795 + 1644062 * 2 ^ 59
def prefixEnd_1644062 : Nat := 4983230072969 + 3 ^ 40 * 1644062 * 2
def baseEnd_1644062 : Nat := 281398010597417277854701

theorem tailTrace_1644062 : CollatzResearch.WordTrace tailWord_1644062 prefixEnd_1644062 281398010597417277854701 := by
  unfold tailWord_1644062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7495483421231454035049805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39975911579901088186932293 7495483421231454035049805)
  ·
    refine ⟨2810806282961795263143677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7495483421231454035049805 2810806282961795263143677)
    ·
      refine ⟨1054052356110673223678879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2810806282961795263143677 1054052356110673223678879)
      ·
        refine ⟨1581078534166009835518319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054052356110673223678879 1581078534166009835518319)
        ·
          refine ⟨2371617801249014753277479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581078534166009835518319 2371617801249014753277479)
          ·
            refine ⟨3557426701873522129916219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2371617801249014753277479 3557426701873522129916219)
            ·
              refine ⟨5336140052810283194874329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3557426701873522129916219 5336140052810283194874329)
              ·
                refine ⟨4002105039607712396155747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5336140052810283194874329 4002105039607712396155747)
                ·
                  refine ⟨6003157559411568594233621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4002105039607712396155747 6003157559411568594233621)
                  ·
                    refine ⟨281398010597417277854701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6003157559411568594233621 281398010597417277854701)
                    ·
                      rfl

theorem cell23_1644062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1644062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644062 prefixEnd_1644062 := by exact prefixLift 1644062
  have htrace : WordTrace (prefixWord ++ tailWord_1644062) baseStart_1644062 baseEnd_1644062 := by
    simpa [prefixWord, tailWord_1644062, baseEnd_1644062] using wordTrace_append hprefix tailTrace_1644062
  have hstable : (prefixWord ++ tailWord_1644062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644062).length < 2 ^ (prefixWord ++ tailWord_1644062).sum := by decide
  have hdescent : baseEnd_1644062 < baseStart_1644062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644072 : List Nat := [2, 1, 5, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_1644072 : Nat := 118140960795 + 1644072 * 2 ^ 59
def prefixEnd_1644072 : Nat := 4983230072969 + 3 ^ 40 * 1644072 * 2
def baseEnd_1644072 : Nat := 844199166598796794439057

theorem tailTrace_1644072 : CollatzResearch.WordTrace tailWord_1644072 prefixEnd_1644072 844199166598796794439057 := by
  unfold tailWord_1644072
  simp only [CollatzResearch.WordTrace]
  refine ⟨29982116049907701994131235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39976154733210269325508313 29982116049907701994131235)
  ·
    refine ⟨44973174074861552991196853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29982116049907701994131235 44973174074861552991196853)
    ·
      refine ⟨4216235069518270592924705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44973174074861552991196853 4216235069518270592924705)
      ·
        refine ⟨3162176302138702944693529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4216235069518270592924705 3162176302138702944693529)
        ·
          refine ⟨2371632226604027208520147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3162176302138702944693529 2371632226604027208520147)
          ·
            refine ⟨3557448339906040812780221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2371632226604027208520147 3557448339906040812780221)
            ·
              refine ⟨1334043127464765304792583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3557448339906040812780221 1334043127464765304792583)
              ·
                refine ⟨2001064691197147957188875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334043127464765304792583 2001064691197147957188875)
                ·
                  refine ⟨3001597036795721935783313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2001064691197147957188875 3001597036795721935783313)
                  ·
                    refine ⟨2251197777596791451837485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3001597036795721935783313 2251197777596791451837485)
                    ·
                      refine ⟨844199166598796794439057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2251197777596791451837485 844199166598796794439057)
                      ·
                        rfl

theorem cell23_1644072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_1644072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644072 prefixEnd_1644072 := by exact prefixLift 1644072
  have htrace : WordTrace (prefixWord ++ tailWord_1644072) baseStart_1644072 baseEnd_1644072 := by
    simpa [prefixWord, tailWord_1644072, baseEnd_1644072] using wordTrace_append hprefix tailTrace_1644072
  have hstable : (prefixWord ++ tailWord_1644072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644072).length < 2 ^ (prefixWord ++ tailWord_1644072).sum := by decide
  have hdescent : baseEnd_1644072 < baseStart_1644072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644085 : List Nat := [1, 3, 3, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_1644085 : Nat := 118140960795 + 1644085 * 2 ^ 59
def prefixEnd_1644085 : Nat := 4983230072969 + 3 ^ 40 * 1644085 * 2
def baseEnd_1644085 : Nat := 844205841847305243576497

theorem tailTrace_1644085 : CollatzResearch.WordTrace tailWord_1644085 prefixEnd_1644085 844205841847305243576497 := by
  unfold tailWord_1644085
  simp only [CollatzResearch.WordTrace]
  refine ⟨59964706248768307208485709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39976470832512204805657139 59964706248768307208485709)
  ·
    refine ⟨22486764843288115203182141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59964706248768307208485709 22486764843288115203182141)
    ·
      refine ⟨8432536816233043201193303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22486764843288115203182141 8432536816233043201193303)
      ·
        refine ⟨12648805224349564801789955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8432536816233043201193303 12648805224349564801789955)
        ·
          refine ⟨18973207836524347202684933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12648805224349564801789955 18973207836524347202684933)
          ·
            refine ⟨3557476469348315100503425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18973207836524347202684933 3557476469348315100503425)
            ·
              refine ⟨2668107352011236325377569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3557476469348315100503425 2668107352011236325377569)
              ·
                refine ⟨2001080514008427244033177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2668107352011236325377569 2001080514008427244033177)
                ·
                  refine ⟨1500810385506320433024883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2001080514008427244033177 1500810385506320433024883)
                  ·
                    refine ⟨2251215578259480649537325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1500810385506320433024883 2251215578259480649537325)
                    ·
                      refine ⟨844205841847305243576497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2251215578259480649537325 844205841847305243576497)
                      ·
                        rfl

theorem cell23_1644085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_1644085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644085 prefixEnd_1644085 := by exact prefixLift 1644085
  have htrace : WordTrace (prefixWord ++ tailWord_1644085) baseStart_1644085 baseEnd_1644085 := by
    simpa [prefixWord, tailWord_1644085, baseEnd_1644085] using wordTrace_append hprefix tailTrace_1644085
  have hstable : (prefixWord ++ tailWord_1644085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644085).length < 2 ^ (prefixWord ++ tailWord_1644085).sum := by decide
  have hdescent : baseEnd_1644085 < baseStart_1644085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644102 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_1644102 : Nat := 118140960795 + 1644102 * 2 ^ 59
def prefixEnd_1644102 : Nat := 4983230072969 + 3 ^ 40 * 1644102 * 2
def baseEnd_1644102 : Nat := 844214571018431677063919

theorem tailTrace_1644102 : CollatzResearch.WordTrace tailWord_1644102 prefixEnd_1644102 844214571018431677063919 := by
  unfold tailWord_1644102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1873916446553334972245455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39976884193137812741236373 1873916446553334972245455)
  ·
    refine ⟨2810874669830002458368183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1873916446553334972245455 2810874669830002458368183)
    ·
      refine ⟨4216312004745003687552275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2810874669830002458368183 4216312004745003687552275)
      ·
        refine ⟨6324468007117505531328413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4216312004745003687552275 6324468007117505531328413)
        ·
          refine ⟨2371675502669064574248155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6324468007117505531328413 2371675502669064574248155)
          ·
            refine ⟨3557513254003596861372233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2371675502669064574248155 3557513254003596861372233)
            ·
              refine ⟨2668134940502697646029175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3557513254003596861372233 2668134940502697646029175)
              ·
                refine ⟨4002202410754046469043763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2668134940502697646029175 4002202410754046469043763)
                ·
                  refine ⟨6003303616131069703565645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4002202410754046469043763 6003303616131069703565645)
                  ·
                    refine ⟨2251238856049151138837117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6003303616131069703565645 2251238856049151138837117)
                    ·
                      refine ⟨844214571018431677063919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2251238856049151138837117 844214571018431677063919)
                      ·
                        rfl

theorem cell23_1644102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_1644102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644102 prefixEnd_1644102 := by exact prefixLift 1644102
  have htrace : WordTrace (prefixWord ++ tailWord_1644102) baseStart_1644102 baseEnd_1644102 := by
    simpa [prefixWord, tailWord_1644102, baseEnd_1644102] using wordTrace_append hprefix tailTrace_1644102
  have hstable : (prefixWord ++ tailWord_1644102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644102).length < 2 ^ (prefixWord ++ tailWord_1644102).sum := by decide
  have hdescent : baseEnd_1644102 < baseStart_1644102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1644108 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 1, 4, 2]
def baseStart_1644108 : Nat := 118140960795 + 1644108 * 2 ^ 59
def prefixEnd_1644108 : Nat := 4983230072969 + 3 ^ 40 * 1644108 * 2
def baseEnd_1644108 : Nat := 844217651902358653588891

theorem tailTrace_1644108 : CollatzResearch.WordTrace tailWord_1644108 prefixEnd_1644108 844217651902358653588891 := by
  unfold tailWord_1644108
  simp only [CollatzResearch.WordTrace]
  refine ⟨29982772563842491068286489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39977030085123321424381985 29982772563842491068286489)
  ·
    refine ⟨22487079422881868301214867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29982772563842491068286489 22487079422881868301214867)
    ·
      refine ⟨33730619134322802451822301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22487079422881868301214867 33730619134322802451822301)
      ·
        refine ⟨12648982175371050919433363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33730619134322802451822301 12648982175371050919433363)
        ·
          refine ⟨18973473263056576379150045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12648982175371050919433363 18973473263056576379150045)
          ·
            refine ⟨7115052473646216142181267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18973473263056576379150045 7115052473646216142181267)
            ·
              refine ⟨10672578710469324213271901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7115052473646216142181267 10672578710469324213271901)
              ·
                refine ⟨4002217016425996579976963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10672578710469324213271901 4002217016425996579976963)
                ·
                  refine ⟨6003325524638994869965445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4002217016425996579976963 6003325524638994869965445)
                  ·
                    refine ⟨1125623535869811538118521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6003325524638994869965445 1125623535869811538118521)
                    ·
                      refine ⟨844217651902358653588891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1125623535869811538118521 844217651902358653588891)
                      ·
                        rfl

theorem cell23_1644108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_1644108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1644108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1644108 prefixEnd_1644108 := by exact prefixLift 1644108
  have htrace : WordTrace (prefixWord ++ tailWord_1644108) baseStart_1644108 baseEnd_1644108 := by
    simpa [prefixWord, tailWord_1644108, baseEnd_1644108] using wordTrace_append hprefix tailTrace_1644108
  have hstable : (prefixWord ++ tailWord_1644108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1644108).length < 2 ^ (prefixWord ++ tailWord_1644108).sum := by decide
  have hdescent : baseEnd_1644108 < baseStart_1644108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1644108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
