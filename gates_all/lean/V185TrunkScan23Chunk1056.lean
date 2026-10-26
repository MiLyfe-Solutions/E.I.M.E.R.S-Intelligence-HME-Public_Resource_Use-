import V185TrunkScan23Chunk1055

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6251927 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 5, 4, 2]
def baseStart_6251927 : Nat := 118140960795 + 6251927 * 2 ^ 59
def prefixEnd_6251927 : Nat := 4983230072969 + 3 ^ 40 * 6251927 * 2
def baseEnd_6251927 : Nat := 3210243567821866040560417

theorem tailTrace_6251927 : CollatzResearch.WordTrace tailWord_6251927 prefixEnd_6251927 3210243567821866040560417 := by
  unfold tailWord_6251927
  simp only [CollatzResearch.WordTrace]
  refine ⟨228026510821343697969258035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152017673880895798646172023 228026510821343697969258035)
  ·
    refine ⟨342039766232015546953887053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228026510821343697969258035 342039766232015546953887053)
    ·
      refine ⟨128264912337005830107707645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342039766232015546953887053 128264912337005830107707645)
      ·
        refine ⟨48099342126377186290390367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128264912337005830107707645 48099342126377186290390367)
        ·
          refine ⟨72149013189565779435585551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48099342126377186290390367 72149013189565779435585551)
          ·
            refine ⟨108223519784348669153378327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72149013189565779435585551 108223519784348669153378327)
            ·
              refine ⟨162335279676523003730067491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108223519784348669153378327 162335279676523003730067491)
              ·
                refine ⟨243502919514784505595101237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162335279676523003730067491 243502919514784505595101237)
                ·
                  refine ⟨22828398704511047399540741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243502919514784505595101237 22828398704511047399540741)
                  ·
                    refine ⟨4280324757095821387413889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22828398704511047399540741 4280324757095821387413889)
                    ·
                      refine ⟨3210243567821866040560417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4280324757095821387413889 3210243567821866040560417)
                      ·
                        rfl

theorem cell23_6251927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_6251927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251927 prefixEnd_6251927 := by exact prefixLift 6251927
  have htrace : WordTrace (prefixWord ++ tailWord_6251927) baseStart_6251927 baseEnd_6251927 := by
    simpa [prefixWord, tailWord_6251927, baseEnd_6251927] using wordTrace_append hprefix tailTrace_6251927
  have hstable : (prefixWord ++ tailWord_6251927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251927).length < 2 ^ (prefixWord ++ tailWord_6251927).sum := by decide
  have hdescent : baseEnd_6251927 < baseStart_6251927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251978 : List Nat := [3, 1, 2, 1, 2, 5, 1, 2, 2, 2, 2]
def baseStart_6251978 : Nat := 118140960795 + 6251978 * 2 ^ 59
def prefixEnd_6251978 : Nat := 4983230072969 + 3 ^ 40 * 6251978 * 2
def baseEnd_6251978 : Nat := 3210269755335245341022683

theorem tailTrace_6251978 : CollatzResearch.WordTrace tailWord_6251978 prefixEnd_6251978 3210269755335245341022683 := by
  unfold tailWord_6251978
  simp only [CollatzResearch.WordTrace]
  refine ⟨57007092736039733419841147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152018913962772622452909725 57007092736039733419841147)
  ·
    refine ⟨85510639104059600129761721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57007092736039733419841147 85510639104059600129761721)
    ·
      refine ⟨64132979328044700097321291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85510639104059600129761721 64132979328044700097321291)
      ·
        refine ⟨96199468992067050145981937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64132979328044700097321291 96199468992067050145981937)
        ·
          refine ⟨72149601744050287609486453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96199468992067050145981937 72149601744050287609486453)
          ·
            refine ⟨6764025163504714463389355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72149601744050287609486453 6764025163504714463389355)
            ·
              refine ⟨10146037745257071695084033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6764025163504714463389355 10146037745257071695084033)
              ·
                refine ⟨7609528308942803771313025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10146037745257071695084033 7609528308942803771313025)
                ·
                  refine ⟨5707146231707102828484769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7609528308942803771313025 5707146231707102828484769)
                  ·
                    refine ⟨4280359673780327121363577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5707146231707102828484769 4280359673780327121363577)
                    ·
                      refine ⟨3210269755335245341022683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4280359673780327121363577 3210269755335245341022683)
                      ·
                        rfl

theorem cell23_6251978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_6251978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251978 prefixEnd_6251978 := by exact prefixLift 6251978
  have htrace : WordTrace (prefixWord ++ tailWord_6251978) baseStart_6251978 baseEnd_6251978 := by
    simpa [prefixWord, tailWord_6251978, baseEnd_6251978] using wordTrace_append hprefix tailTrace_6251978
  have hstable : (prefixWord ++ tailWord_6251978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251978).length < 2 ^ (prefixWord ++ tailWord_6251978).sum := by decide
  have hdescent : baseEnd_6251978 < baseStart_6251978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6251997 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_6251997 : Nat := 118140960795 + 6251997 * 2 ^ 59
def prefixEnd_6251997 : Nat := 4983230072969 + 3 ^ 40 * 6251997 * 2
def baseEnd_6251997 : Nat := 1070093170489226922228365

theorem tailTrace_6251997 : CollatzResearch.WordTrace tailWord_6251997 prefixEnd_6251997 1070093170489226922228365 := by
  unfold tailWord_6251997
  simp only [CollatzResearch.WordTrace]
  refine ⟨228029063931090099924306245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152019375954060066616204163 228029063931090099924306245)
  ·
    refine ⟨42755449487079393735807421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228029063931090099924306245 42755449487079393735807421)
    ·
      refine ⟨16033293557654772650927783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42755449487079393735807421 16033293557654772650927783)
      ·
        refine ⟨24049940336482158976391675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16033293557654772650927783 24049940336482158976391675)
        ·
          refine ⟨36074910504723238464587513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24049940336482158976391675 36074910504723238464587513)
          ·
            refine ⟨27056182878542428848440635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36074910504723238464587513 27056182878542428848440635)
            ·
              refine ⟨40584274317813643272660953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27056182878542428848440635 40584274317813643272660953)
              ·
                refine ⟨30438205738360232454495715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40584274317813643272660953 30438205738360232454495715)
                ·
                  refine ⟨45657308607540348681743573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30438205738360232454495715 45657308607540348681743573)
                  ·
                    refine ⟨1070093170489226922228365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45657308607540348681743573 1070093170489226922228365)
                    ·
                      rfl

theorem cell23_6251997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_6251997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6251997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6251997 prefixEnd_6251997 := by exact prefixLift 6251997
  have htrace : WordTrace (prefixWord ++ tailWord_6251997) baseStart_6251997 baseEnd_6251997 := by
    simpa [prefixWord, tailWord_6251997, baseEnd_6251997] using wordTrace_append hprefix tailTrace_6251997
  have hstable : (prefixWord ++ tailWord_6251997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6251997).length < 2 ^ (prefixWord ++ tailWord_6251997).sum := by decide
  have hdescent : baseEnd_6251997 < baseStart_6251997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6251997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252017 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_6252017 : Nat := 118140960795 + 6252017 * 2 ^ 59
def prefixEnd_6252017 : Nat := 4983230072969 + 3 ^ 40 * 6252017 * 2
def baseEnd_6252017 : Nat := 3210289781080770688435003

theorem tailTrace_6252017 : CollatzResearch.WordTrace tailWord_6252017 prefixEnd_6252017 3210289781080770688435003 := by
  unfold tailWord_6252017
  simp only [CollatzResearch.WordTrace]
  refine ⟨228029793391017643340034305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152019862260678428893356203 228029793391017643340034305)
  ·
    refine ⟨171022345043263232505025729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228029793391017643340034305 171022345043263232505025729)
    ·
      refine ⟨128266758782447424378769297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171022345043263232505025729 128266758782447424378769297)
      ·
        refine ⟨96200069086835568284076973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128266758782447424378769297 96200069086835568284076973)
        ·
          refine ⟨36075025907563338106528865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96200069086835568284076973 36075025907563338106528865)
          ·
            refine ⟨27056269430672503579896649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36075025907563338106528865 27056269430672503579896649)
            ·
              refine ⟨20292202073004377684922487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27056269430672503579896649 20292202073004377684922487)
              ·
                refine ⟨30438303109506566527383731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20292202073004377684922487 30438303109506566527383731)
                ·
                  refine ⟨45657454664259849791075597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30438303109506566527383731 45657454664259849791075597)
                  ·
                    refine ⟨17121545499097443671653349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45657454664259849791075597 17121545499097443671653349)
                    ·
                      refine ⟨3210289781080770688435003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17121545499097443671653349 3210289781080770688435003)
                      ·
                        rfl

theorem cell23_6252017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_6252017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252017 prefixEnd_6252017 := by exact prefixLift 6252017
  have htrace : WordTrace (prefixWord ++ tailWord_6252017) baseStart_6252017 baseEnd_6252017 := by
    simpa [prefixWord, tailWord_6252017, baseEnd_6252017] using wordTrace_append hprefix tailTrace_6252017
  have hstable : (prefixWord ++ tailWord_6252017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252017).length < 2 ^ (prefixWord ++ tailWord_6252017).sum := by decide
  have hdescent : baseEnd_6252017 < baseStart_6252017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252138 : List Nat := [3, 1, 3, 2, 1, 4, 2, 1, 1, 5]
def baseStart_6252138 : Nat := 118140960795 + 6252138 * 2 ^ 59
def prefixEnd_6252138 : Nat := 4983230072969 + 3 ^ 40 * 6252138 * 2
def baseEnd_6252138 : Nat := 1070117304079988238340649

theorem tailTrace_6252138 : CollatzResearch.WordTrace tailWord_6252138 prefixEnd_6252138 1070117304079988238340649 := by
  unfold tailWord_6252138
  simp only [CollatzResearch.WordTrace]
  refine ⟨57008551655894820251297267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152022804415719520670126045 57008551655894820251297267)
  ·
    refine ⟨85512827483842230376945901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57008551655894820251297267 85512827483842230376945901)
    ·
      refine ⟨32067310306440836391354713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85512827483842230376945901 32067310306440836391354713)
      ·
        refine ⟨24050482729830627293516035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32067310306440836391354713 24050482729830627293516035)
        ·
          refine ⟨36075724094745940940274053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24050482729830627293516035 36075724094745940940274053)
          ·
            refine ⟨6764198267764863926301385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36075724094745940940274053 6764198267764863926301385)
            ·
              refine ⟨5073148700823647944726039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6764198267764863926301385 5073148700823647944726039)
              ·
                refine ⟨7609723051235471917089059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5073148700823647944726039 7609723051235471917089059)
                ·
                  refine ⟨11414584576853207875633589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7609723051235471917089059 11414584576853207875633589)
                  ·
                    refine ⟨1070117304079988238340649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11414584576853207875633589 1070117304079988238340649)
                    ·
                      rfl

theorem cell23_6252138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_6252138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252138 prefixEnd_6252138 := by exact prefixLift 6252138
  have htrace : WordTrace (prefixWord ++ tailWord_6252138) baseStart_6252138 baseEnd_6252138 := by
    simpa [prefixWord, tailWord_6252138, baseEnd_6252138] using wordTrace_append hprefix tailTrace_6252138
  have hstable : (prefixWord ++ tailWord_6252138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252138).length < 2 ^ (prefixWord ++ tailWord_6252138).sum := by decide
  have hdescent : baseEnd_6252138 < baseStart_6252138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252168 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 1, 6]
def baseStart_6252168 : Nat := 118140960795 + 6252168 * 2 ^ 59
def prefixEnd_6252168 : Nat := 4983230072969 + 3 ^ 40 * 6252168 * 2
def baseEnd_6252168 : Nat := 1070122438886533199215603

theorem tailTrace_6252168 : CollatzResearch.WordTrace tailWord_6252168 prefixEnd_6252168 1070122438886533199215603 := by
  unfold tailWord_6252168
  simp only [CollatzResearch.WordTrace]
  refine ⟨114017650406735298064390579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152023533875647064085854105 114017650406735298064390579)
  ·
    refine ⟨171026475610102947096585869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114017650406735298064390579 171026475610102947096585869)
    ·
      refine ⟨64134928353788605161219701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171026475610102947096585869 64134928353788605161219701)
      ·
        refine ⟨6012649533167681733864347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64134928353788605161219701 6012649533167681733864347)
        ·
          refine ⟨9018974299751522600796521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6012649533167681733864347 9018974299751522600796521)
          ·
            refine ⟨6764230724813641950597391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9018974299751522600796521 6764230724813641950597391)
            ·
              refine ⟨10146346087220462925896087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6764230724813641950597391 10146346087220462925896087)
              ·
                refine ⟨15219519130830694388844131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10146346087220462925896087 15219519130830694388844131)
                ·
                  refine ⟨22829278696246041583266197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15219519130830694388844131 22829278696246041583266197)
                  ·
                    refine ⟨1070122438886533199215603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22829278696246041583266197 1070122438886533199215603)
                    ·
                      rfl

theorem cell23_6252168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_6252168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252168 prefixEnd_6252168 := by exact prefixLift 6252168
  have htrace : WordTrace (prefixWord ++ tailWord_6252168) baseStart_6252168 baseEnd_6252168 := by
    simpa [prefixWord, tailWord_6252168, baseEnd_6252168] using wordTrace_append hprefix tailTrace_6252168
  have hstable : (prefixWord ++ tailWord_6252168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252168).length < 2 ^ (prefixWord ++ tailWord_6252168).sum := by decide
  have hdescent : baseEnd_6252168 < baseStart_6252168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252192 : List Nat := [2, 1, 1, 4, 3, 3, 1, 3, 1, 2, 2]
def baseStart_6252192 : Nat := 118140960795 + 6252192 * 2 ^ 59
def prefixEnd_6252192 : Nat := 4983230072969 + 3 ^ 40 * 6252192 * 2
def baseEnd_6252192 : Nat := 3210379640195307503746699

theorem tailTrace_6252192 : CollatzResearch.WordTrace tailWord_6252192 prefixEnd_6252192 3210379640195307503746699 := by
  unfold tailWord_6252192
  simp only [CollatzResearch.WordTrace]
  refine ⟨114018088082691824113827415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152024117443589098818436553 114018088082691824113827415)
  ·
    refine ⟨171027132124037736170741123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114018088082691824113827415 171027132124037736170741123)
    ·
      refine ⟨256540698186056604256111685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171027132124037736170741123 256540698186056604256111685)
      ·
        refine ⟨48101380909885613298020941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256540698186056604256111685 48101380909885613298020941)
        ·
          refine ⟨18038017841207104986757853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48101380909885613298020941 18038017841207104986757853)
          ·
            refine ⟨6764256690452664370034195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18038017841207104986757853 6764256690452664370034195)
            ·
              refine ⟨10146385035678996555051293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6764256690452664370034195 10146385035678996555051293)
              ·
                refine ⟨3804894388379623708144235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10146385035678996555051293 3804894388379623708144235)
                ·
                  refine ⟨5707341582569435562216353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3804894388379623708144235 5707341582569435562216353)
                  ·
                    refine ⟨4280506186927076671662265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5707341582569435562216353 4280506186927076671662265)
                    ·
                      refine ⟨3210379640195307503746699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4280506186927076671662265 3210379640195307503746699)
                      ·
                        rfl

theorem cell23_6252192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_6252192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252192 prefixEnd_6252192 := by exact prefixLift 6252192
  have htrace : WordTrace (prefixWord ++ tailWord_6252192) baseStart_6252192 baseEnd_6252192 := by
    simpa [prefixWord, tailWord_6252192, baseEnd_6252192] using wordTrace_append hprefix tailTrace_6252192
  have hstable : (prefixWord ++ tailWord_6252192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252192).length < 2 ^ (prefixWord ++ tailWord_6252192).sum := by decide
  have hdescent : baseEnd_6252192 < baseStart_6252192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252227 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 6]
def baseStart_6252227 : Nat := 118140960795 + 6252227 * 2 ^ 59
def prefixEnd_6252227 : Nat := 4983230072969 + 3 ^ 40 * 6252227 * 2
def baseEnd_6252227 : Nat := 3210397612018214866809037

theorem tailTrace_6252227 : CollatzResearch.WordTrace tailWord_6252227 prefixEnd_6252227 3210397612018214866809037 := by
  unfold tailWord_6252227
  simp only [CollatzResearch.WordTrace]
  refine ⟨228037452720256849205178935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152024968480171232803452623 228037452720256849205178935)
  ·
    refine ⟨342056179080385273807768403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228037452720256849205178935 342056179080385273807768403)
    ·
      refine ⟨513084268620577910711652605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342056179080385273807768403 513084268620577910711652605)
      ·
        refine ⟨192406600732716716516869727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 513084268620577910711652605 192406600732716716516869727)
        ·
          refine ⟨288609901099075074775304591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192406600732716716516869727 288609901099075074775304591)
          ·
            refine ⟨432914851648612612162956887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288609901099075074775304591 432914851648612612162956887)
            ·
              refine ⟨649372277472918918244435331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432914851648612612162956887 649372277472918918244435331)
              ·
                refine ⟨974058416209378377366652997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649372277472918918244435331 974058416209378377366652997)
                ·
                  refine ⟨182635953039258445756247437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 974058416209378377366652997 182635953039258445756247437)
                  ·
                    refine ⟨68488482389721917158592789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 182635953039258445756247437 68488482389721917158592789)
                    ·
                      refine ⟨3210397612018214866809037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68488482389721917158592789 3210397612018214866809037)
                      ·
                        rfl

theorem cell23_6252227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_6252227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252227 prefixEnd_6252227 := by exact prefixLift 6252227
  have htrace : WordTrace (prefixWord ++ tailWord_6252227) baseStart_6252227 baseEnd_6252227 := by
    simpa [prefixWord, tailWord_6252227, baseEnd_6252227] using wordTrace_append hprefix tailTrace_6252227
  have hstable : (prefixWord ++ tailWord_6252227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252227).length < 2 ^ (prefixWord ++ tailWord_6252227).sum := by decide
  have hdescent : baseEnd_6252227 < baseStart_6252227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252231 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 1, 4, 2]
def baseStart_6252231 : Nat := 118140960795 + 6252231 * 2 ^ 59
def prefixEnd_6252231 : Nat := 4983230072969 + 3 ^ 40 * 6252231 * 2
def baseEnd_6252231 : Nat := 3210399665940832851159019

theorem tailTrace_6252231 : CollatzResearch.WordTrace tailWord_6252231 prefixEnd_6252231 3210399665940832851159019 := by
  unfold tailWord_6252231
  simp only [CollatzResearch.WordTrace]
  refine ⟨228037598612242357888324547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152025065741494905258883031 228037598612242357888324547)
  ·
    refine ⟨342056397918363536832486821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228037598612242357888324547 342056397918363536832486821)
    ·
      refine ⟨64135574609693163156091279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 342056397918363536832486821 64135574609693163156091279)
      ·
        refine ⟨96203361914539744734136919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64135574609693163156091279 96203361914539744734136919)
        ·
          refine ⟨144305042871809617101205379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96203361914539744734136919 144305042871809617101205379)
          ·
            refine ⟨216457564307714425651808069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144305042871809617101205379 216457564307714425651808069)
            ·
              refine ⟨40585793307696454809714013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216457564307714425651808069 40585793307696454809714013)
              ·
                refine ⟨15219672490386170553642755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40585793307696454809714013 15219672490386170553642755)
                ·
                  refine ⟨22829508735579255830464133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15219672490386170553642755 22829508735579255830464133)
                  ·
                    refine ⟨4280532887921110468212025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22829508735579255830464133 4280532887921110468212025)
                    ·
                      refine ⟨3210399665940832851159019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4280532887921110468212025 3210399665940832851159019)
                      ·
                        rfl

theorem cell23_6252231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_6252231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252231 prefixEnd_6252231 := by exact prefixLift 6252231
  have htrace : WordTrace (prefixWord ++ tailWord_6252231) baseStart_6252231 baseEnd_6252231 := by
    simpa [prefixWord, tailWord_6252231, baseEnd_6252231] using wordTrace_append hprefix tailTrace_6252231
  have hstable : (prefixWord ++ tailWord_6252231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252231).length < 2 ^ (prefixWord ++ tailWord_6252231).sum := by decide
  have hdescent : baseEnd_6252231 < baseStart_6252231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252271 : List Nat := [1, 1, 2, 1, 5, 1, 3, 4, 5]
def baseStart_6252271 : Nat := 118140960795 + 6252271 * 2 ^ 59
def prefixEnd_6252271 : Nat := 4983230072969 + 3 ^ 40 * 6252271 * 2
def baseEnd_6252271 : Nat := 356713356129668077184315

theorem tailTrace_6252271 : CollatzResearch.WordTrace tailWord_6252271 prefixEnd_6252271 356713356129668077184315 := by
  unfold tailWord_6252271
  simp only [CollatzResearch.WordTrace]
  refine ⟨228039057532097444719780667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152026038354731629813187111 228039057532097444719780667)
  ·
    refine ⟨342058586298146167079671001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228039057532097444719780667 342058586298146167079671001)
    ·
      refine ⟨256543939723609625309753251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342058586298146167079671001 256543939723609625309753251)
      ·
        refine ⟨384815909585414437964629877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256543939723609625309753251 384815909585414437964629877)
        ·
          refine ⟨36076491523632603559184051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 384815909585414437964629877 36076491523632603559184051)
          ·
            refine ⟨54114737285448905338776077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36076491523632603559184051 54114737285448905338776077)
            ·
              refine ⟨20293026482043339502041029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54114737285448905338776077 20293026482043339502041029)
              ·
                refine ⟨3804942465383126156632693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20293026482043339502041029 3804942465383126156632693)
                ·
                  refine ⟨356713356129668077184315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3804942465383126156632693 356713356129668077184315)
                  ·
                    rfl

theorem cell23_6252271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 5].length) (baseStart_6252271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252271 prefixEnd_6252271 := by exact prefixLift 6252271
  have htrace : WordTrace (prefixWord ++ tailWord_6252271) baseStart_6252271 baseEnd_6252271 := by
    simpa [prefixWord, tailWord_6252271, baseEnd_6252271] using wordTrace_append hprefix tailTrace_6252271
  have hstable : (prefixWord ++ tailWord_6252271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252271).length < 2 ^ (prefixWord ++ tailWord_6252271).sum := by decide
  have hdescent : baseEnd_6252271 < baseStart_6252271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252284 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 1, 7]
def baseStart_6252284 : Nat := 118140960795 + 6252284 * 2 ^ 59
def prefixEnd_6252284 : Nat := 4983230072969 + 3 ^ 40 * 6252284 * 2
def baseEnd_6252284 : Nat := 1070142293471840381265425

theorem tailTrace_6252284 : CollatzResearch.WordTrace tailWord_6252284 prefixEnd_6252284 1070142293471840381265425 := by
  unfold tailWord_6252284
  simp only [CollatzResearch.WordTrace]
  refine ⟨114019765840525173970001953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152026354454033565293335937 114019765840525173970001953)
  ·
    refine ⟨85514824380393880477501465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114019765840525173970001953 85514824380393880477501465)
    ·
      refine ⟨64136118285295410358126099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85514824380393880477501465 64136118285295410358126099)
      ·
        refine ⟨96204177427943115537189149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64136118285295410358126099 96204177427943115537189149)
        ·
          refine ⟨36076566535478668326445931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96204177427943115537189149 36076566535478668326445931)
          ·
            refine ⟨54114849803218002489668897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36076566535478668326445931 54114849803218002489668897)
            ·
              refine ⟨40586137352413501867251673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54114849803218002489668897 40586137352413501867251673)
              ·
                refine ⟨30439603014310126400438755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40586137352413501867251673 30439603014310126400438755)
                ·
                  refine ⟨45659404521465189600658133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30439603014310126400438755 45659404521465189600658133)
                  ·
                    refine ⟨1070142293471840381265425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45659404521465189600658133 1070142293471840381265425)
                    ·
                      rfl

theorem cell23_6252284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_6252284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252284 prefixEnd_6252284 := by exact prefixLift 6252284
  have htrace : WordTrace (prefixWord ++ tailWord_6252284) baseStart_6252284 baseEnd_6252284 := by
    simpa [prefixWord, tailWord_6252284, baseEnd_6252284] using wordTrace_append hprefix tailTrace_6252284
  have hstable : (prefixWord ++ tailWord_6252284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252284).length < 2 ^ (prefixWord ++ tailWord_6252284).sum := by decide
  have hdescent : baseEnd_6252284 < baseStart_6252284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252338 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2]
def baseStart_6252338 : Nat := 118140960795 + 6252338 * 2 ^ 59
def prefixEnd_6252338 : Nat := 4983230072969 + 3 ^ 40 * 6252338 * 2
def baseEnd_6252338 : Nat := 3210454608370863932521027

theorem tailTrace_6252338 : CollatzResearch.WordTrace tailWord_6252338 prefixEnd_6252338 3210454608370863932521027 := by
  unfold tailWord_6252338
  simp only [CollatzResearch.WordTrace]
  refine ⟨57010375305713678790617417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152027667481903143441646445 57010375305713678790617417)
  ·
    refine ⟨42757781479285259092963063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57010375305713678790617417 42757781479285259092963063)
    ·
      refine ⟨64136672218927888639444595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42757781479285259092963063 64136672218927888639444595)
      ·
        refine ⟨96205008328391832959166893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64136672218927888639444595 96205008328391832959166893)
        ·
          refine ⟨36076878123146937359687585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96205008328391832959166893 36076878123146937359687585)
          ·
            refine ⟨27057658592360203019765689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36076878123146937359687585 27057658592360203019765689)
            ·
              refine ⟨20293243944270152264824267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27057658592360203019765689 20293243944270152264824267)
              ·
                refine ⟨30439865916405228397236401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20293243944270152264824267 30439865916405228397236401)
                ·
                  refine ⟨22829899437303921297927301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30439865916405228397236401 22829899437303921297927301)
                  ·
                    refine ⟨4280606144494485243361369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22829899437303921297927301 4280606144494485243361369)
                    ·
                      refine ⟨3210454608370863932521027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4280606144494485243361369 3210454608370863932521027)
                      ·
                        rfl

theorem cell23_6252338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_6252338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252338 prefixEnd_6252338 := by exact prefixLift 6252338
  have htrace : WordTrace (prefixWord ++ tailWord_6252338) baseStart_6252338 baseEnd_6252338 := by
    simpa [prefixWord, tailWord_6252338, baseEnd_6252338] using wordTrace_append hprefix tailTrace_6252338
  have hstable : (prefixWord ++ tailWord_6252338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252338).length < 2 ^ (prefixWord ++ tailWord_6252338).sum := by decide
  have hdescent : baseEnd_6252338 < baseStart_6252338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252391 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 3, 5]
def baseStart_6252391 : Nat := 118140960795 + 6252391 * 2 ^ 59
def prefixEnd_6252391 : Nat := 4983230072969 + 3 ^ 40 * 6252391 * 2
def baseEnd_6252391 : Nat := 1070160607615184075052761

theorem tailTrace_6252391 : CollatzResearch.WordTrace tailWord_6252391 prefixEnd_6252391 1070160607615184075052761 := by
  unfold tailWord_6252391
  simp only [CollatzResearch.WordTrace]
  refine ⟨228043434291662705214149027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152028956194441803476099351 228043434291662705214149027)
  ·
    refine ⟨342065151437494057821223541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228043434291662705214149027 342065151437494057821223541)
    ·
      refine ⟨32068607947265067920739707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 342065151437494057821223541 32068607947265067920739707)
      ·
        refine ⟨48102911920897601881109561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32068607947265067920739707 48102911920897601881109561)
        ·
          refine ⟨36077183940673201410832171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48102911920897601881109561 36077183940673201410832171)
          ·
            refine ⟨54115775911009802116248257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36077183940673201410832171 54115775911009802116248257)
            ·
              refine ⟨40586831933257351587186193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54115775911009802116248257 40586831933257351587186193)
              ·
                refine ⟨30440123949943013690389645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40586831933257351587186193 30440123949943013690389645)
                ·
                  refine ⟨11415046481228630133896117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30440123949943013690389645 11415046481228630133896117)
                  ·
                    refine ⟨1070160607615184075052761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11415046481228630133896117 1070160607615184075052761)
                    ·
                      rfl

theorem cell23_6252391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_6252391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252391 prefixEnd_6252391 := by exact prefixLift 6252391
  have htrace : WordTrace (prefixWord ++ tailWord_6252391) baseStart_6252391 baseEnd_6252391 := by
    simpa [prefixWord, tailWord_6252391, baseEnd_6252391] using wordTrace_append hprefix tailTrace_6252391
  have hstable : (prefixWord ++ tailWord_6252391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252391).length < 2 ^ (prefixWord ++ tailWord_6252391).sum := by decide
  have hdescent : baseEnd_6252391 < baseStart_6252391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252421 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 1, 6]
def baseStart_6252421 : Nat := 118140960795 + 6252421 * 2 ^ 59
def prefixEnd_6252421 : Nat := 4983230072969 + 3 ^ 40 * 6252421 * 2
def baseEnd_6252421 : Nat := 1070165742421729035927715

theorem tailTrace_6252421 : CollatzResearch.WordTrace tailWord_6252421 prefixEnd_6252421 1070165742421729035927715 := by
  unfold tailWord_6252421
  simp only [CollatzResearch.WordTrace]
  refine ⟨228044528481554020337741117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152029685654369346891827411 228044528481554020337741117)
  ·
    refine ⟨85516698180582757626652919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228044528481554020337741117 85516698180582757626652919)
    ·
      refine ⟨128275047270874136439979379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85516698180582757626652919 128275047270874136439979379)
      ·
        refine ⟨192412570906311204659969069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128275047270874136439979379 192412570906311204659969069)
        ·
          refine ⟨72154714089866701747488401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192412570906311204659969069 72154714089866701747488401)
          ·
            refine ⟨54116035567400026310616301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72154714089866701747488401 54116035567400026310616301)
            ·
              refine ⟨20293513337775009866481113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54116035567400026310616301 20293513337775009866481113)
              ·
                refine ⟨15220135003331257399860835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20293513337775009866481113 15220135003331257399860835)
                ·
                  refine ⟨22830202504996886099791253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15220135003331257399860835 22830202504996886099791253)
                  ·
                    refine ⟨1070165742421729035927715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22830202504996886099791253 1070165742421729035927715)
                    ·
                      rfl

theorem cell23_6252421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_6252421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252421 prefixEnd_6252421 := by exact prefixLift 6252421
  have htrace : WordTrace (prefixWord ++ tailWord_6252421) baseStart_6252421 baseEnd_6252421 := by
    simpa [prefixWord, tailWord_6252421, baseEnd_6252421] using wordTrace_append hprefix tailTrace_6252421
  have hstable : (prefixWord ++ tailWord_6252421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252421).length < 2 ^ (prefixWord ++ tailWord_6252421).sum := by decide
  have hdescent : baseEnd_6252421 < baseStart_6252421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252439 : List Nat := [1, 1, 3, 3, 1, 5, 2, 2, 1, 1, 3]
def baseStart_6252439 : Nat := 118140960795 + 6252439 * 2 ^ 59
def prefixEnd_6252439 : Nat := 4983230072969 + 3 ^ 40 * 6252439 * 2
def baseEnd_6252439 : Nat := 3210506469916968037358063

theorem tailTrace_6252439 : CollatzResearch.WordTrace tailWord_6252439 prefixEnd_6252439 3210506469916968037358063 := by
  unfold tailWord_6252439
  simp only [CollatzResearch.WordTrace]
  refine ⟨228045184995488809411896371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152030123330325872941264247 228045184995488809411896371)
  ·
    refine ⟨342067777493233214117844557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228045184995488809411896371 342067777493233214117844557)
    ·
      refine ⟨128275416559962455294191709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342067777493233214117844557 128275416559962455294191709)
      ·
        refine ⟨48103281209985920735321891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128275416559962455294191709 48103281209985920735321891)
        ·
          refine ⟨72154921814978881102982837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48103281209985920735321891 72154921814978881102982837)
          ·
            refine ⟨6764523920154270103404641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72154921814978881102982837 6764523920154270103404641)
            ·
              refine ⟨5073392940115702577553481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6764523920154270103404641 5073392940115702577553481)
              ·
                refine ⟨3805044705086776933165111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5073392940115702577553481 3805044705086776933165111)
                ·
                  refine ⟨5707567057630165399747667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3805044705086776933165111 5707567057630165399747667)
                  ·
                    refine ⟨8561350586445248099621501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5707567057630165399747667 8561350586445248099621501)
                    ·
                      refine ⟨3210506469916968037358063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8561350586445248099621501 3210506469916968037358063)
                      ·
                        rfl

theorem cell23_6252439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_6252439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252439 prefixEnd_6252439 := by exact prefixLift 6252439
  have htrace : WordTrace (prefixWord ++ tailWord_6252439) baseStart_6252439 baseEnd_6252439 := by
    simpa [prefixWord, tailWord_6252439, baseEnd_6252439] using wordTrace_append hprefix tailTrace_6252439
  have hstable : (prefixWord ++ tailWord_6252439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252439).length < 2 ^ (prefixWord ++ tailWord_6252439).sum := by decide
  have hdescent : baseEnd_6252439 < baseStart_6252439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252455 : List Nat := [1, 1, 6, 1, 2, 1, 2, 3, 2, 4]
def baseStart_6252455 : Nat := 118140960795 + 6252455 * 2 ^ 59
def prefixEnd_6252455 : Nat := 4983230072969 + 3 ^ 40 * 6252455 * 2
def baseEnd_6252455 : Nat := 1070171561869146658252663

theorem tailTrace_6252455 : CollatzResearch.WordTrace tailWord_6252455 prefixEnd_6252455 1070171561869146658252663 := by
  unfold tailWord_6252455
  simp only [CollatzResearch.WordTrace]
  refine ⟨228045768563430844144478819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152030512375620562762985879 228045768563430844144478819)
  ·
    refine ⟨342068652845146266216718229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228045768563430844144478819 342068652845146266216718229)
    ·
      refine ⟨16034468102116231228908667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 342068652845146266216718229 16034468102116231228908667)
      ·
        refine ⟨24051702153174346843363001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16034468102116231228908667 24051702153174346843363001)
        ·
          refine ⟨18038776614880760132522251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24051702153174346843363001 18038776614880760132522251)
          ·
            refine ⟨27058164922321140198783377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18038776614880760132522251 27058164922321140198783377)
            ·
              refine ⟨20293623691740855149087533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27058164922321140198783377 20293623691740855149087533)
              ·
                refine ⟨7610108884402820680907825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20293623691740855149087533 7610108884402820680907825)
                ·
                  refine ⟨5707581663302115510680869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7610108884402820680907825 5707581663302115510680869)
                  ·
                    refine ⟨1070171561869146658252663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5707581663302115510680869 1070171561869146658252663)
                    ·
                      rfl

theorem cell23_6252455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_6252455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252455 prefixEnd_6252455 := by exact prefixLift 6252455
  have htrace : WordTrace (prefixWord ++ tailWord_6252455) baseStart_6252455 baseEnd_6252455 := by
    simpa [prefixWord, tailWord_6252455, baseEnd_6252455] using wordTrace_append hprefix tailTrace_6252455
  have hstable : (prefixWord ++ tailWord_6252455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252455).length < 2 ^ (prefixWord ++ tailWord_6252455).sum := by decide
  have hdescent : baseEnd_6252455 < baseStart_6252455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252522 : List Nat := [3, 1, 3, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_6252522 : Nat := 118140960795 + 6252522 * 2 ^ 59
def prefixEnd_6252522 : Nat := 4983230072969 + 3 ^ 40 * 6252522 * 2
def baseEnd_6252522 : Nat := 3210549088811291212620181

theorem tailTrace_6252522 : CollatzResearch.WordTrace tailWord_6252522 prefixEnd_6252522 3210549088811291212620181 := by
  unfold tailWord_6252522
  simp only [CollatzResearch.WordTrace]
  refine ⟨57012053063547028646791955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152032141502792076391445213 57012053063547028646791955)
  ·
    refine ⟨85518079595320542970187933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57012053063547028646791955 85518079595320542970187933)
    ·
      refine ⟨32069279848245203613820475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85518079595320542970187933 32069279848245203613820475)
      ·
        refine ⟨48103919772367805420730713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32069279848245203613820475 48103919772367805420730713)
        ·
          refine ⟨36077939829275854065548035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48103919772367805420730713 36077939829275854065548035)
          ·
            refine ⟨54116909743913781098322053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36077939829275854065548035 54116909743913781098322053)
            ·
              refine ⟨10146920576983833955935385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54116909743913781098322053 10146920576983833955935385)
              ·
                refine ⟨7610190432737875466951539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10146920576983833955935385 7610190432737875466951539)
                ·
                  refine ⟨11415285649106813200427309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7610190432737875466951539 11415285649106813200427309)
                  ·
                    refine ⟨4280732118415054950160241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11415285649106813200427309 4280732118415054950160241)
                    ·
                      refine ⟨3210549088811291212620181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4280732118415054950160241 3210549088811291212620181)
                      ·
                        rfl

theorem cell23_6252522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_6252522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252522 prefixEnd_6252522 := by exact prefixLift 6252522
  have htrace : WordTrace (prefixWord ++ tailWord_6252522) baseStart_6252522 baseEnd_6252522 := by
    simpa [prefixWord, tailWord_6252522, baseEnd_6252522] using wordTrace_append hprefix tailTrace_6252522
  have hstable : (prefixWord ++ tailWord_6252522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252522).length < 2 ^ (prefixWord ++ tailWord_6252522).sum := by decide
  have hdescent : baseEnd_6252522 < baseStart_6252522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252531 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 4]
def baseStart_6252531 : Nat := 118140960795 + 6252531 * 2 ^ 59
def prefixEnd_6252531 : Nat := 4983230072969 + 3 ^ 40 * 6252531 * 2
def baseEnd_6252531 : Nat := 3210553710137181677407639

theorem tailTrace_6252531 : CollatzResearch.WordTrace tailWord_6252531 prefixEnd_6252531 3210553710137181677407639 := by
  unfold tailWord_6252531
  simp only [CollatzResearch.WordTrace]
  refine ⟨228048540511155509124245447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152032360340770339416163631 228048540511155509124245447)
  ·
    refine ⟨342072810766733263686368171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228048540511155509124245447 342072810766733263686368171)
    ·
      refine ⟨513109216150099895529552257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342072810766733263686368171 513109216150099895529552257)
      ·
        refine ⟨384831912112574921647164193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513109216150099895529552257 384831912112574921647164193)
        ·
          refine ⟨288623934084431191235373145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384831912112574921647164193 288623934084431191235373145)
          ·
            refine ⟨216467950563323393426529859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288623934084431191235373145 216467950563323393426529859)
            ·
              refine ⟨324701925844985090139794789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216467950563323393426529859 324701925844985090139794789)
              ·
                refine ⟨60881611095934704401211523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324701925844985090139794789 60881611095934704401211523)
                ·
                  refine ⟨91322416643902056601817285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60881611095934704401211523 91322416643902056601817285)
                  ·
                    refine ⟨17122953120731635612840741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91322416643902056601817285 17122953120731635612840741)
                    ·
                      refine ⟨3210553710137181677407639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17122953120731635612840741 3210553710137181677407639)
                      ·
                        rfl

theorem cell23_6252531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_6252531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252531 prefixEnd_6252531 := by exact prefixLift 6252531
  have htrace : WordTrace (prefixWord ++ tailWord_6252531) baseStart_6252531 baseEnd_6252531 := by
    simpa [prefixWord, tailWord_6252531, baseEnd_6252531] using wordTrace_append hprefix tailTrace_6252531
  have hstable : (prefixWord ++ tailWord_6252531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252531).length < 2 ^ (prefixWord ++ tailWord_6252531).sum := by decide
  have hdescent : baseEnd_6252531 < baseStart_6252531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252541 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 9]
def baseStart_6252541 : Nat := 118140960795 + 6252541 * 2 ^ 59
def prefixEnd_6252541 : Nat := 4983230072969 + 3 ^ 40 * 6252541 * 2
def baseEnd_6252541 : Nat := 356728760549302959809177

theorem tailTrace_6252541 : CollatzResearch.WordTrace tailWord_6252541 prefixEnd_6252541 356728760549302959809177 := by
  unfold tailWord_6252541
  simp only [CollatzResearch.WordTrace]
  refine ⟨228048905241119280832109477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152032603494079520554739651 228048905241119280832109477)
  ·
    refine ⟨42759169732709865156020527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228048905241119280832109477 42759169732709865156020527)
    ·
      refine ⟨64138754599064797734030791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42759169732709865156020527 64138754599064797734030791)
      ·
        refine ⟨96208131898597196601046187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64138754599064797734030791 96208131898597196601046187)
        ·
          refine ⟨144312197847895794901569281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96208131898597196601046187 144312197847895794901569281)
          ·
            refine ⟨108234148385921846176176961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144312197847895794901569281 108234148385921846176176961)
            ·
              refine ⟨81175611289441384632132721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108234148385921846176176961 81175611289441384632132721)
              ·
                refine ⟨60881708467081038474099541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81175611289441384632132721 60881708467081038474099541)
                ·
                  refine ⟨356728760549302959809177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60881708467081038474099541 356728760549302959809177)
                  ·
                    rfl

theorem cell23_6252541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_6252541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252541 prefixEnd_6252541 := by exact prefixLift 6252541
  have htrace : WordTrace (prefixWord ++ tailWord_6252541) baseStart_6252541 baseEnd_6252541 := by
    simpa [prefixWord, tailWord_6252541, baseEnd_6252541] using wordTrace_append hprefix tailTrace_6252541
  have hstable : (prefixWord ++ tailWord_6252541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252541).length < 2 ^ (prefixWord ++ tailWord_6252541).sum := by decide
  have hdescent : baseEnd_6252541 < baseStart_6252541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252552 : List Nat := [2, 1, 3, 2, 1, 2, 2, 4, 2, 2, 2]
def baseStart_6252552 : Nat := 118140960795 + 6252552 * 2 ^ 59
def prefixEnd_6252552 : Nat := 4983230072969 + 3 ^ 40 * 6252552 * 2
def baseEnd_6252552 : Nat := 3210564493230926095245043

theorem tailTrace_6252552 : CollatzResearch.WordTrace tailWord_6252552 prefixEnd_6252552 3210564493230926095245043 := by
  unfold tailWord_6252552
  simp only [CollatzResearch.WordTrace]
  refine ⟨114024653222039714855379955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152032870962719619807173273 114024653222039714855379955)
  ·
    refine ⟨171036979833059572283069933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114024653222039714855379955 171036979833059572283069933)
    ·
      refine ⟨64138867437397339606151225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171036979833059572283069933 64138867437397339606151225)
      ·
        refine ⟨48104150578048004704613419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64138867437397339606151225 48104150578048004704613419)
        ·
          refine ⟨72156225867072007056920129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48104150578048004704613419 72156225867072007056920129)
          ·
            refine ⟨54117169400304005292690097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72156225867072007056920129 54117169400304005292690097)
            ·
              refine ⟨40587877050228003969517573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54117169400304005292690097 40587877050228003969517573)
              ·
                refine ⟨7610226946917750744284545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40587877050228003969517573 7610226946917750744284545)
                ·
                  refine ⟨5707670210188313058213409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7610226946917750744284545 5707670210188313058213409)
                  ·
                    refine ⟨4280752657641234793660057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5707670210188313058213409 4280752657641234793660057)
                    ·
                      refine ⟨3210564493230926095245043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4280752657641234793660057 3210564493230926095245043)
                      ·
                        rfl

theorem cell23_6252552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_6252552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252552 prefixEnd_6252552 := by exact prefixLift 6252552
  have htrace : WordTrace (prefixWord ++ tailWord_6252552) baseStart_6252552 baseEnd_6252552 := by
    simpa [prefixWord, tailWord_6252552, baseEnd_6252552] using wordTrace_append hprefix tailTrace_6252552
  have hstable : (prefixWord ++ tailWord_6252552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252552).length < 2 ^ (prefixWord ++ tailWord_6252552).sum := by decide
  have hdescent : baseEnd_6252552 < baseStart_6252552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252568 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 1, 5, 3]
def baseStart_6252568 : Nat := 118140960795 + 6252568 * 2 ^ 59
def prefixEnd_6252568 : Nat := 4983230072969 + 3 ^ 40 * 6252568 * 2
def baseEnd_6252568 : Nat := 3210572708921398032644969

theorem tailTrace_6252568 : CollatzResearch.WordTrace tailWord_6252568 prefixEnd_6252568 3210572708921398032644969 := by
  unfold tailWord_6252568
  simp only [CollatzResearch.WordTrace]
  refine ⟨114024945006010732221671179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152033260008014309628894905 114024945006010732221671179)
  ·
    refine ⟨171037417509016098332506769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114024945006010732221671179 171037417509016098332506769)
    ·
      refine ⟨128278063131762073749380077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171037417509016098332506769 128278063131762073749380077)
      ·
        refine ⟨48104273674410777656017529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128278063131762073749380077 48104273674410777656017529)
        ·
          refine ⟨36078205255808083242013147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48104273674410777656017529 36078205255808083242013147)
          ·
            refine ⟨54117307883712124863019721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36078205255808083242013147 54117307883712124863019721)
            ·
              refine ⟨40587980912784093647264791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54117307883712124863019721 40587980912784093647264791)
              ·
                refine ⟨60881971369176140470897187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40587980912784093647264791 60881971369176140470897187)
                ·
                  refine ⟨91322957053764210706345781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60881971369176140470897187 91322957053764210706345781)
                  ·
                    refine ⟨8561527223790394753719917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91322957053764210706345781 8561527223790394753719917)
                    ·
                      refine ⟨3210572708921398032644969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8561527223790394753719917 3210572708921398032644969)
                      ·
                        rfl

theorem cell23_6252568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_6252568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252568 prefixEnd_6252568 := by exact prefixLift 6252568
  have htrace : WordTrace (prefixWord ++ tailWord_6252568) baseStart_6252568 baseEnd_6252568 := by
    simpa [prefixWord, tailWord_6252568, baseEnd_6252568] using wordTrace_append hprefix tailTrace_6252568
  have hstable : (prefixWord ++ tailWord_6252568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252568).length < 2 ^ (prefixWord ++ tailWord_6252568).sum := by decide
  have hdescent : baseEnd_6252568 < baseStart_6252568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252571 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 1, 7]
def baseStart_6252571 : Nat := 118140960795 + 6252571 * 2 ^ 59
def prefixEnd_6252571 : Nat := 4983230072969 + 3 ^ 40 * 6252571 * 2
def baseEnd_6252571 : Nat := 1070191416454453840302485

theorem tailTrace_6252571 : CollatzResearch.WordTrace tailWord_6252571 prefixEnd_6252571 1070191416454453840302485 := by
  unfold tailWord_6252571
  simp only [CollatzResearch.WordTrace]
  refine ⟨228049999431010595955701567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152033332954007063970467711 228049999431010595955701567)
  ·
    refine ⟨342074999146515893933552351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228049999431010595955701567 342074999146515893933552351)
    ·
      refine ⟨513112498719773840900328527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342074999146515893933552351 513112498719773840900328527)
      ·
        refine ⟨769668748079660761350492791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513112498719773840900328527 769668748079660761350492791)
        ·
          refine ⟨1154503122119491142025739187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769668748079660761350492791 1154503122119491142025739187)
          ·
            refine ⟨1731754683179236713038608781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154503122119491142025739187 1731754683179236713038608781)
            ·
              refine ⟨649408006192213767389478293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1731754683179236713038608781 649408006192213767389478293)
              ·
                refine ⟨30441000290260020346381795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 649408006192213767389478293 30441000290260020346381795)
                ·
                  refine ⟨45661500435390030519572693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30441000290260020346381795 45661500435390030519572693)
                  ·
                    refine ⟨1070191416454453840302485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45661500435390030519572693 1070191416454453840302485)
                    ·
                      rfl

theorem cell23_6252571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 7].length) (baseStart_6252571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252571 prefixEnd_6252571 := by exact prefixLift 6252571
  have htrace : WordTrace (prefixWord ++ tailWord_6252571) baseStart_6252571 baseEnd_6252571 := by
    simpa [prefixWord, tailWord_6252571, baseEnd_6252571] using wordTrace_append hprefix tailTrace_6252571
  have hstable : (prefixWord ++ tailWord_6252571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252571).length < 2 ^ (prefixWord ++ tailWord_6252571).sum := by decide
  have hdescent : baseEnd_6252571 < baseStart_6252571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252609 : List Nat := [1, 2, 5, 1, 2, 3, 2, 2, 5]
def baseStart_6252609 : Nat := 118140960795 + 6252609 * 2 ^ 59
def prefixEnd_6252609 : Nat := 4983230072969 + 3 ^ 40 * 6252609 * 2
def baseEnd_6252609 : Nat := 356732640180914708025809

theorem tailTrace_6252609 : CollatzResearch.WordTrace tailWord_6252609 prefixEnd_6252609 356732640180914708025809 := by
  unfold tailWord_6252609
  simp only [CollatzResearch.WordTrace]
  refine ⟨228051385404872928445584881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152034256936581952297056587 228051385404872928445584881)
  ·
    refine ⟨171038539053654696334188661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228051385404872928445584881 171038539053654696334188661)
    ·
      refine ⟨16034863036280127781330187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171038539053654696334188661 16034863036280127781330187)
      ·
        refine ⟨24052294554420191671995281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16034863036280127781330187 24052294554420191671995281)
        ·
          refine ⟨18039220915815143753996461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24052294554420191671995281 18039220915815143753996461)
          ·
            refine ⟨6764707843430678907748673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18039220915815143753996461 6764707843430678907748673)
            ·
              refine ⟨5073530882573009180811505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6764707843430678907748673 5073530882573009180811505)
              ·
                refine ⟨3805148161929756885608629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5073530882573009180811505 3805148161929756885608629)
                ·
                  refine ⟨356732640180914708025809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3805148161929756885608629 356732640180914708025809)
                  ·
                    rfl

theorem cell23_6252609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 5].length) (baseStart_6252609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252609 prefixEnd_6252609 := by exact prefixLift 6252609
  have htrace : WordTrace (prefixWord ++ tailWord_6252609) baseStart_6252609 baseEnd_6252609 := by
    simpa [prefixWord, tailWord_6252609, baseEnd_6252609] using wordTrace_append hprefix tailTrace_6252609
  have hstable : (prefixWord ++ tailWord_6252609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252609).length < 2 ^ (prefixWord ++ tailWord_6252609).sum := by decide
  have hdescent : baseEnd_6252609 < baseStart_6252609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252642 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_6252642 : Nat := 118140960795 + 6252642 * 2 ^ 59
def prefixEnd_6252642 : Nat := 4983230072969 + 3 ^ 40 * 6252642 * 2
def baseEnd_6252642 : Nat := 3210610706489830743119629

theorem tailTrace_6252642 : CollatzResearch.WordTrace tailWord_6252642 prefixEnd_6252642 3210610706489830743119629 := by
  unfold tailWord_6252642
  simp only [CollatzResearch.WordTrace]
  refine ⟨57013147253438343770384045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152035059342502250054357453 57013147253438343770384045)
  ·
    refine ⟨21379930220039378913894017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57013147253438343770384045 21379930220039378913894017)
    ·
      refine ⟨16034947665029534185420513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21379930220039378913894017 16034947665029534185420513)
      ·
        refine ⟨12026210748772150639065385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16034947665029534185420513 12026210748772150639065385)
        ·
          refine ⟨9019658061579112979299039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12026210748772150639065385 9019658061579112979299039)
          ·
            refine ⟨13529487092368669468948559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9019658061579112979299039 13529487092368669468948559)
            ·
              refine ⟨20294230638553004203422839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13529487092368669468948559 20294230638553004203422839)
              ·
                refine ⟨30441345957829506305134259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20294230638553004203422839 30441345957829506305134259)
                ·
                  refine ⟨45662018936744259457701389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30441345957829506305134259 45662018936744259457701389)
                  ·
                    refine ⟨17123257101279097296638021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45662018936744259457701389 17123257101279097296638021)
                    ·
                      refine ⟨3210610706489830743119629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17123257101279097296638021 3210610706489830743119629)
                      ·
                        rfl

theorem cell23_6252642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_6252642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252642 prefixEnd_6252642 := by exact prefixLift 6252642
  have htrace : WordTrace (prefixWord ++ tailWord_6252642) baseStart_6252642 baseEnd_6252642 := by
    simpa [prefixWord, tailWord_6252642, baseEnd_6252642] using wordTrace_append hprefix tailTrace_6252642
  have hstable : (prefixWord ++ tailWord_6252642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252642).length < 2 ^ (prefixWord ++ tailWord_6252642).sum := by decide
  have hdescent : baseEnd_6252642 < baseStart_6252642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252645 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 1, 4, 3]
def baseStart_6252645 : Nat := 118140960795 + 6252645 * 2 ^ 59
def prefixEnd_6252645 : Nat := 4983230072969 + 3 ^ 40 * 6252645 * 2
def baseEnd_6252645 : Nat := 3210612246931794231382115

theorem tailTrace_6252645 : CollatzResearch.WordTrace tailWord_6252645 prefixEnd_6252645 3210612246931794231382115 := by
  unfold tailWord_6252645
  simp only [CollatzResearch.WordTrace]
  refine ⟨228052698432742506593895389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152035132288495004395930259 228052698432742506593895389)
  ·
    refine ⟨85519761912278439972710771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228052698432742506593895389 85519761912278439972710771)
    ·
      refine ⟨128279642868417659959066157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85519761912278439972710771 128279642868417659959066157)
      ·
        refine ⟨48104866075656622484649809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128279642868417659959066157 48104866075656622484649809)
        ·
          refine ⟨36078649556742466863487357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48104866075656622484649809 36078649556742466863487357)
          ·
            refine ⟨13529493583778425073807759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36078649556742466863487357 13529493583778425073807759)
            ·
              refine ⟨20294240375667637610711639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13529493583778425073807759 20294240375667637610711639)
              ·
                refine ⟨30441360563501456416067459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20294240375667637610711639 30441360563501456416067459)
                ·
                  refine ⟨45662040845252184624101189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30441360563501456416067459 45662040845252184624101189)
                  ·
                    refine ⟨8561632658484784617018973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45662040845252184624101189 8561632658484784617018973)
                    ·
                      refine ⟨3210612246931794231382115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8561632658484784617018973 3210612246931794231382115)
                      ·
                        rfl

theorem cell23_6252645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_6252645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252645 prefixEnd_6252645 := by exact prefixLift 6252645
  have htrace : WordTrace (prefixWord ++ tailWord_6252645) baseStart_6252645 baseEnd_6252645 := by
    simpa [prefixWord, tailWord_6252645, baseEnd_6252645] using wordTrace_append hprefix tailTrace_6252645
  have hstable : (prefixWord ++ tailWord_6252645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252645).length < 2 ^ (prefixWord ++ tailWord_6252645).sum := by decide
  have hdescent : baseEnd_6252645 < baseStart_6252645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252652 : List Nat := [2, 2, 1, 1, 3, 3, 1, 5, 1, 4]
def baseStart_6252652 : Nat := 118140960795 + 6252652 * 2 ^ 59
def prefixEnd_6252652 : Nat := 4983230072969 + 3 ^ 40 * 6252652 * 2
def baseEnd_6252652 : Nat := 1070205280432125234664861

theorem tailTrace_6252652 : CollatzResearch.WordTrace tailWord_6252652 prefixEnd_6252652 1070205280432125234664861 := by
  unfold tailWord_6252652
  simp only [CollatzResearch.WordTrace]
  refine ⟨114026476871858573394700105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152035302495811431192933473 114026476871858573394700105)
  ·
    refine ⟨85519857653893930046025079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114026476871858573394700105 85519857653893930046025079)
    ·
      refine ⟨128279786480840895069037619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85519857653893930046025079 128279786480840895069037619)
      ·
        refine ⟨192419679721261342603556429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128279786480840895069037619 192419679721261342603556429)
        ·
          refine ⟨72157379895473003476333661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192419679721261342603556429 72157379895473003476333661)
          ·
            refine ⟨27059017460802376303625123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72157379895473003476333661 27059017460802376303625123)
            ·
              refine ⟨40588526191203564455437685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27059017460802376303625123 40588526191203564455437685)
              ·
                refine ⟨3805174330425334167697283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40588526191203564455437685 3805174330425334167697283)
                ·
                  refine ⟨5707761495638001251545925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3805174330425334167697283 5707761495638001251545925)
                  ·
                    refine ⟨1070205280432125234664861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5707761495638001251545925 1070205280432125234664861)
                    ·
                      rfl

theorem cell23_6252652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_6252652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252652 prefixEnd_6252652 := by exact prefixLift 6252652
  have htrace : WordTrace (prefixWord ++ tailWord_6252652) baseStart_6252652 baseEnd_6252652 := by
    simpa [prefixWord, tailWord_6252652, baseEnd_6252652] using wordTrace_append hprefix tailTrace_6252652
  have hstable : (prefixWord ++ tailWord_6252652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252652).length < 2 ^ (prefixWord ++ tailWord_6252652).sum := by decide
  have hdescent : baseEnd_6252652 < baseStart_6252652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252665 : List Nat := [1, 2, 1, 3, 4, 1, 3, 2, 6]
def baseStart_6252665 : Nat := 118140960795 + 6252665 * 2 ^ 59
def prefixEnd_6252665 : Nat := 4983230072969 + 3 ^ 40 * 6252665 * 2
def baseEnd_6252665 : Nat := 356735835171653794792447

theorem tailTrace_6252665 : CollatzResearch.WordTrace tailWord_6252665 prefixEnd_6252665 356735835171653794792447 := by
  unfold tailWord_6252665
  simp only [CollatzResearch.WordTrace]
  refine ⟨228053427892670050009623449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152035618595113366673082299 228053427892670050009623449)
  ·
    refine ⟨171040070919502537507217587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228053427892670050009623449 171040070919502537507217587)
    ·
      refine ⟨256560106379253806260826381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171040070919502537507217587 256560106379253806260826381)
      ·
        refine ⟨96210039892220177347809893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256560106379253806260826381 96210039892220177347809893)
        ·
          refine ⟨18039382479791283252714355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96210039892220177347809893 18039382479791283252714355)
          ·
            refine ⟨27059073719686924879071533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18039382479791283252714355 27059073719686924879071533)
            ·
              refine ⟨10147152644882596829651825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27059073719686924879071533 10147152644882596829651825)
              ·
                refine ⟨7610364483661947622238869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10147152644882596829651825 7610364483661947622238869)
                ·
                  refine ⟨356735835171653794792447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7610364483661947622238869 356735835171653794792447)
                  ·
                    rfl

theorem cell23_6252665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 6].length) (baseStart_6252665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252665 prefixEnd_6252665 := by exact prefixLift 6252665
  have htrace : WordTrace (prefixWord ++ tailWord_6252665) baseStart_6252665 baseEnd_6252665 := by
    simpa [prefixWord, tailWord_6252665, baseEnd_6252665] using wordTrace_append hprefix tailTrace_6252665
  have hstable : (prefixWord ++ tailWord_6252665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252665).length < 2 ^ (prefixWord ++ tailWord_6252665).sum := by decide
  have hdescent : baseEnd_6252665 < baseStart_6252665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252668 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_6252668 : Nat := 118140960795 + 6252668 * 2 ^ 59
def prefixEnd_6252668 : Nat := 4983230072969 + 3 ^ 40 * 6252668 * 2
def baseEnd_6252668 : Nat := 3210624056986847641394509

theorem tailTrace_6252668 : CollatzResearch.WordTrace tailWord_6252668 prefixEnd_6252668 3210624056986847641394509 := by
  unfold tailWord_6252668
  simp only [CollatzResearch.WordTrace]
  refine ⟨114026768655829590760991329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152035691541106121014655105 114026768655829590760991329)
  ·
    refine ⟨85520076491872193070743497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114026768655829590760991329 85520076491872193070743497)
    ·
      refine ⟨64140057368904144803057623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85520076491872193070743497 64140057368904144803057623)
      ·
        refine ⟨96210086053356217204586435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64140057368904144803057623 96210086053356217204586435)
        ·
          refine ⟨144315129080034325806879653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96210086053356217204586435 144315129080034325806879653)
          ·
            refine ⟨27059086702506436088789935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144315129080034325806879653 27059086702506436088789935)
            ·
              refine ⟨40588630053759654133184903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27059086702506436088789935 40588630053759654133184903)
              ·
                refine ⟨60882945080639481199777355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40588630053759654133184903 60882945080639481199777355)
                ·
                  refine ⟨91324417620959221799666033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60882945080639481199777355 91324417620959221799666033)
                  ·
                    refine ⟨68493313215719416349749525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91324417620959221799666033 68493313215719416349749525)
                    ·
                      refine ⟨3210624056986847641394509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68493313215719416349749525 3210624056986847641394509)
                      ·
                        rfl

theorem cell23_6252668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_6252668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252668 prefixEnd_6252668 := by exact prefixLift 6252668
  have htrace : WordTrace (prefixWord ++ tailWord_6252668) baseStart_6252668 baseEnd_6252668 := by
    simpa [prefixWord, tailWord_6252668, baseEnd_6252668] using wordTrace_append hprefix tailTrace_6252668
  have hstable : (prefixWord ++ tailWord_6252668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252668).length < 2 ^ (prefixWord ++ tailWord_6252668).sum := by decide
  have hdescent : baseEnd_6252668 < baseStart_6252668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252682 : List Nat := [3, 1, 2, 3, 1, 3, 3, 1, 6]
def baseStart_6252682 : Nat := 118140960795 + 6252682 * 2 ^ 59
def prefixEnd_6252682 : Nat := 4983230072969 + 3 ^ 40 * 6252682 * 2
def baseEnd_6252682 : Nat := 356736805079556731846605

theorem tailTrace_6252682 : CollatzResearch.WordTrace tailWord_6252682 prefixEnd_6252682 356736805079556731846605 := by
  unfold tailWord_6252682
  simp only [CollatzResearch.WordTrace]
  refine ⟨57013511983402115478248075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152036031955738974608661533 57013511983402115478248075)
  ·
    refine ⟨85520267975103173217372113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57013511983402115478248075 85520267975103173217372113)
    ·
      refine ⟨64140200981327379913029085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85520267975103173217372113 64140200981327379913029085)
      ·
        refine ⟨24052575367997767467385907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64140200981327379913029085 24052575367997767467385907)
        ·
          refine ⟨36078863051996651201078861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24052575367997767467385907 36078863051996651201078861)
          ·
            refine ⟨13529573644498744200404573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36078863051996651201078861 13529573644498744200404573)
            ·
              refine ⟨5073590116687029075151715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13529573644498744200404573 5073590116687029075151715)
              ·
                refine ⟨7610385175030543612727573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5073590116687029075151715 7610385175030543612727573)
                ·
                  refine ⟨356736805079556731846605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7610385175030543612727573 356736805079556731846605)
                  ·
                    rfl

theorem cell23_6252682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 6].length) (baseStart_6252682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252682 prefixEnd_6252682 := by exact prefixLift 6252682
  have htrace : WordTrace (prefixWord ++ tailWord_6252682) baseStart_6252682 baseEnd_6252682 := by
    simpa [prefixWord, tailWord_6252682, baseEnd_6252682] using wordTrace_append hprefix tailTrace_6252682
  have hstable : (prefixWord ++ tailWord_6252682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252682).length < 2 ^ (prefixWord ++ tailWord_6252682).sum := by decide
  have hdescent : baseEnd_6252682 < baseStart_6252682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252728 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_6252728 : Nat := 118140960795 + 6252728 * 2 ^ 59
def prefixEnd_6252728 : Nat := 4983230072969 + 3 ^ 40 * 6252728 * 2
def baseEnd_6252728 : Nat := 3210654865826117406644233

theorem tailTrace_6252728 : CollatzResearch.WordTrace tailWord_6252728 prefixEnd_6252728 3210654865826117406644233 := by
  unfold tailWord_6252728
  simp only [CollatzResearch.WordTrace]
  refine ⟨114027862845720905884583419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152037150460961207846111225 114027862845720905884583419)
  ·
    refine ⟨171041794268581358826875129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114027862845720905884583419 171041794268581358826875129)
    ·
      refine ⟨128281345701436019120156347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171041794268581358826875129 128281345701436019120156347)
      ·
        refine ⟨192422018552154028680234521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128281345701436019120156347 192422018552154028680234521)
        ·
          refine ⟨144316513914115521510175891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192422018552154028680234521 144316513914115521510175891)
          ·
            refine ⟨216474770871173282265263837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144316513914115521510175891 216474770871173282265263837)
            ·
              refine ⟨81178039076689980849473939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216474770871173282265263837 81178039076689980849473939)
              ·
                refine ⟨121767058615034971274210909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81178039076689980849473939 121767058615034971274210909)
                ·
                  refine ⟨45662646980638114227829091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121767058615034971274210909 45662646980638114227829091)
                  ·
                    refine ⟨68493970470957171341743637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45662646980638114227829091 68493970470957171341743637)
                    ·
                      refine ⟨3210654865826117406644233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68493970470957171341743637 3210654865826117406644233)
                      ·
                        rfl

theorem cell23_6252728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_6252728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252728 prefixEnd_6252728 := by exact prefixLift 6252728
  have htrace : WordTrace (prefixWord ++ tailWord_6252728) baseStart_6252728 baseEnd_6252728 := by
    simpa [prefixWord, tailWord_6252728, baseEnd_6252728] using wordTrace_append hprefix tailTrace_6252728
  have hstable : (prefixWord ++ tailWord_6252728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252728).length < 2 ^ (prefixWord ++ tailWord_6252728).sum := by decide
  have hdescent : baseEnd_6252728 < baseStart_6252728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252735 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 3]
def baseStart_6252735 : Nat := 118140960795 + 6252735 * 2 ^ 59
def prefixEnd_6252735 : Nat := 4983230072969 + 3 ^ 40 * 6252735 * 2
def baseEnd_6252735 : Nat := 3210658460190698879256701

theorem tailTrace_6252735 : CollatzResearch.WordTrace tailWord_6252735 prefixEnd_6252735 3210658460190698879256701 := by
  unfold tailWord_6252735
  simp only [CollatzResearch.WordTrace]
  refine ⟨228055981002416451964671659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152037320668277634643114439 228055981002416451964671659)
  ·
    refine ⟨342083971503624677947007489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228055981002416451964671659 342083971503624677947007489)
    ·
      refine ⟨256562978627718508460255617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342083971503624677947007489 256562978627718508460255617)
      ·
        refine ⟨192422233970788881345191713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256562978627718508460255617 192422233970788881345191713)
        ·
          refine ⟨144316675478091661008893785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192422233970788881345191713 144316675478091661008893785)
          ·
            refine ⟨108237506608568745756670339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144316675478091661008893785 108237506608568745756670339)
            ·
              refine ⟨162356259912853118635005509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108237506608568745756670339 162356259912853118635005509)
              ·
                refine ⟨30441798733659959744063533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162356259912853118635005509 30441798733659959744063533)
                ·
                  refine ⟨11415674525122484904023825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30441798733659959744063533 11415674525122484904023825)
                  ·
                    refine ⟨8561755893841863678017869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11415674525122484904023825 8561755893841863678017869)
                    ·
                      refine ⟨3210658460190698879256701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8561755893841863678017869 3210658460190698879256701)
                      ·
                        rfl

theorem cell23_6252735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_6252735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252735 prefixEnd_6252735 := by exact prefixLift 6252735
  have htrace : WordTrace (prefixWord ++ tailWord_6252735) baseStart_6252735 baseEnd_6252735 := by
    simpa [prefixWord, tailWord_6252735, baseEnd_6252735] using wordTrace_append hprefix tailTrace_6252735
  have hstable : (prefixWord ++ tailWord_6252735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252735).length < 2 ^ (prefixWord ++ tailWord_6252735).sum := by decide
  have hdescent : baseEnd_6252735 < baseStart_6252735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252769 : List Nat := [1, 2, 3, 1, 3, 1, 5, 1, 1, 2, 3]
def baseStart_6252769 : Nat := 118140960795 + 6252769 * 2 ^ 59
def prefixEnd_6252769 : Nat := 4983230072969 + 3 ^ 40 * 6252769 * 2
def baseEnd_6252769 : Nat := 3210675918532951746231545

theorem tailTrace_6252769 : CollatzResearch.WordTrace tailWord_6252769 prefixEnd_6252769 3210675918532951746231545 := by
  unfold tailWord_6252769
  simp only [CollatzResearch.WordTrace]
  refine ⟨228057221084293275771409361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152038147389528850514272907 228057221084293275771409361)
  ·
    refine ⟨171042915813219956828557021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228057221084293275771409361 171042915813219956828557021)
    ·
      refine ⟨64141093429957483810708883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171042915813219956828557021 64141093429957483810708883)
      ·
        refine ⟨96211640144936225716063325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64141093429957483810708883 96211640144936225716063325)
        ·
          refine ⟨36079365054351084643523747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96211640144936225716063325 36079365054351084643523747)
          ·
            refine ⟨54119047581526626965285621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36079365054351084643523747 54119047581526626965285621)
            ·
              refine ⟨5073660710768121277995527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54119047581526626965285621 5073660710768121277995527)
              ·
                refine ⟨7610491066152181916993291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5073660710768121277995527 7610491066152181916993291)
                ·
                  refine ⟨11415736599228272875489937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7610491066152181916993291 11415736599228272875489937)
                  ·
                    refine ⟨8561802449421204656617453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11415736599228272875489937 8561802449421204656617453)
                    ·
                      refine ⟨3210675918532951746231545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8561802449421204656617453 3210675918532951746231545)
                      ·
                        rfl

theorem cell23_6252769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_6252769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252769 prefixEnd_6252769 := by exact prefixLift 6252769
  have htrace : WordTrace (prefixWord ++ tailWord_6252769) baseStart_6252769 baseEnd_6252769 := by
    simpa [prefixWord, tailWord_6252769, baseEnd_6252769] using wordTrace_append hprefix tailTrace_6252769
  have hstable : (prefixWord ++ tailWord_6252769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252769).length < 2 ^ (prefixWord ++ tailWord_6252769).sum := by decide
  have hdescent : baseEnd_6252769 < baseStart_6252769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252783 : List Nat := [1, 1, 2, 1, 6, 1, 4, 2, 1, 2, 2]
def baseStart_6252783 : Nat := 118140960795 + 6252783 * 2 ^ 59
def prefixEnd_6252783 : Nat := 4983230072969 + 3 ^ 40 * 6252783 * 2
def baseEnd_6252783 : Nat := 3210683107262114691456481

theorem tailTrace_6252783 : CollatzResearch.WordTrace tailWord_6252783 prefixEnd_6252783 3210683107262114691456481 := by
  unfold tailWord_6252783
  simp only [CollatzResearch.WordTrace]
  refine ⟨228057731706242556162419003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152038487804161704108279335 228057731706242556162419003)
  ·
    refine ⟨342086597559363834243628505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228057731706242556162419003 342086597559363834243628505)
    ·
      refine ⟨256564948169522875682721379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342086597559363834243628505 256564948169522875682721379)
      ·
        refine ⟨384847422254284313524082069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256564948169522875682721379 384847422254284313524082069)
        ·
          refine ⟨18039722918169577196441347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 384847422254284313524082069 18039722918169577196441347)
          ·
            refine ⟨27059584377254365794662021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18039722918169577196441347 27059584377254365794662021)
            ·
              refine ⟨5073672070735193586499129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27059584377254365794662021 5073672070735193586499129)
              ·
                refine ⟨3805254053051395189874347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5073672070735193586499129 3805254053051395189874347)
                ·
                  refine ⟨5707881079577092784811521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3805254053051395189874347 5707881079577092784811521)
                  ·
                    refine ⟨4280910809682819588608641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5707881079577092784811521 4280910809682819588608641)
                    ·
                      refine ⟨3210683107262114691456481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4280910809682819588608641 3210683107262114691456481)
                      ·
                        rfl

theorem cell23_6252783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 1, 2, 2].length) (baseStart_6252783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252783 prefixEnd_6252783 := by exact prefixLift 6252783
  have htrace : WordTrace (prefixWord ++ tailWord_6252783) baseStart_6252783 baseEnd_6252783 := by
    simpa [prefixWord, tailWord_6252783, baseEnd_6252783] using wordTrace_append hprefix tailTrace_6252783
  have hstable : (prefixWord ++ tailWord_6252783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252783).length < 2 ^ (prefixWord ++ tailWord_6252783).sum := by decide
  have hdescent : baseEnd_6252783 < baseStart_6252783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252826 : List Nat := [3, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2]
def baseStart_6252826 : Nat := 118140960795 + 6252826 * 2 ^ 59
def prefixEnd_6252826 : Nat := 4983230072969 + 3 ^ 40 * 6252826 * 2
def baseEnd_6252826 : Nat := 3210705186930258023218783

theorem tailTrace_6252826 : CollatzResearch.WordTrace tailWord_6252826 prefixEnd_6252826 3210705186930258023218783 := by
  unfold tailWord_6252826
  simp only [CollatzResearch.WordTrace]
  refine ⟨57014825011271693626558583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152039533363391183004156221 57014825011271693626558583)
  ·
    refine ⟨85522237516907540439837875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57014825011271693626558583 85522237516907540439837875)
    ·
      refine ⟨128283356275361310659756813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85522237516907540439837875 128283356275361310659756813)
      ·
        refine ⟨48106258603260491497408805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128283356275361310659756813 48106258603260491497408805)
        ·
          refine ⟨9019923488111342155764151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48106258603260491497408805 9019923488111342155764151)
          ·
            refine ⟨13529885232167013233646227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9019923488111342155764151 13529885232167013233646227)
            ·
              refine ⟨20294827848250519850469341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13529885232167013233646227 20294827848250519850469341)
              ·
                refine ⟨7610560443093944943926003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20294827848250519850469341 7610560443093944943926003)
                ·
                  refine ⟨11415840664640917415889005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7610560443093944943926003 11415840664640917415889005)
                  ·
                    refine ⟨4280940249240344030958377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11415840664640917415889005 4280940249240344030958377)
                    ·
                      refine ⟨3210705186930258023218783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4280940249240344030958377 3210705186930258023218783)
                      ·
                        rfl

theorem cell23_6252826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_6252826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252826 prefixEnd_6252826 := by exact prefixLift 6252826
  have htrace : WordTrace (prefixWord ++ tailWord_6252826) baseStart_6252826 baseEnd_6252826 := by
    simpa [prefixWord, tailWord_6252826, baseEnd_6252826] using wordTrace_append hprefix tailTrace_6252826
  have hstable : (prefixWord ++ tailWord_6252826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252826).length < 2 ^ (prefixWord ++ tailWord_6252826).sum := by decide
  have hdescent : baseEnd_6252826 < baseStart_6252826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252835 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 4]
def baseStart_6252835 : Nat := 118140960795 + 6252835 * 2 ^ 59
def prefixEnd_6252835 : Nat := 4983230072969 + 3 ^ 40 * 6252835 * 2
def baseEnd_6252835 : Nat := 3210709808256148488006241

theorem tailTrace_6252835 : CollatzResearch.WordTrace tailWord_6252835 prefixEnd_6252835 3210709808256148488006241 := by
  unfold tailWord_6252835
  simp only [CollatzResearch.WordTrace]
  refine ⟨228059628302054169043311959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152039752201369446028874639 228059628302054169043311959)
  ·
    refine ⟨342089442453081253564967939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228059628302054169043311959 342089442453081253564967939)
    ·
      refine ⟨513134163679621880347451909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342089442453081253564967939 513134163679621880347451909)
      ·
        refine ⟨96212655689929102565147233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 513134163679621880347451909 96212655689929102565147233)
        ·
          refine ⟨72159491767446826923860425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96212655689929102565147233 72159491767446826923860425)
          ·
            refine ⟨54119618825585120192895319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72159491767446826923860425 54119618825585120192895319)
            ·
              refine ⟨81179428238377680289342979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54119618825585120192895319 81179428238377680289342979)
              ·
                refine ⟨121769142357566520434014469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81179428238377680289342979 121769142357566520434014469)
                ·
                  refine ⟨22831714192043722581377713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121769142357566520434014469 22831714192043722581377713)
                  ·
                    refine ⟨17123785644032791936033285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22831714192043722581377713 17123785644032791936033285)
                    ·
                      refine ⟨3210709808256148488006241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17123785644032791936033285 3210709808256148488006241)
                      ·
                        rfl

theorem cell23_6252835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_6252835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252835 prefixEnd_6252835 := by exact prefixLift 6252835
  have htrace : WordTrace (prefixWord ++ tailWord_6252835) baseStart_6252835 baseEnd_6252835 := by
    simpa [prefixWord, tailWord_6252835, baseEnd_6252835] using wordTrace_append hprefix tailTrace_6252835
  have hstable : (prefixWord ++ tailWord_6252835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252835).length < 2 ^ (prefixWord ++ tailWord_6252835).sum := by decide
  have hdescent : baseEnd_6252835 < baseStart_6252835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252862 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 7]
def baseStart_6252862 : Nat := 118140960795 + 6252862 * 2 ^ 59
def prefixEnd_6252862 : Nat := 4983230072969 + 3 ^ 40 * 6252862 * 2
def baseEnd_6252862 : Nat := 356747074692646653596513

theorem tailTrace_6252862 : CollatzResearch.WordTrace tailWord_6252862 prefixEnd_6252862 356747074692646653596513 := by
  unfold tailWord_6252862
  simp only [CollatzResearch.WordTrace]
  refine ⟨28507576634119544081818105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152040408715304235103029893 28507576634119544081818105)
  ·
    refine ⟨21380682475589658061363579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28507576634119544081818105 21380682475589658061363579)
    ·
      refine ⟨32071023713384487092045369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21380682475589658061363579 32071023713384487092045369)
      ·
        refine ⟨24053267785038365319034027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32071023713384487092045369 24053267785038365319034027)
        ·
          refine ⟨36079901677557547978551041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24053267785038365319034027 36079901677557547978551041)
          ·
            refine ⟨27059926258168160983913281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36079901677557547978551041 27059926258168160983913281)
            ·
              refine ⟨20294944693626120737934961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27059926258168160983913281 20294944693626120737934961)
              ·
                refine ⟨15221208520219590553451221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20294944693626120737934961 15221208520219590553451221)
                ·
                  refine ⟨356747074692646653596513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15221208520219590553451221 356747074692646653596513)
                  ·
                    rfl

theorem cell23_6252862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_6252862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252862 prefixEnd_6252862 := by exact prefixLift 6252862
  have htrace : WordTrace (prefixWord ++ tailWord_6252862) baseStart_6252862 baseEnd_6252862 := by
    simpa [prefixWord, tailWord_6252862, baseEnd_6252862] using wordTrace_append hprefix tailTrace_6252862
  have hstable : (prefixWord ++ tailWord_6252862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252862).length < 2 ^ (prefixWord ++ tailWord_6252862).sum := by decide
  have hdescent : baseEnd_6252862 < baseStart_6252862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252896 : List Nat := [2, 1, 1, 3, 5, 1, 3, 2, 5]
def baseStart_6252896 : Nat := 118140960795 + 6252896 * 2 ^ 59
def prefixEnd_6252896 : Nat := 4983230072969 + 3 ^ 40 * 6252896 * 2
def baseEnd_6252896 : Nat := 356749014508452527704829

theorem tailTrace_6252896 : CollatzResearch.WordTrace tailWord_6252896 prefixEnd_6252896 356749014508452527704829 := by
  unfold tailWord_6252896
  simp only [CollatzResearch.WordTrace]
  refine ⟨114030926577416588230641271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152041235436555450974188361 114030926577416588230641271)
  ·
    refine ⟨171046389866124882345961907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114030926577416588230641271 171046389866124882345961907)
    ·
      refine ⟨256569584799187323518942861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171046389866124882345961907 256569584799187323518942861)
      ·
        refine ⟨96213594299695246319603573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256569584799187323518942861 96213594299695246319603573)
        ·
          refine ⟨9020024465596429342462835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96213594299695246319603573 9020024465596429342462835)
          ·
            refine ⟨13530036698394644013694253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9020024465596429342462835 13530036698394644013694253)
            ·
              refine ⟨5073763761897991505135345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13530036698394644013694253 5073763761897991505135345)
              ·
                refine ⟨3805322821423493628851509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5073763761897991505135345 3805322821423493628851509)
                ·
                  refine ⟨356749014508452527704829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3805322821423493628851509 356749014508452527704829)
                  ·
                    rfl

theorem cell23_6252896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 5].length) (baseStart_6252896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252896 prefixEnd_6252896 := by exact prefixLift 6252896
  have htrace : WordTrace (prefixWord ++ tailWord_6252896) baseStart_6252896 baseEnd_6252896 := by
    simpa [prefixWord, tailWord_6252896, baseEnd_6252896] using wordTrace_append hprefix tailTrace_6252896
  have hstable : (prefixWord ++ tailWord_6252896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252896).length < 2 ^ (prefixWord ++ tailWord_6252896).sum := by decide
  have hdescent : baseEnd_6252896 < baseStart_6252896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252929 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_6252929 : Nat := 118140960795 + 6252929 * 2 ^ 59
def prefixEnd_6252929 : Nat := 4983230072969 + 3 ^ 40 * 6252929 * 2
def baseEnd_6252929 : Nat := 3210758075437671120230809

theorem tailTrace_6252929 : CollatzResearch.WordTrace tailWord_6252929 prefixEnd_6252929 3210758075437671120230809 := by
  unfold tailWord_6252929
  simp only [CollatzResearch.WordTrace]
  refine ⟨228063056763713623097233841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152042037842475748731489227 228063056763713623097233841)
  ·
    refine ⟨171047292572785217322925381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228063056763713623097233841 171047292572785217322925381)
    ·
      refine ⟨32071367357397228248048509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171047292572785217322925381 32071367357397228248048509)
      ·
        refine ⟨12026762759023960593018191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32071367357397228248048509 12026762759023960593018191)
        ·
          refine ⟨18040144138535940889527287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12026762759023960593018191 18040144138535940889527287)
          ·
            refine ⟨27060216207803911334290931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18040144138535940889527287 27060216207803911334290931)
            ·
              refine ⟨40590324311705867001436397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27060216207803911334290931 40590324311705867001436397)
              ·
                refine ⟨15221371616889700125538649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40590324311705867001436397 15221371616889700125538649)
                ·
                  refine ⟨11416028712667275094153987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15221371616889700125538649 11416028712667275094153987)
                  ·
                    refine ⟨17124043069000912641230981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11416028712667275094153987 17124043069000912641230981)
                    ·
                      refine ⟨3210758075437671120230809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17124043069000912641230981 3210758075437671120230809)
                      ·
                        rfl

theorem cell23_6252929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_6252929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252929 prefixEnd_6252929 := by exact prefixLift 6252929
  have htrace : WordTrace (prefixWord ++ tailWord_6252929) baseStart_6252929 baseEnd_6252929 := by
    simpa [prefixWord, tailWord_6252929, baseEnd_6252929] using wordTrace_append hprefix tailTrace_6252929
  have hstable : (prefixWord ++ tailWord_6252929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252929).length < 2 ^ (prefixWord ++ tailWord_6252929).sum := by decide
  have hdescent : baseEnd_6252929 < baseStart_6252929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252980 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_6252980 : Nat := 118140960795 + 6252980 * 2 ^ 59
def prefixEnd_6252980 : Nat := 4983230072969 + 3 ^ 40 * 6252980 * 2
def baseEnd_6252980 : Nat := 3210784262951050420693075

theorem tailTrace_6252980 : CollatzResearch.WordTrace tailWord_6252980 prefixEnd_6252980 3210784262951050420693075 := by
  unfold tailWord_6252980
  simp only [CollatzResearch.WordTrace]
  refine ⟨114032458443264429403670197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152043277924352572538226929 114032458443264429403670197)
  ·
    refine ⟨10690542979056040256594081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114032458443264429403670197 10690542979056040256594081)
    ·
      refine ⟨8017907234292030192445561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10690542979056040256594081 8017907234292030192445561)
      ·
        refine ⟨6013430425719022644334171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8017907234292030192445561 6013430425719022644334171)
        ·
          refine ⟨9020145638578533966501257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6013430425719022644334171 9020145638578533966501257)
          ·
            refine ⟨6765109228933900474875943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9020145638578533966501257 6765109228933900474875943)
            ·
              refine ⟨10147663843400850712313915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6765109228933900474875943 10147663843400850712313915)
              ·
                refine ⟨15221495765101276068470873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10147663843400850712313915 15221495765101276068470873)
                ·
                  refine ⟨11416121823825957051353155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15221495765101276068470873 11416121823825957051353155)
                  ·
                    refine ⟨17124182735738935577029733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11416121823825957051353155 17124182735738935577029733)
                    ·
                      refine ⟨3210784262951050420693075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17124182735738935577029733 3210784262951050420693075)
                      ·
                        rfl

theorem cell23_6252980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_6252980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252980 prefixEnd_6252980 := by exact prefixLift 6252980
  have htrace : WordTrace (prefixWord ++ tailWord_6252980) baseStart_6252980 baseEnd_6252980 := by
    simpa [prefixWord, tailWord_6252980, baseEnd_6252980] using wordTrace_append hprefix tailTrace_6252980
  have hstable : (prefixWord ++ tailWord_6252980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252980).length < 2 ^ (prefixWord ++ tailWord_6252980).sum := by decide
  have hdescent : baseEnd_6252980 < baseStart_6252980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6252999 : List Nat := [1, 1, 4, 1, 1, 5, 1, 3, 1, 5]
def baseStart_6252999 : Nat := 118140960795 + 6252999 * 2 ^ 59
def prefixEnd_6252999 : Nat := 4983230072969 + 3 ^ 40 * 6252999 * 2
def baseEnd_6252999 : Nat := 1070264673027828615451829

theorem tailTrace_6252999 : CollatzResearch.WordTrace tailWord_6252999 prefixEnd_6252999 1070264673027828615451829 := by
  unfold tailWord_6252999
  simp only [CollatzResearch.WordTrace]
  refine ⟨228065609873460025052282051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152043739915640016701521367 228065609873460025052282051)
  ·
    refine ⟨342098414810190037578423077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228065609873460025052282051 342098414810190037578423077)
    ·
      refine ⟨64143452776910632045954327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 342098414810190037578423077 64143452776910632045954327)
      ·
        refine ⟨96215179165365948068931491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64143452776910632045954327 96215179165365948068931491)
        ·
          refine ⟨144322768748048922103397237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96215179165365948068931491 144322768748048922103397237)
          ·
            refine ⟨13530259570129586447193491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144322768748048922103397237 13530259570129586447193491)
            ·
              refine ⟨20295389355194379670790237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13530259570129586447193491 20295389355194379670790237)
              ·
                refine ⟨7610771008197892376546339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20295389355194379670790237 7610771008197892376546339)
                ·
                  refine ⟨11416156512296838564819509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7610771008197892376546339 11416156512296838564819509)
                  ·
                    refine ⟨1070264673027828615451829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11416156512296838564819509 1070264673027828615451829)
                    ·
                      rfl

theorem cell23_6252999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_6252999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6252999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6252999 prefixEnd_6252999 := by exact prefixLift 6252999
  have htrace : WordTrace (prefixWord ++ tailWord_6252999) baseStart_6252999 baseEnd_6252999 := by
    simpa [prefixWord, tailWord_6252999, baseEnd_6252999] using wordTrace_append hprefix tailTrace_6252999
  have hstable : (prefixWord ++ tailWord_6252999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6252999).length < 2 ^ (prefixWord ++ tailWord_6252999).sum := by decide
  have hdescent : baseEnd_6252999 < baseStart_6252999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6252999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253013 : List Nat := [1, 3, 2, 3, 1, 2, 2, 4, 1, 1, 3]
def baseStart_6253013 : Nat := 118140960795 + 6253013 * 2 ^ 59
def prefixEnd_6253013 : Nat := 4983230072969 + 3 ^ 40 * 6253013 * 2
def baseEnd_6253013 : Nat := 3210801207812648791580423

theorem tailTrace_6253013 : CollatzResearch.WordTrace tailWord_6253013 prefixEnd_6253013 3210801207812648791580423 := by
  unfold tailWord_6253013
  simp only [CollatzResearch.WordTrace]
  refine ⟨228066120495409305443291693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152044080330272870295527795 228066120495409305443291693)
  ·
    refine ⟨85524795185778489541234385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228066120495409305443291693 85524795185778489541234385)
    ·
      refine ⟨64143596389333867155925789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85524795185778489541234385 64143596389333867155925789)
      ·
        refine ⟨24053848646000200183472171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64143596389333867155925789 24053848646000200183472171)
        ·
          refine ⟨36080772969000300275208257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24053848646000200183472171 36080772969000300275208257)
          ·
            refine ⟨27060579726750225206406193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36080772969000300275208257 27060579726750225206406193)
            ·
              refine ⟨20295434795062668904804645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27060579726750225206406193 20295434795062668904804645)
              ·
                refine ⟨3805394024074250419650871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20295434795062668904804645 3805394024074250419650871)
                ·
                  refine ⟨5708091036111375629476307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3805394024074250419650871 5708091036111375629476307)
                  ·
                    refine ⟨8562136554167063444214461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5708091036111375629476307 8562136554167063444214461)
                    ·
                      refine ⟨3210801207812648791580423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8562136554167063444214461 3210801207812648791580423)
                      ·
                        rfl

theorem cell23_6253013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_6253013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253013 prefixEnd_6253013 := by exact prefixLift 6253013
  have htrace : WordTrace (prefixWord ++ tailWord_6253013) baseStart_6253013 baseEnd_6253013 := by
    simpa [prefixWord, tailWord_6253013, baseEnd_6253013] using wordTrace_append hprefix tailTrace_6253013
  have hstable : (prefixWord ++ tailWord_6253013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253013).length < 2 ^ (prefixWord ++ tailWord_6253013).sum := by decide
  have hdescent : baseEnd_6253013 < baseStart_6253013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253036 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 3, 2, 2]
def baseStart_6253036 : Nat := 118140960795 + 6253036 * 2 ^ 59
def prefixEnd_6253036 : Nat := 4983230072969 + 3 ^ 40 * 6253036 * 2
def baseEnd_6253036 : Nat := 3210813017867702201592817

theorem tailTrace_6253036 : CollatzResearch.WordTrace tailWord_6253036 prefixEnd_6253036 3210813017867702201592817 := by
  unfold tailWord_6253036
  simp only [CollatzResearch.WordTrace]
  refine ⟨114033479687162990185689481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152044639582883986914252641 114033479687162990185689481)
  ·
    refine ⟨85525109765372242639267111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114033479687162990185689481 85525109765372242639267111)
    ·
      refine ⟨128287664648058363958900667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85525109765372242639267111 128287664648058363958900667)
      ·
        refine ⟨192431496972087545938351001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128287664648058363958900667 192431496972087545938351001)
        ·
          refine ⟨144323622729065659453763251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192431496972087545938351001 144323622729065659453763251)
          ·
            refine ⟨216485434093598489180644877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144323622729065659453763251 216485434093598489180644877)
            ·
              refine ⟨81182037785099433442741829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216485434093598489180644877 81182037785099433442741829)
              ·
                refine ⟨15221632084706143770514093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81182037785099433442741829 15221632084706143770514093)
                ·
                  refine ⟨5708112031764803913942785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15221632084706143770514093 5708112031764803913942785)
                  ·
                    refine ⟨4281084023823602935457089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5708112031764803913942785 4281084023823602935457089)
                    ·
                      refine ⟨3210813017867702201592817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4281084023823602935457089 3210813017867702201592817)
                      ·
                        rfl

theorem cell23_6253036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 2, 2].length) (baseStart_6253036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253036 prefixEnd_6253036 := by exact prefixLift 6253036
  have htrace : WordTrace (prefixWord ++ tailWord_6253036) baseStart_6253036 baseEnd_6253036 := by
    simpa [prefixWord, tailWord_6253036, baseEnd_6253036] using wordTrace_append hprefix tailTrace_6253036
  have hstable : (prefixWord ++ tailWord_6253036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253036).length < 2 ^ (prefixWord ++ tailWord_6253036).sum := by decide
  have hdescent : baseEnd_6253036 < baseStart_6253036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253070 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2]
def baseStart_6253070 : Nat := 118140960795 + 6253070 * 2 ^ 59
def prefixEnd_6253070 : Nat := 4983230072969 + 3 ^ 40 * 6253070 * 2
def baseEnd_6253070 : Nat := 3210830476209955068567661

theorem tailTrace_6253070 : CollatzResearch.WordTrace tailWord_6253070 prefixEnd_6253070 3210830476209955068567661 := by
  unfold tailWord_6253070
  simp only [CollatzResearch.WordTrace]
  refine ⟨28508524932025350522264583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152045466304135202785411109 28508524932025350522264583)
  ·
    refine ⟨42762787398038025783396875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28508524932025350522264583 42762787398038025783396875)
    ·
      refine ⟨64144181097057038675095313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42762787398038025783396875 64144181097057038675095313)
      ·
        refine ⟨48108135822792779006321485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64144181097057038675095313 48108135822792779006321485)
        ·
          refine ⟨18040550933547292127370557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48108135822792779006321485 18040550933547292127370557)
          ·
            refine ⟨6765206600080234547763959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18040550933547292127370557 6765206600080234547763959)
            ·
              refine ⟨10147809900120351821645939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6765206600080234547763959 10147809900120351821645939)
              ·
                refine ⟨15221714850180527732468909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10147809900120351821645939 15221714850180527732468909)
                ·
                  refine ⟨5708143068817697899675841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15221714850180527732468909 5708143068817697899675841)
                  ·
                    refine ⟨4281107301613273424756881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5708143068817697899675841 4281107301613273424756881)
                    ·
                      refine ⟨3210830476209955068567661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4281107301613273424756881 3210830476209955068567661)
                      ·
                        rfl

theorem cell23_6253070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_6253070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253070 prefixEnd_6253070 := by exact prefixLift 6253070
  have htrace : WordTrace (prefixWord ++ tailWord_6253070) baseStart_6253070 baseEnd_6253070 := by
    simpa [prefixWord, tailWord_6253070, baseEnd_6253070] using wordTrace_append hprefix tailTrace_6253070
  have hstable : (prefixWord ++ tailWord_6253070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253070).length < 2 ^ (prefixWord ++ tailWord_6253070).sum := by decide
  have hdescent : baseEnd_6253070 < baseStart_6253070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253076 : List Nat := [2, 4, 3, 1, 1, 2, 2, 8]
def baseStart_6253076 : Nat := 118140960795 + 6253076 * 2 ^ 59
def prefixEnd_6253076 : Nat := 4983230072969 + 3 ^ 40 * 6253076 * 2
def baseEnd_6253076 : Nat := 118919761373847483151579

theorem tailTrace_6253076 : CollatzResearch.WordTrace tailWord_6253076 prefixEnd_6253076 118919761373847483151579 := by
  unfold tailWord_6253076
  simp only [CollatzResearch.WordTrace]
  refine ⟨114034209147090533601417541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152045612196120711468556721 114034209147090533601417541)
  ·
    refine ⟨21381414215079475050265789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114034209147090533601417541 21381414215079475050265789)
    ·
      refine ⟨8018030330654803143849671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21381414215079475050265789 8018030330654803143849671)
      ·
        refine ⟨12027045495982204715774507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8018030330654803143849671 12027045495982204715774507)
        ·
          refine ⟨18040568243973307073661761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12027045495982204715774507 18040568243973307073661761)
          ·
            refine ⟨13530426182979980305246321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18040568243973307073661761 13530426182979980305246321)
            ·
              refine ⟨10147819637234985228934741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13530426182979980305246321 10147819637234985228934741)
              ·
                refine ⟨118919761373847483151579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10147819637234985228934741 118919761373847483151579)
                ·
                  rfl

theorem cell23_6253076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 8].length) (baseStart_6253076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253076 prefixEnd_6253076 := by exact prefixLift 6253076
  have htrace : WordTrace (prefixWord ++ tailWord_6253076) baseStart_6253076 baseEnd_6253076 := by
    simpa [prefixWord, tailWord_6253076, baseEnd_6253076] using wordTrace_append hprefix tailTrace_6253076
  have hstable : (prefixWord ++ tailWord_6253076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253076).length < 2 ^ (prefixWord ++ tailWord_6253076).sum := by decide
  have hdescent : baseEnd_6253076 < baseStart_6253076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253143 : List Nat := [1, 1, 3, 2, 2, 2, 1, 5, 2, 2, 2]
def baseStart_6253143 : Nat := 118140960795 + 6253143 * 2 ^ 59
def prefixEnd_6253143 : Nat := 4983230072969 + 3 ^ 40 * 6253143 * 2
def baseEnd_6253143 : Nat := 3210867960297733282954825

theorem tailTrace_6253143 : CollatzResearch.WordTrace tailWord_6253143 prefixEnd_6253143 3210867960297733282954825 := by
  unfold tailWord_6253143
  simp only [CollatzResearch.WordTrace]
  refine ⟨228070861984938337645524083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152047241323292225097016055 228070861984938337645524083)
  ·
    refine ⟨342106292977407506468286125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228070861984938337645524083 342106292977407506468286125)
    ·
      refine ⟨128289859866527814925607297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342106292977407506468286125 128289859866527814925607297)
      ·
        refine ⟨96217394899895861194205473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128289859866527814925607297 96217394899895861194205473)
        ·
          refine ⟨72163046174921895895654105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96217394899895861194205473 72163046174921895895654105)
          ·
            refine ⟨54122284631191421921740579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72163046174921895895654105 54122284631191421921740579)
            ·
              refine ⟨81183426946787132882610869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54122284631191421921740579 81183426946787132882610869)
              ·
                refine ⟨7610946276261293707744769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81183426946787132882610869 7610946276261293707744769)
                ·
                  refine ⟨5708209707195970280808577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7610946276261293707744769 5708209707195970280808577)
                  ·
                    refine ⟨4281157280396977710606433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5708209707195970280808577 4281157280396977710606433)
                    ·
                      refine ⟨3210867960297733282954825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4281157280396977710606433 3210867960297733282954825)
                      ·
                        rfl

theorem cell23_6253143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_6253143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253143 prefixEnd_6253143 := by exact prefixLift 6253143
  have htrace : WordTrace (prefixWord ++ tailWord_6253143) baseStart_6253143 baseEnd_6253143 := by
    simpa [prefixWord, tailWord_6253143, baseEnd_6253143] using wordTrace_append hprefix tailTrace_6253143
  have hstable : (prefixWord ++ tailWord_6253143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253143).length < 2 ^ (prefixWord ++ tailWord_6253143).sum := by decide
  have hdescent : baseEnd_6253143 < baseStart_6253143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253159 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_6253159 : Nat := 118140960795 + 6253159 * 2 ^ 59
def prefixEnd_6253159 : Nat := 4983230072969 + 3 ^ 40 * 6253159 * 2
def baseEnd_6253159 : Nat := 3210876175988205220354751

theorem tailTrace_6253159 : CollatzResearch.WordTrace tailWord_6253159 prefixEnd_6253159 3210876175988205220354751 := by
  unfold tailWord_6253159
  simp only [CollatzResearch.WordTrace]
  refine ⟨228071445552880372378106531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152047630368586914918737687 228071445552880372378106531)
  ·
    refine ⟨342107168329320558567159797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228071445552880372378106531 342107168329320558567159797)
    ·
      refine ⟨32072547030873802365671231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 342107168329320558567159797 32072547030873802365671231)
      ·
        refine ⟨48108820546310703548506847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32072547030873802365671231 48108820546310703548506847)
        ·
          refine ⟨72163230819466055322760271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48108820546310703548506847 72163230819466055322760271)
          ·
            refine ⟨108244846229199082984140407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72163230819466055322760271 108244846229199082984140407)
            ·
              refine ⟨162367269343798624476210611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108244846229199082984140407 162367269343798624476210611)
              ·
                refine ⟨243550904015697936714315917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162367269343798624476210611 243550904015697936714315917)
                ·
                  refine ⟨91331589005886726267868469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243550904015697936714315917 91331589005886726267868469)
                  ·
                    refine ⟨8562336469301880587612669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91331589005886726267868469 8562336469301880587612669)
                    ·
                      refine ⟨3210876175988205220354751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8562336469301880587612669 3210876175988205220354751)
                      ·
                        rfl

theorem cell23_6253159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_6253159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253159 prefixEnd_6253159 := by exact prefixLift 6253159
  have htrace : WordTrace (prefixWord ++ tailWord_6253159) baseStart_6253159 baseEnd_6253159 := by
    simpa [prefixWord, tailWord_6253159, baseEnd_6253159] using wordTrace_append hprefix tailTrace_6253159
  have hstable : (prefixWord ++ tailWord_6253159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253159).length < 2 ^ (prefixWord ++ tailWord_6253159).sum := by decide
  have hdescent : baseEnd_6253159 < baseStart_6253159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253199 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 4]
def baseStart_6253199 : Nat := 118140960795 + 6253199 * 2 ^ 59
def prefixEnd_6253199 : Nat := 4983230072969 + 3 ^ 40 * 6253199 * 2
def baseEnd_6253199 : Nat := 3210896715214385063854567

theorem tailTrace_6253199 : CollatzResearch.WordTrace tailWord_6253199 prefixEnd_6253199 3210896715214385063854567 := by
  unfold tailWord_6253199
  simp only [CollatzResearch.WordTrace]
  refine ⟨228072904472735459209562651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152048602981823639473041767 228072904472735459209562651)
  ·
    refine ⟨342109356709103188814343977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228072904472735459209562651 342109356709103188814343977)
    ·
      refine ⟨256582017531827391610757983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342109356709103188814343977 256582017531827391610757983)
      ·
        refine ⟨384873026297741087416136975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256582017531827391610757983 384873026297741087416136975)
        ·
          refine ⟨577309539446611631124205463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384873026297741087416136975 577309539446611631124205463)
          ·
            refine ⟨865964309169917446686308195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577309539446611631124205463 865964309169917446686308195)
            ·
              refine ⟨1298946463754876170029462293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865964309169917446686308195 1298946463754876170029462293)
              ·
                refine ⟨60888115488509820470131045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1298946463754876170029462293 60888115488509820470131045)
                ·
                  refine ⟨11416521654095591338149571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60888115488509820470131045 11416521654095591338149571)
                  ·
                    refine ⟨17124782481143387007224357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11416521654095591338149571 17124782481143387007224357)
                    ·
                      refine ⟨3210896715214385063854567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17124782481143387007224357 3210896715214385063854567)
                      ·
                        rfl

theorem cell23_6253199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_6253199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253199 prefixEnd_6253199 := by exact prefixLift 6253199
  have htrace : WordTrace (prefixWord ++ tailWord_6253199) baseStart_6253199 baseEnd_6253199 := by
    simpa [prefixWord, tailWord_6253199, baseEnd_6253199] using wordTrace_append hprefix tailTrace_6253199
  have hstable : (prefixWord ++ tailWord_6253199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253199).length < 2 ^ (prefixWord ++ tailWord_6253199).sum := by decide
  have hdescent : baseEnd_6253199 < baseStart_6253199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253256 : List Nat := [2, 1, 3, 1, 2, 4, 1, 3, 6]
def baseStart_6253256 : Nat := 118140960795 + 6253256 * 2 ^ 59
def prefixEnd_6253256 : Nat := 4983230072969 + 3 ^ 40 * 6253256 * 2
def baseEnd_6253256 : Nat := 356769553734632371204645

theorem tailTrace_6253256 : CollatzResearch.WordTrace tailWord_6253256 prefixEnd_6253256 356769553734632371204645 := by
  unfold tailWord_6253256
  simp only [CollatzResearch.WordTrace]
  refine ⟨114037491716764478972193811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152049988955685971962925081 114037491716764478972193811)
  ·
    refine ⟨171056237575146718458290717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114037491716764478972193811 171056237575146718458290717)
    ·
      refine ⟨64146089090680019421859019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171056237575146718458290717 64146089090680019421859019)
      ·
        refine ⟨96219133636020029132788529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64146089090680019421859019 96219133636020029132788529)
        ·
          refine ⟨72164350227015021849591397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96219133636020029132788529 72164350227015021849591397)
          ·
            refine ⟨13530815667565316596798387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72164350227015021849591397 13530815667565316596798387)
            ·
              refine ⟨20296223501347974895197581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13530815667565316596798387 20296223501347974895197581)
              ·
                refine ⟨7611083813005490585699093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20296223501347974895197581 7611083813005490585699093)
                ·
                  refine ⟨356769553734632371204645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7611083813005490585699093 356769553734632371204645)
                  ·
                    rfl

theorem cell23_6253256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 6].length) (baseStart_6253256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253256 prefixEnd_6253256 := by exact prefixLift 6253256
  have htrace : WordTrace (prefixWord ++ tailWord_6253256) baseStart_6253256 baseEnd_6253256 := by
    simpa [prefixWord, tailWord_6253256, baseEnd_6253256] using wordTrace_append hprefix tailTrace_6253256
  have hstable : (prefixWord ++ tailWord_6253256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253256).length < 2 ^ (prefixWord ++ tailWord_6253256).sum := by decide
  have hdescent : baseEnd_6253256 < baseStart_6253256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253299 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 5, 6]
def baseStart_6253299 : Nat := 118140960795 + 6253299 * 2 ^ 59
def prefixEnd_6253299 : Nat := 4983230072969 + 3 ^ 40 * 6253299 * 2
def baseEnd_6253299 : Nat := 1070316021093278224201369

theorem tailTrace_6253299 : CollatzResearch.WordTrace tailWord_6253299 prefixEnd_6253299 1070316021093278224201369 := by
  unfold tailWord_6253299
  simp only [CollatzResearch.WordTrace]
  refine ⟨228076551772373176288202951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152051034514915450858801967 228076551772373176288202951)
  ·
    refine ⟨342114827658559764432304427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228076551772373176288202951 342114827658559764432304427)
    ·
      refine ⟨513172241487839646648456641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342114827658559764432304427 513172241487839646648456641)
      ·
        refine ⟨384879181115879734986342481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513172241487839646648456641 384879181115879734986342481)
        ·
          refine ⟨288659385836909801239756861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384879181115879734986342481 288659385836909801239756861)
          ·
            refine ⟨108247269688841175464908823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288659385836909801239756861 108247269688841175464908823)
            ·
              refine ⟨162370904533261763197363235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108247269688841175464908823 162370904533261763197363235)
              ·
                refine ⟨243556356799892644796044853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162370904533261763197363235 243556356799892644796044853)
                ·
                  refine ⟨22833408449989935449629205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243556356799892644796044853 22833408449989935449629205)
                  ·
                    refine ⟨1070316021093278224201369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22833408449989935449629205 1070316021093278224201369)
                    ·
                      rfl

theorem cell23_6253299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 6].length) (baseStart_6253299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253299 prefixEnd_6253299 := by exact prefixLift 6253299
  have htrace : WordTrace (prefixWord ++ tailWord_6253299) baseStart_6253299 baseEnd_6253299 := by
    simpa [prefixWord, tailWord_6253299, baseEnd_6253299] using wordTrace_append hprefix tailTrace_6253299
  have hstable : (prefixWord ++ tailWord_6253299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253299).length < 2 ^ (prefixWord ++ tailWord_6253299).sum := by decide
  have hdescent : baseEnd_6253299 < baseStart_6253299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253306 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4]
def baseStart_6253306 : Nat := 118140960795 + 6253306 * 2 ^ 59
def prefixEnd_6253306 : Nat := 4983230072969 + 3 ^ 40 * 6253306 * 2
def baseEnd_6253306 : Nat := 3210951657644416145216575

theorem tailTrace_6253306 : CollatzResearch.WordTrace tailWord_6253306 prefixEnd_6253306 3210951657644416145216575 := by
  unfold tailWord_6253306
  simp only [CollatzResearch.WordTrace]
  refine ⟨57019201770836954120926943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152051204722231877655805181 57019201770836954120926943)
  ·
    refine ⟨85528802656255431181390415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57019201770836954120926943 85528802656255431181390415)
    ·
      refine ⟨128293203984383146772085623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85528802656255431181390415 128293203984383146772085623)
      ·
        refine ⟨192439805976574720158128435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128293203984383146772085623 192439805976574720158128435)
        ·
          refine ⟨288659708964862080237192653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192439805976574720158128435 288659708964862080237192653)
          ·
            refine ⟨108247390861823280088947245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288659708964862080237192653 108247390861823280088947245)
            ·
              refine ⟨40592771573183730033355217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108247390861823280088947245 40592771573183730033355217)
              ·
                refine ⟨30444578679887797525016413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40592771573183730033355217 30444578679887797525016413)
                ·
                  refine ⟨11416717004957924071881155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30444578679887797525016413 11416717004957924071881155)
                  ·
                    refine ⟨17125075507436886107821733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11416717004957924071881155 17125075507436886107821733)
                    ·
                      refine ⟨3210951657644416145216575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17125075507436886107821733 3210951657644416145216575)
                      ·
                        rfl

theorem cell23_6253306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_6253306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253306 prefixEnd_6253306 := by exact prefixLift 6253306
  have htrace : WordTrace (prefixWord ++ tailWord_6253306) baseStart_6253306 baseEnd_6253306 := by
    simpa [prefixWord, tailWord_6253306, baseEnd_6253306] using wordTrace_append hprefix tailTrace_6253306
  have hstable : (prefixWord ++ tailWord_6253306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253306).length < 2 ^ (prefixWord ++ tailWord_6253306).sum := by decide
  have hdescent : baseEnd_6253306 < baseStart_6253306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253329 : List Nat := [1, 2, 2, 1, 1, 3, 2, 11]
def baseStart_6253329 : Nat := 118140960795 + 6253329 * 2 ^ 59
def prefixEnd_6253329 : Nat := 4983230072969 + 3 ^ 40 * 6253329 * 2
def baseEnd_6253329 : Nat := 118924572877758131675147

theorem tailTrace_6253329 : CollatzResearch.WordTrace tailWord_6253329 prefixEnd_6253329 118924572877758131675147 := by
  unfold tailWord_6253329
  simp only [CollatzResearch.WordTrace]
  refine ⟨228077645962264491411795041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152051763974842994274530027 228077645962264491411795041)
  ·
    refine ⟨171058234471698368558846281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228077645962264491411795041 171058234471698368558846281)
    ·
      refine ⟨128293675853773776419134711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171058234471698368558846281 128293675853773776419134711)
      ·
        refine ⟨192440513780660664628702067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128293675853773776419134711 192440513780660664628702067)
        ·
          refine ⟨288660770670990996943053101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192440513780660664628702067 288660770670990996943053101)
          ·
            refine ⟨108247789001621623853644913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288660770670990996943053101 108247789001621623853644913)
            ·
              refine ⟨81185841751216217890233685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108247789001621623853644913 81185841751216217890233685)
              ·
                refine ⟨118924572877758131675147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 81185841751216217890233685 118924572877758131675147)
                ·
                  rfl

theorem cell23_6253329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 11].length) (baseStart_6253329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253329 prefixEnd_6253329 := by exact prefixLift 6253329
  have htrace : WordTrace (prefixWord ++ tailWord_6253329) baseStart_6253329 baseEnd_6253329 := by
    simpa [prefixWord, tailWord_6253329, baseEnd_6253329] using wordTrace_append hprefix tailTrace_6253329
  have hstable : (prefixWord ++ tailWord_6253329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253329).length < 2 ^ (prefixWord ++ tailWord_6253329).sum := by decide
  have hdescent : baseEnd_6253329 < baseStart_6253329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253340 : List Nat := [2, 2, 3, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_6253340 : Nat := 118140960795 + 6253340 * 2 ^ 59
def prefixEnd_6253340 : Nat := 4983230072969 + 3 ^ 40 * 6253340 * 2
def baseEnd_6253340 : Nat := 3210969115986669012191419

theorem tailTrace_6253340 : CollatzResearch.WordTrace tailWord_6253340 prefixEnd_6253340 3210969115986669012191419 := by
  unfold tailWord_6253340
  simp only [CollatzResearch.WordTrace]
  refine ⟨114039023582612320145222737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152052031443483093526963649 114039023582612320145222737)
  ·
    refine ⟨85529267686959240108917053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114039023582612320145222737 85529267686959240108917053)
    ·
      refine ⟨32073475382609715040843895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85529267686959240108917053 32073475382609715040843895)
      ·
        refine ⟨48110213073914572561265843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32073475382609715040843895 48110213073914572561265843)
        ·
          refine ⟨72165319610871858841898765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48110213073914572561265843 72165319610871858841898765)
          ·
            refine ⟨27061994854076947065712037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72165319610871858841898765 27061994854076947065712037)
            ·
              refine ⟨5074124035139427574821007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27061994854076947065712037 5074124035139427574821007)
              ·
                refine ⟨7611186052709141362231511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5074124035139427574821007 7611186052709141362231511)
                ·
                  refine ⟨11416779079063712043347267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7611186052709141362231511 11416779079063712043347267)
                  ·
                    refine ⟨17125168618595568065020901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11416779079063712043347267 17125168618595568065020901)
                    ·
                      refine ⟨3210969115986669012191419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17125168618595568065020901 3210969115986669012191419)
                      ·
                        rfl

theorem cell23_6253340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_6253340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253340 prefixEnd_6253340 := by exact prefixLift 6253340
  have htrace : WordTrace (prefixWord ++ tailWord_6253340) baseStart_6253340 baseEnd_6253340 := by
    simpa [prefixWord, tailWord_6253340, baseEnd_6253340] using wordTrace_append hprefix tailTrace_6253340
  have hstable : (prefixWord ++ tailWord_6253340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253340).length < 2 ^ (prefixWord ++ tailWord_6253340).sum := by decide
  have hdescent : baseEnd_6253340 < baseStart_6253340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253346 : List Nat := [3, 3, 1, 1, 2, 3, 10]
def baseStart_6253346 : Nat := 118140960795 + 6253346 * 2 ^ 59
def prefixEnd_6253346 : Nat := 4983230072969 + 3 ^ 40 * 6253346 * 2
def baseEnd_6253346 : Nat := 39641632060130814675511

theorem tailTrace_6253346 : CollatzResearch.WordTrace tailWord_6253346 prefixEnd_6253346 39641632060130814675511 := by
  unfold tailWord_6253346
  simp only [CollatzResearch.WordTrace]
  refine ⟨57019566500800725828790973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152052177335468602210109261 57019566500800725828790973)
  ·
    refine ⟨21382337437800272185796615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57019566500800725828790973 21382337437800272185796615)
    ·
      refine ⟨32073506156700408278694923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21382337437800272185796615 32073506156700408278694923)
      ·
        refine ⟨48110259235050612418042385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32073506156700408278694923 48110259235050612418042385)
        ·
          refine ⟨36082694426287959313531789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48110259235050612418042385 36082694426287959313531789)
          ·
            refine ⟨13531010409857984742574421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36082694426287959313531789 13531010409857984742574421)
            ·
              refine ⟨39641632060130814675511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13531010409857984742574421 39641632060130814675511)
              ·
                rfl

theorem cell23_6253346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 10].length) (baseStart_6253346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253346 prefixEnd_6253346 := by exact prefixLift 6253346
  have htrace : WordTrace (prefixWord ++ tailWord_6253346) baseStart_6253346 baseEnd_6253346 := by
    simpa [prefixWord, tailWord_6253346, baseEnd_6253346] using wordTrace_append hprefix tailTrace_6253346
  have hstable : (prefixWord ++ tailWord_6253346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253346).length < 2 ^ (prefixWord ++ tailWord_6253346).sum := by decide
  have hdescent : baseEnd_6253346 < baseStart_6253346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253370 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4]
def baseStart_6253370 : Nat := 118140960795 + 6253370 * 2 ^ 59
def prefixEnd_6253370 : Nat := 4983230072969 + 3 ^ 40 * 6253370 * 2
def baseEnd_6253370 : Nat := 3210984520406303894816281

theorem tailTrace_6253370 : CollatzResearch.WordTrace tailWord_6253370 prefixEnd_6253370 3210984520406303894816281 := by
  unfold tailWord_6253370
  simp only [CollatzResearch.WordTrace]
  refine ⟨57019785338778988853509391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152052760903410636942691709 57019785338778988853509391)
  ·
    refine ⟨85529678008168483280264087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57019785338778988853509391 85529678008168483280264087)
    ·
      refine ⟨128294517012252724920396131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85529678008168483280264087 128294517012252724920396131)
      ·
        refine ⟨192441775518379087380594197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128294517012252724920396131 192441775518379087380594197)
        ·
          refine ⟨9020708227424019720965353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 192441775518379087380594197 9020708227424019720965353)
          ·
            refine ⟨6765531170568014790724015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9020708227424019720965353 6765531170568014790724015)
            ·
              refine ⟨10148296755852022186086023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6765531170568014790724015 10148296755852022186086023)
              ·
                refine ⟨15222445133778033279129035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10148296755852022186086023 15222445133778033279129035)
                ·
                  refine ⟨22833667700667049918693553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15222445133778033279129035 22833667700667049918693553)
                  ·
                    refine ⟨17125250775500287439020165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22833667700667049918693553 17125250775500287439020165)
                    ·
                      refine ⟨3210984520406303894816281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17125250775500287439020165 3210984520406303894816281)
                      ·
                        rfl

theorem cell23_6253370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_6253370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253370 prefixEnd_6253370 := by exact prefixLift 6253370
  have htrace : WordTrace (prefixWord ++ tailWord_6253370) baseStart_6253370 baseEnd_6253370 := by
    simpa [prefixWord, tailWord_6253370, baseEnd_6253370] using wordTrace_append hprefix tailTrace_6253370
  have hstable : (prefixWord ++ tailWord_6253370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253370).length < 2 ^ (prefixWord ++ tailWord_6253370).sum := by decide
  have hdescent : baseEnd_6253370 < baseStart_6253370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253380 : List Nat := [2, 3, 4, 2, 1, 1, 1, 9]
def baseStart_6253380 : Nat := 118140960795 + 6253380 * 2 ^ 59
def prefixEnd_6253380 : Nat := 4983230072969 + 3 ^ 40 * 6253380 * 2
def baseEnd_6253380 : Nat := 118925542785661068729305

theorem tailTrace_6253380 : CollatzResearch.WordTrace tailWord_6253380 prefixEnd_6253380 118925542785661068729305 := by
  unfold tailWord_6253380
  simp only [CollatzResearch.WordTrace]
  refine ⟨114039753042539863560950797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152053004056719818081267729 114039753042539863560950797)
  ·
    refine ⟨42764907390952448835356549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114039753042539863560950797 42764907390952448835356549)
    ·
      refine ⟨8018420135803584156629353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42764907390952448835356549 8018420135803584156629353)
      ·
        refine ⟨6013815101852688117472015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8018420135803584156629353 6013815101852688117472015)
        ·
          refine ⟨9020722652779032176208023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6013815101852688117472015 9020722652779032176208023)
          ·
            refine ⟨13531083979168548264312035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9020722652779032176208023 13531083979168548264312035)
            ·
              refine ⟨20296625968752822396468053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13531083979168548264312035 20296625968752822396468053)
              ·
                refine ⟨118925542785661068729305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20296625968752822396468053 118925542785661068729305)
                ·
                  rfl

theorem cell23_6253380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 9].length) (baseStart_6253380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253380 prefixEnd_6253380 := by exact prefixLift 6253380
  have htrace : WordTrace (prefixWord ++ tailWord_6253380) baseStart_6253380 baseEnd_6253380 := by
    simpa [prefixWord, tailWord_6253380, baseEnd_6253380] using wordTrace_append hprefix tailTrace_6253380
  have hstable : (prefixWord ++ tailWord_6253380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253380).length < 2 ^ (prefixWord ++ tailWord_6253380).sum := by decide
  have hdescent : baseEnd_6253380 < baseStart_6253380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253436 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 7]
def baseStart_6253436 : Nat := 118140960795 + 6253436 * 2 ^ 59
def prefixEnd_6253436 : Nat := 4983230072969 + 3 ^ 40 * 6253436 * 2
def baseEnd_6253436 : Nat := 356779823347722292954553

theorem tailTrace_6253436 : CollatzResearch.WordTrace tailWord_6253436 prefixEnd_6253436 356779823347722292954553 := by
  unfold tailWord_6253436
  simp only [CollatzResearch.WordTrace]
  refine ⟨114040774286438424342970081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152054365715251232457293441 114040774286438424342970081)
  ·
    refine ⟨85530580714828818257227561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114040774286438424342970081 85530580714828818257227561)
    ·
      refine ⟨64147935536121613692920671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85530580714828818257227561 64147935536121613692920671)
      ·
        refine ⟨96221903304182420539381007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64147935536121613692920671 96221903304182420539381007)
        ·
          refine ⟨144332854956273630809071511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96221903304182420539381007 144332854956273630809071511)
          ·
            refine ⟨216499282434410446213607267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144332854956273630809071511 216499282434410446213607267)
            ·
              refine ⟨324748923651615669320410901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216499282434410446213607267 324748923651615669320410901)
              ·
                refine ⟨15222605796169484499394261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 324748923651615669320410901 15222605796169484499394261)
                ·
                  refine ⟨356779823347722292954553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15222605796169484499394261 356779823347722292954553)
                  ·
                    rfl

theorem cell23_6253436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_6253436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253436 prefixEnd_6253436 := by exact prefixLift 6253436
  have htrace : WordTrace (prefixWord ++ tailWord_6253436) baseStart_6253436 baseEnd_6253436 := by
    simpa [prefixWord, tailWord_6253436, baseEnd_6253436] using wordTrace_append hprefix tailTrace_6253436
  have hstable : (prefixWord ++ tailWord_6253436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253436).length < 2 ^ (prefixWord ++ tailWord_6253436).sum := by decide
  have hdescent : baseEnd_6253436 < baseStart_6253436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253463 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 3]
def baseStart_6253463 : Nat := 118140960795 + 6253463 * 2 ^ 59
def prefixEnd_6253463 : Nat := 4983230072969 + 3 ^ 40 * 6253463 * 2
def baseEnd_6253463 : Nat := 3211032274107172030953353

theorem tailTrace_6253463 : CollatzResearch.WordTrace tailWord_6253463 prefixEnd_6253463 3211032274107172030953353 := by
  unfold tailWord_6253463
  simp only [CollatzResearch.WordTrace]
  refine ⟨228082533343779032297173043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152055022229186021531448695 228082533343779032297173043)
  ·
    refine ⟨342123800015668548445759565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228082533343779032297173043 342123800015668548445759565)
    ·
      refine ⟨128296425005875705667159837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342123800015668548445759565 128296425005875705667159837)
      ·
        refine ⟨48111159377203389625184939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128296425005875705667159837 48111159377203389625184939)
        ·
          refine ⟨72166739065805084437777409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48111159377203389625184939 72166739065805084437777409)
          ·
            refine ⟨54125054299353813328333057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72166739065805084437777409 54125054299353813328333057)
            ·
              refine ⟨40593790724515359996249793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54125054299353813328333057 40593790724515359996249793)
              ·
                refine ⟨30445343043386519997187345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40593790724515359996249793 30445343043386519997187345)
                ·
                  refine ⟨22834007282539889997890509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30445343043386519997187345 22834007282539889997890509)
                  ·
                    refine ⟨8562752730952458749208941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22834007282539889997890509 8562752730952458749208941)
                    ·
                      refine ⟨3211032274107172030953353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8562752730952458749208941 3211032274107172030953353)
                      ·
                        rfl

theorem cell23_6253463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_6253463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253463 prefixEnd_6253463 := by exact prefixLift 6253463
  have htrace : WordTrace (prefixWord ++ tailWord_6253463) baseStart_6253463 baseEnd_6253463 := by
    simpa [prefixWord, tailWord_6253463, baseEnd_6253463] using wordTrace_append hprefix tailTrace_6253463
  have hstable : (prefixWord ++ tailWord_6253463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253463).length < 2 ^ (prefixWord ++ tailWord_6253463).sum := by decide
  have hdescent : baseEnd_6253463 < baseStart_6253463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253503 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 4]
def baseStart_6253503 : Nat := 118140960795 + 6253503 * 2 ^ 59
def prefixEnd_6253503 : Nat := 4983230072969 + 3 ^ 40 * 6253503 * 2
def baseEnd_6253503 : Nat := 3211052813333351874453169

theorem tailTrace_6253503 : CollatzResearch.WordTrace tailWord_6253503 prefixEnd_6253503 3211052813333351874453169 := by
  unfold tailWord_6253503
  simp only [CollatzResearch.WordTrace]
  refine ⟨228083992263634119128629163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152055994842422746085752775 228083992263634119128629163)
  ·
    refine ⟨342125988395451178692943745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228083992263634119128629163 342125988395451178692943745)
    ·
      refine ⟨256594491296588384019707809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342125988395451178692943745 256594491296588384019707809)
      ·
        refine ⟨192445868472441288014780857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256594491296588384019707809 192445868472441288014780857)
        ·
          refine ⟨144334401354330966011085643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192445868472441288014780857 144334401354330966011085643)
          ·
            refine ⟨216501602031496449016628465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144334401354330966011085643 216501602031496449016628465)
            ·
              refine ⟨162376201523622336762471349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216501602031496449016628465 162376201523622336762471349)
              ·
                refine ⟨15222768892839594071481689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162376201523622336762471349 15222768892839594071481689)
                ·
                  refine ⟨11417076669629695553611267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15222768892839594071481689 11417076669629695553611267)
                  ·
                    refine ⟨17125615004444543330416901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11417076669629695553611267 17125615004444543330416901)
                    ·
                      refine ⟨3211052813333351874453169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17125615004444543330416901 3211052813333351874453169)
                      ·
                        rfl

theorem cell23_6253503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_6253503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253503 prefixEnd_6253503 := by exact prefixLift 6253503
  have htrace : WordTrace (prefixWord ++ tailWord_6253503) baseStart_6253503 baseEnd_6253503 := by
    simpa [prefixWord, tailWord_6253503, baseEnd_6253503] using wordTrace_append hprefix tailTrace_6253503
  have hstable : (prefixWord ++ tailWord_6253503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253503).length < 2 ^ (prefixWord ++ tailWord_6253503).sum := by decide
  have hdescent : baseEnd_6253503 < baseStart_6253503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253530 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 3, 4]
def baseStart_6253530 : Nat := 118140960795 + 6253530 * 2 ^ 59
def prefixEnd_6253530 : Nat := 4983230072969 + 3 ^ 40 * 6253530 * 2
def baseEnd_6253530 : Nat := 1070355559103674422938515

theorem tailTrace_6253530 : CollatzResearch.WordTrace tailWord_6253530 prefixEnd_6253530 1070355559103674422938515 := by
  unfold tailWord_6253530
  simp only [CollatzResearch.WordTrace]
  refine ⟨57021244258634075684965511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152056651356357535159908029 57021244258634075684965511)
  ·
    refine ⟨85531866387951113527448267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57021244258634075684965511 85531866387951113527448267)
    ·
      refine ⟨128297799581926670291172401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85531866387951113527448267 128297799581926670291172401)
      ·
        refine ⟨96223349686445002718379301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128297799581926670291172401 96223349686445002718379301)
        ·
          refine ⟨18041878066208438009696119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96223349686445002718379301 18041878066208438009696119)
          ·
            refine ⟨27062817099312657014544179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18041878066208438009696119 27062817099312657014544179)
            ·
              refine ⟨40594225648968985521816269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27062817099312657014544179 40594225648968985521816269)
              ·
                refine ⟨15222834618363369570681101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40594225648968985521816269 15222834618363369570681101)
                ·
                  refine ⟨5708562981886263589005413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15222834618363369570681101 5708562981886263589005413)
                  ·
                    refine ⟨1070355559103674422938515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5708562981886263589005413 1070355559103674422938515)
                    ·
                      rfl

theorem cell23_6253530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_6253530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253530 prefixEnd_6253530 := by exact prefixLift 6253530
  have htrace : WordTrace (prefixWord ++ tailWord_6253530) baseStart_6253530 baseEnd_6253530 := by
    simpa [prefixWord, tailWord_6253530, baseEnd_6253530] using wordTrace_append hprefix tailTrace_6253530
  have hstable : (prefixWord ++ tailWord_6253530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253530).length < 2 ^ (prefixWord ++ tailWord_6253530).sum := by decide
  have hdescent : baseEnd_6253530 < baseStart_6253530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253564 : List Nat := [2, 2, 2, 1, 2, 5, 1, 3, 1, 4]
def baseStart_6253564 : Nat := 118140960795 + 6253564 * 2 ^ 59
def prefixEnd_6253564 : Nat := 4983230072969 + 3 ^ 40 * 6253564 * 2
def baseEnd_6253564 : Nat := 1070361378551092045263463

theorem tailTrace_6253564 : CollatzResearch.WordTrace tailWord_6253564 prefixEnd_6253564 1070361378551092045263463 := by
  unfold tailWord_6253564
  simp only [CollatzResearch.WordTrace]
  refine ⟨114043108558206563273299873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152057478077608751031066497 114043108558206563273299873)
  ·
    refine ⟨85532331418654922454974905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114043108558206563273299873 85532331418654922454974905)
    ·
      refine ⟨64149248563991191841231179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85532331418654922454974905 64149248563991191841231179)
      ·
        refine ⟨96223872845986787761846769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64149248563991191841231179 96223872845986787761846769)
        ·
          refine ⟨72167904634490090821385077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96223872845986787761846769 72167904634490090821385077)
          ·
            refine ⟨6765741059483446014504851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72167904634490090821385077 6765741059483446014504851)
            ·
              refine ⟨10148611589225169021757277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6765741059483446014504851 10148611589225169021757277)
              ·
                refine ⟨3805729345959438383158979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10148611589225169021757277 3805729345959438383158979)
                ·
                  refine ⟨5708594018939157574738469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3805729345959438383158979 5708594018939157574738469)
                  ·
                    refine ⟨1070361378551092045263463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5708594018939157574738469 1070361378551092045263463)
                    ·
                      rfl

theorem cell23_6253564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_6253564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253564 prefixEnd_6253564 := by exact prefixLift 6253564
  have htrace : WordTrace (prefixWord ++ tailWord_6253564) baseStart_6253564 baseEnd_6253564 := by
    simpa [prefixWord, tailWord_6253564, baseEnd_6253564] using wordTrace_append hprefix tailTrace_6253564
  have hstable : (prefixWord ++ tailWord_6253564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253564).length < 2 ^ (prefixWord ++ tailWord_6253564).sum := by decide
  have hdescent : baseEnd_6253564 < baseStart_6253564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253607 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 3, 5]
def baseStart_6253607 : Nat := 118140960795 + 6253607 * 2 ^ 59
def prefixEnd_6253607 : Nat := 4983230072969 + 3 ^ 40 * 6253607 * 2
def baseEnd_6253607 : Nat := 1070368738440473155850897

theorem tailTrace_6253607 : CollatzResearch.WordTrace tailWord_6253607 prefixEnd_6253607 1070368738440473155850897 := by
  unfold tailWord_6253607
  simp only [CollatzResearch.WordTrace]
  refine ⟨228087785455257344890415075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152058523636838229926943383 228087785455257344890415075)
  ·
    refine ⟨342131678182886017335622613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228087785455257344890415075 342131678182886017335622613)
    ·
      refine ⟨8018711207411391031303655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 342131678182886017335622613 8018711207411391031303655)
      ·
        refine ⟨12028066811117086546955483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8018711207411391031303655 12028066811117086546955483)
        ·
          refine ⟨18042100216675629820433225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12028066811117086546955483 18042100216675629820433225)
          ·
            refine ⟨13531575162506722365324919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18042100216675629820433225 13531575162506722365324919)
            ·
              refine ⟨20297362743760083547987379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13531575162506722365324919 20297362743760083547987379)
              ·
                refine ⟨30446044115640125321981069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20297362743760083547987379 30446044115640125321981069)
                ·
                  refine ⟨11417266543365046995742901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30446044115640125321981069 11417266543365046995742901)
                  ·
                    refine ⟨1070368738440473155850897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11417266543365046995742901 1070368738440473155850897)
                    ·
                      rfl

theorem cell23_6253607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_6253607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253607 prefixEnd_6253607 := by exact prefixLift 6253607
  have htrace : WordTrace (prefixWord ++ tailWord_6253607) baseStart_6253607 baseEnd_6253607 := by
    simpa [prefixWord, tailWord_6253607, baseEnd_6253607] using wordTrace_append hprefix tailTrace_6253607
  have hstable : (prefixWord ++ tailWord_6253607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253607).length < 2 ^ (prefixWord ++ tailWord_6253607).sum := by decide
  have hdescent : baseEnd_6253607 < baseStart_6253607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253614 : List Nat := [4, 1, 3, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_6253614 : Nat := 118140960795 + 6253614 * 2 ^ 59
def prefixEnd_6253614 : Nat := 4983230072969 + 3 ^ 40 * 6253614 * 2
def baseEnd_6253614 : Nat := 3211109809686000940165159

theorem tailTrace_6253614 : CollatzResearch.WordTrace tailWord_6253614 prefixEnd_6253614 3211109809686000940165159 := by
  unfold tailWord_6253614
  simp only [CollatzResearch.WordTrace]
  refine ⟨28511005095778998135739987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152058693844154656723946597 28511005095778998135739987)
  ·
    refine ⟨42766507643668497203609981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28511005095778998135739987 42766507643668497203609981)
    ·
      refine ⟨16037440366375686451353743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42766507643668497203609981 16037440366375686451353743)
      ·
        refine ⟨24056160549563529677030615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16037440366375686451353743 24056160549563529677030615)
        ·
          refine ⟨36084240824345294515545923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24056160549563529677030615 36084240824345294515545923)
          ·
            refine ⟨54126361236517941773318885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36084240824345294515545923 54126361236517941773318885)
            ·
              refine ⟨10148692731847114082497291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54126361236517941773318885 10148692731847114082497291)
              ·
                refine ⟨15223039097770671123745937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10148692731847114082497291 15223039097770671123745937)
                ·
                  refine ⟨11417279323328003342809453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15223039097770671123745937 11417279323328003342809453)
                  ·
                    refine ⟨4281479746248001253553545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11417279323328003342809453 4281479746248001253553545)
                    ·
                      refine ⟨3211109809686000940165159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4281479746248001253553545 3211109809686000940165159)
                      ·
                        rfl

theorem cell23_6253614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_6253614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253614 prefixEnd_6253614 := by exact prefixLift 6253614
  have htrace : WordTrace (prefixWord ++ tailWord_6253614) baseStart_6253614 baseEnd_6253614 := by
    simpa [prefixWord, tailWord_6253614, baseEnd_6253614] using wordTrace_append hprefix tailTrace_6253614
  have hstable : (prefixWord ++ tailWord_6253614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253614).length < 2 ^ (prefixWord ++ tailWord_6253614).sum := by decide
  have hdescent : baseEnd_6253614 < baseStart_6253614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253633 : List Nat := [1, 2, 5, 1, 14]
def baseStart_6253633 : Nat := 118140960795 + 6253633 * 2 ^ 59
def prefixEnd_6253633 : Nat := 4983230072969 + 3 ^ 40 * 6253633 * 2
def baseEnd_6253633 : Nat := 4404827936650804342699

theorem tailTrace_6253633 : CollatzResearch.WordTrace tailWord_6253633 prefixEnd_6253633 4404827936650804342699 := by
  unfold tailWord_6253633
  simp only [CollatzResearch.WordTrace]
  refine ⟨228088733753163151330861553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152059155835442100887241035 228088733753163151330861553)
  ·
    refine ⟨171066550314872363498146165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228088733753163151330861553 171066550314872363498146165)
    ·
      refine ⟨16037489092019284077951203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171066550314872363498146165 16037489092019284077951203)
      ·
        refine ⟨24056233638028926116926805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16037489092019284077951203 24056233638028926116926805)
        ·
          refine ⟨4404827936650804342699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 24056233638028926116926805 4404827936650804342699)
          ·
            rfl

theorem cell23_6253633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 14].length) (baseStart_6253633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253633 prefixEnd_6253633 := by exact prefixLift 6253633
  have htrace : WordTrace (prefixWord ++ tailWord_6253633) baseStart_6253633 baseEnd_6253633 := by
    simpa [prefixWord, tailWord_6253633, baseEnd_6253633] using wordTrace_append hprefix tailTrace_6253633
  have hstable : (prefixWord ++ tailWord_6253633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253633).length < 2 ^ (prefixWord ++ tailWord_6253633).sum := by decide
  have hdescent : baseEnd_6253633 < baseStart_6253633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253638 : List Nat := [6, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_6253638 : Nat := 118140960795 + 6253638 * 2 ^ 59
def prefixEnd_6253638 : Nat := 4983230072969 + 3 ^ 40 * 6253638 * 2
def baseEnd_6253638 : Nat := 3211122133221708846265049

theorem tailTrace_6253638 : CollatzResearch.WordTrace tailWord_6253638 prefixEnd_6253638 3211122133221708846265049 := by
  unfold tailWord_6253638
  simp only [CollatzResearch.WordTrace]
  refine ⟨7127778628692032412024799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152059277412096691456529045 7127778628692032412024799)
  ·
    refine ⟨10691667943038048618037199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7127778628692032412024799 10691667943038048618037199)
    ·
      refine ⟨16037501914557072927055799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10691667943038048618037199 16037501914557072927055799)
      ·
        refine ⟨24056252871835609390583699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16037501914557072927055799 24056252871835609390583699)
        ·
          refine ⟨36084379307753414085875549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24056252871835609390583699 36084379307753414085875549)
          ·
            refine ⟨13531642240407530282203331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36084379307753414085875549 13531642240407530282203331)
            ·
              refine ⟨20297463360611295423304997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13531642240407530282203331 20297463360611295423304997)
              ·
                refine ⟨3805774380114617891869687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20297463360611295423304997 3805774380114617891869687)
                ·
                  refine ⟨5708661570171926837804531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3805774380114617891869687 5708661570171926837804531)
                  ·
                    refine ⟨8562992355257890256706797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5708661570171926837804531 8562992355257890256706797)
                    ·
                      refine ⟨3211122133221708846265049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8562992355257890256706797 3211122133221708846265049)
                      ·
                        rfl

theorem cell23_6253638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_6253638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253638 prefixEnd_6253638 := by exact prefixLift 6253638
  have htrace : WordTrace (prefixWord ++ tailWord_6253638) baseStart_6253638 baseEnd_6253638 := by
    simpa [prefixWord, tailWord_6253638, baseEnd_6253638] using wordTrace_append hprefix tailTrace_6253638
  have hstable : (prefixWord ++ tailWord_6253638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253638).length < 2 ^ (prefixWord ++ tailWord_6253638).sum := by decide
  have hdescent : baseEnd_6253638 < baseStart_6253638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253650 : List Nat := [3, 2, 2, 1, 3, 1, 3, 8]
def baseStart_6253650 : Nat := 118140960795 + 6253650 * 2 ^ 59
def prefixEnd_6253650 : Nat := 4983230072969 + 3 ^ 40 * 6253650 * 2
def baseEnd_6253650 : Nat := 118930677592206029604259

theorem tailTrace_6253650 : CollatzResearch.WordTrace tailWord_6253650 prefixEnd_6253650 118930677592206029604259 := by
  unfold tailWord_6253650
  simp only [CollatzResearch.WordTrace]
  refine ⟨57022338448525390808557601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152059569196067708822820269 57022338448525390808557601)
  ·
    refine ⟨42766753836394043106418201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57022338448525390808557601 42766753836394043106418201)
    ·
      refine ⟨32075065377295532329813651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42766753836394043106418201 32075065377295532329813651)
      ·
        refine ⟨48112598065943298494720477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32075065377295532329813651 48112598065943298494720477)
        ·
          refine ⟨18042224274728736935520179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48112598065943298494720477 18042224274728736935520179)
          ·
            refine ⟨27063336412093105403280269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18042224274728736935520179 27063336412093105403280269)
            ·
              refine ⟨10148751154534914526230101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27063336412093105403280269 10148751154534914526230101)
              ·
                refine ⟨118930677592206029604259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10148751154534914526230101 118930677592206029604259)
                ·
                  rfl

theorem cell23_6253650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 8].length) (baseStart_6253650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253650 prefixEnd_6253650 := by exact prefixLift 6253650
  have htrace : WordTrace (prefixWord ++ tailWord_6253650) baseStart_6253650 baseEnd_6253650 := by
    simpa [prefixWord, tailWord_6253650, baseEnd_6253650] using wordTrace_append hprefix tailTrace_6253650
  have hstable : (prefixWord ++ tailWord_6253650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253650).length < 2 ^ (prefixWord ++ tailWord_6253650).sum := by decide
  have hdescent : baseEnd_6253650 < baseStart_6253650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253663 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 2, 7]
def baseStart_6253663 : Nat := 118140960795 + 6253663 * 2 ^ 59
def prefixEnd_6253663 : Nat := 4983230072969 + 3 ^ 40 * 6253663 * 2
def baseEnd_6253663 : Nat := 1070378323412690416150811

theorem tailTrace_6253663 : CollatzResearch.WordTrace tailWord_6253663 prefixEnd_6253663 1070378323412690416150811 := by
  unfold tailWord_6253663
  simp only [CollatzResearch.WordTrace]
  refine ⟨228089827943054466454453643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152059885295369644302969095 228089827943054466454453643)
  ·
    refine ⟨342134741914581699681680465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228089827943054466454453643 342134741914581699681680465)
    ·
      refine ⟨256601056435936274761260349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342134741914581699681680465 256601056435936274761260349)
      ·
        refine ⟨96225396163476103035472631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256601056435936274761260349 96225396163476103035472631)
        ·
          refine ⟨144338094245214154553208947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96225396163476103035472631 144338094245214154553208947)
          ·
            refine ⟨216507141367821231829813421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144338094245214154553208947 216507141367821231829813421)
            ·
              refine ⟨81190178012932961936180033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216507141367821231829813421 81190178012932961936180033)
              ·
                refine ⟨60892633509699721452135025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81190178012932961936180033 60892633509699721452135025)
                ·
                  refine ⟨45669475132274791089101269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60892633509699721452135025 45669475132274791089101269)
                  ·
                    refine ⟨1070378323412690416150811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45669475132274791089101269 1070378323412690416150811)
                    ·
                      rfl

theorem cell23_6253663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_6253663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253663 prefixEnd_6253663 := by exact prefixLift 6253663
  have htrace : WordTrace (prefixWord ++ tailWord_6253663) baseStart_6253663 baseEnd_6253663 := by
    simpa [prefixWord, tailWord_6253663, baseEnd_6253663] using wordTrace_append hprefix tailTrace_6253663
  have hstable : (prefixWord ++ tailWord_6253663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253663).length < 2 ^ (prefixWord ++ tailWord_6253663).sum := by decide
  have hdescent : baseEnd_6253663 < baseStart_6253663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253677 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_6253677 : Nat := 118140960795 + 6253677 * 2 ^ 59
def prefixEnd_6253677 : Nat := 4983230072969 + 3 ^ 40 * 6253677 * 2
def baseEnd_6253677 : Nat := 3211142158967234193677369

theorem tailTrace_6253677 : CollatzResearch.WordTrace tailWord_6253677 prefixEnd_6253677 3211142158967234193677369 := by
  unfold tailWord_6253677
  simp only [CollatzResearch.WordTrace]
  refine ⟨228090338565003746845463285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152060225710002497896975523 228090338565003746845463285)
  ·
    refine ⟨21383469240469101266762183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228090338565003746845463285 21383469240469101266762183)
    ·
      refine ⟨32075203860703651900143275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21383469240469101266762183 32075203860703651900143275)
      ·
        refine ⟨48112805791055477850214913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32075203860703651900143275 48112805791055477850214913)
        ·
          refine ⟨36084604343291608387661185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48112805791055477850214913 36084604343291608387661185)
          ·
            refine ⟨27063453257468706290745889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36084604343291608387661185 27063453257468706290745889)
            ·
              refine ⟨20297589943101529718059417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27063453257468706290745889 20297589943101529718059417)
              ·
                refine ⟨15223192457326147288544563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20297589943101529718059417 15223192457326147288544563)
                ·
                  refine ⟨22834788685989220932816845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15223192457326147288544563 22834788685989220932816845)
                  ·
                    refine ⟨8563045757245957849806317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22834788685989220932816845 8563045757245957849806317)
                    ·
                      refine ⟨3211142158967234193677369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8563045757245957849806317 3211142158967234193677369)
                      ·
                        rfl

theorem cell23_6253677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_6253677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253677 prefixEnd_6253677 := by exact prefixLift 6253677
  have htrace : WordTrace (prefixWord ++ tailWord_6253677) baseStart_6253677 baseEnd_6253677 := by
    simpa [prefixWord, tailWord_6253677, baseEnd_6253677] using wordTrace_append hprefix tailTrace_6253677
  have hstable : (prefixWord ++ tailWord_6253677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253677).length < 2 ^ (prefixWord ++ tailWord_6253677).sum := by decide
  have hdescent : baseEnd_6253677 < baseStart_6253677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253678 : List Nat := [4, 1, 2, 2, 1, 3, 2, 3, 1, 2, 2]
def baseStart_6253678 : Nat := 118140960795 + 6253678 * 2 ^ 59
def prefixEnd_6253678 : Nat := 4983230072969 + 3 ^ 40 * 6253678 * 2
def baseEnd_6253678 : Nat := 3211142672447888689764865

theorem tailTrace_6253678 : CollatzResearch.WordTrace tailWord_6253678 prefixEnd_6253678 3211142672447888689764865 := by
  unfold tailWord_6253678
  simp only [CollatzResearch.WordTrace]
  refine ⟨28511296879750015502031211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152060250025333416010833125 28511296879750015502031211)
  ·
    refine ⟨42766945319625023253046817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28511296879750015502031211 42766945319625023253046817)
    ·
      refine ⟨32075208989718767439785113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42766945319625023253046817 32075208989718767439785113)
      ·
        refine ⟨24056406742289075579838835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32075208989718767439785113 24056406742289075579838835)
        ·
          refine ⟨36084610113433613369758253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24056406742289075579838835 36084610113433613369758253)
          ·
            refine ⟨13531728792537605013659345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36084610113433613369758253 13531728792537605013659345)
            ·
              refine ⟨10148796594403203760244509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13531728792537605013659345 10148796594403203760244509)
              ·
                refine ⟨3805798722901201410091691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10148796594403203760244509 3805798722901201410091691)
                ·
                  refine ⟨5708698084351802115137537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3805798722901201410091691 5708698084351802115137537)
                  ·
                    refine ⟨4281523563263851586353153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5708698084351802115137537 4281523563263851586353153)
                    ·
                      refine ⟨3211142672447888689764865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4281523563263851586353153 3211142672447888689764865)
                      ·
                        rfl

theorem cell23_6253678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_6253678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253678 prefixEnd_6253678 := by exact prefixLift 6253678
  have htrace : WordTrace (prefixWord ++ tailWord_6253678) baseStart_6253678 baseEnd_6253678 := by
    simpa [prefixWord, tailWord_6253678, baseEnd_6253678] using wordTrace_append hprefix tailTrace_6253678
  have hstable : (prefixWord ++ tailWord_6253678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253678).length < 2 ^ (prefixWord ++ tailWord_6253678).sum := by decide
  have hdescent : baseEnd_6253678 < baseStart_6253678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253713 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_6253713 : Nat := 118140960795 + 6253713 * 2 ^ 59
def prefixEnd_6253713 : Nat := 4983230072969 + 3 ^ 40 * 6253713 * 2
def baseEnd_6253713 : Nat := 3211160644270796052827203

theorem tailTrace_6253713 : CollatzResearch.WordTrace tailWord_6253713 prefixEnd_6253713 3211160644270796052827203 := by
  unfold tailWord_6253713
  simp only [CollatzResearch.WordTrace]
  refine ⟨228091651592873324993773793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152061101061915549995849195 228091651592873324993773793)
  ·
    refine ⟨171068738694654993745330345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228091651592873324993773793 171068738694654993745330345)
    ·
      refine ⟨128301554020991245308997759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171068738694654993745330345 128301554020991245308997759)
      ·
        refine ⟨192452331031486867963496639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128301554020991245308997759 192452331031486867963496639)
        ·
          refine ⟨288678496547230301945244959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192452331031486867963496639 288678496547230301945244959)
          ·
            refine ⟨433017744820845452917867439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288678496547230301945244959 433017744820845452917867439)
            ·
              refine ⟨649526617231268179376801159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433017744820845452917867439 649526617231268179376801159)
              ·
                refine ⟨974289925846902269065201739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649526617231268179376801159 974289925846902269065201739)
                ·
                  refine ⟨1461434888770353403597802609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974289925846902269065201739 1461434888770353403597802609)
                  ·
                    refine ⟨1096076166577765052698351957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1461434888770353403597802609 1096076166577765052698351957)
                    ·
                      refine ⟨3211160644270796052827203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1096076166577765052698351957 3211160644270796052827203)
                      ·
                        rfl

theorem cell23_6253713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_6253713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253713 prefixEnd_6253713 := by exact prefixLift 6253713
  have htrace : WordTrace (prefixWord ++ tailWord_6253713) baseStart_6253713 baseEnd_6253713 := by
    simpa [prefixWord, tailWord_6253713, baseEnd_6253713] using wordTrace_append hprefix tailTrace_6253713
  have hstable : (prefixWord ++ tailWord_6253713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253713).length < 2 ^ (prefixWord ++ tailWord_6253713).sum := by decide
  have hdescent : baseEnd_6253713 < baseStart_6253713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253717 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 1, 4, 2]
def baseStart_6253717 : Nat := 118140960795 + 6253717 * 2 ^ 59
def prefixEnd_6253717 : Nat := 4983230072969 + 3 ^ 40 * 6253717 * 2
def baseEnd_6253717 : Nat := 3211162698193414037177185

theorem tailTrace_6253717 : CollatzResearch.WordTrace tailWord_6253717 prefixEnd_6253717 3211162698193414037177185 := by
  unfold tailWord_6253717
  simp only [CollatzResearch.WordTrace]
  refine ⟨228091797484858833676919405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152061198323239222451279603 228091797484858833676919405)
  ·
    refine ⟨85534424056822062628844777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228091797484858833676919405 85534424056822062628844777)
    ·
      refine ⟨64150818042616546971633583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85534424056822062628844777 64150818042616546971633583)
      ·
        refine ⟨96226227063924820457450375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64150818042616546971633583 96226227063924820457450375)
        ·
          refine ⟨144339340595887230686175563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96226227063924820457450375 144339340595887230686175563)
          ·
            refine ⟨216509010893830846029263345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144339340595887230686175563 216509010893830846029263345)
            ·
              refine ⟨162381758170373134521947509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216509010893830846029263345 162381758170373134521947509)
              ·
                refine ⟨15223289828472481361432579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162381758170373134521947509 15223289828472481361432579)
                ·
                  refine ⟨22834934742708722042148869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15223289828472481361432579 22834934742708722042148869)
                  ·
                    refine ⟨4281550264257885382902913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22834934742708722042148869 4281550264257885382902913)
                    ·
                      refine ⟨3211162698193414037177185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4281550264257885382902913 3211162698193414037177185)
                      ·
                        rfl

theorem cell23_6253717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_6253717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253717 prefixEnd_6253717 := by exact prefixLift 6253717
  have htrace : WordTrace (prefixWord ++ tailWord_6253717) baseStart_6253717 baseEnd_6253717 := by
    simpa [prefixWord, tailWord_6253717, baseEnd_6253717] using wordTrace_append hprefix tailTrace_6253717
  have hstable : (prefixWord ++ tailWord_6253717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253717).length < 2 ^ (prefixWord ++ tailWord_6253717).sum := by decide
  have hdescent : baseEnd_6253717 < baseStart_6253717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253757 : List Nat := [1, 4, 1, 2, 1, 1, 2, 6, 5]
def baseStart_6253757 : Nat := 118140960795 + 6253757 * 2 ^ 59
def prefixEnd_6253757 : Nat := 4983230072969 + 3 ^ 40 * 6253757 * 2
def baseEnd_6253757 : Nat := 356798137491065986741889

theorem tailTrace_6253757 : CollatzResearch.WordTrace tailWord_6253757 prefixEnd_6253757 356798137491065986741889 := by
  unfold tailWord_6253757
  simp only [CollatzResearch.WordTrace]
  refine ⟨228093256404713920508375525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152062170936475947005583683 228093256404713920508375525)
  ·
    refine ⟨42767485575883860095320411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228093256404713920508375525 42767485575883860095320411)
    ·
      refine ⟨64151228363825790142980617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42767485575883860095320411 64151228363825790142980617)
      ·
        refine ⟨48113421272869342607235463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64151228363825790142980617 48113421272869342607235463)
        ·
          refine ⟨72170131909304013910853195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48113421272869342607235463 72170131909304013910853195)
          ·
            refine ⟨108255197863956020866279793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72170131909304013910853195 108255197863956020866279793)
            ·
              refine ⟨81191398397967015649709845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108255197863956020866279793 81191398397967015649709845)
              ·
                refine ⟨3805846799904703858580149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81191398397967015649709845 3805846799904703858580149)
                ·
                  refine ⟨356798137491065986741889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3805846799904703858580149 356798137491065986741889)
                  ·
                    rfl

theorem cell23_6253757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_6253757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253757 prefixEnd_6253757 := by exact prefixLift 6253757
  have htrace : WordTrace (prefixWord ++ tailWord_6253757) baseStart_6253757 baseEnd_6253757 := by
    simpa [prefixWord, tailWord_6253757, baseEnd_6253757] using wordTrace_append hprefix tailTrace_6253757
  have hstable : (prefixWord ++ tailWord_6253757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253757).length < 2 ^ (prefixWord ++ tailWord_6253757).sum := by decide
  have hdescent : baseEnd_6253757 < baseStart_6253757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253762 : List Nat := [3, 5, 1, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_6253762 : Nat := 118140960795 + 6253762 * 2 ^ 59
def prefixEnd_6253762 : Nat := 4983230072969 + 3 ^ 40 * 6253762 * 2
def baseEnd_6253762 : Nat := 3211185804822866361114479

theorem tailTrace_6253762 : CollatzResearch.WordTrace tailWord_6253762 prefixEnd_6253762 3211185804822866361114479 := by
  unfold tailWord_6253762
  simp only [CollatzResearch.WordTrace]
  refine ⟨57023359692423951590576885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152062292513130537574871693 57023359692423951590576885)
  ·
    refine ⟨5345939971164745461616583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57023359692423951590576885 5345939971164745461616583)
    ·
      refine ⟨8018909956747118192424875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5345939971164745461616583 8018909956747118192424875)
      ·
        refine ⟨12028364935120677288637313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8018909956747118192424875 12028364935120677288637313)
        ·
          refine ⟨9021273701340507966477985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12028364935120677288637313 9021273701340507966477985)
          ·
            refine ⟨6765955276005380974858489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9021273701340507966477985 6765955276005380974858489)
            ·
              refine ⟨5074466457004035731143867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6765955276005380974858489 5074466457004035731143867)
              ·
                refine ⟨7611699685506053596715801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5074466457004035731143867 7611699685506053596715801)
                ·
                  refine ⟨5708774764129540197536851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7611699685506053596715801 5708774764129540197536851)
                  ·
                    refine ⟨8563162146194310296305277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5708774764129540197536851 8563162146194310296305277)
                    ·
                      refine ⟨3211185804822866361114479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8563162146194310296305277 3211185804822866361114479)
                      ·
                        rfl

theorem cell23_6253762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_6253762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253762 prefixEnd_6253762 := by exact prefixLift 6253762
  have htrace : WordTrace (prefixWord ++ tailWord_6253762) baseStart_6253762 baseEnd_6253762 := by
    simpa [prefixWord, tailWord_6253762, baseEnd_6253762] using wordTrace_append hprefix tailTrace_6253762
  have hstable : (prefixWord ++ tailWord_6253762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253762).length < 2 ^ (prefixWord ++ tailWord_6253762).sum := by decide
  have hdescent : baseEnd_6253762 < baseStart_6253762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253817 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 3, 4]
def baseStart_6253817 : Nat := 118140960795 + 6253817 * 2 ^ 59
def prefixEnd_6253817 : Nat := 4983230072969 + 3 ^ 40 * 6253817 * 2
def baseEnd_6253817 : Nat := 1070404682086287881975575

theorem tailTrace_6253817 : CollatzResearch.WordTrace tailWord_6253817 prefixEnd_6253817 1070404682086287881975575 := by
  unfold tailWord_6253817
  simp only [CollatzResearch.WordTrace]
  refine ⟨228095444784496550755559705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152063629856331033837039803 228095444784496550755559705)
  ·
    refine ⟨171071583588372413066669779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228095444784496550755559705 171071583588372413066669779)
    ·
      refine ⟨256607375382558619600004669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171071583588372413066669779 256607375382558619600004669)
      ·
        refine ⟨96227765768459482350001751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256607375382558619600004669 96227765768459482350001751)
        ·
          refine ⟨144341648652689223525002627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96227765768459482350001751 144341648652689223525002627)
          ·
            refine ⟨216512472979033835287503941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144341648652689223525002627 216512472979033835287503941)
            ·
              refine ⟨40596088683568844116406989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216512472979033835287503941 40596088683568844116406989)
              ·
                refine ⟨15223533256338316543652621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40596088683568844116406989 15223533256338316543652621)
                ·
                  refine ⟨5708824971126868703869733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15223533256338316543652621 5708824971126868703869733)
                  ·
                    refine ⟨1070404682086287881975575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5708824971126868703869733 1070404682086287881975575)
                    ·
                      rfl

theorem cell23_6253817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 4].length) (baseStart_6253817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253817 prefixEnd_6253817 := by exact prefixLift 6253817
  have htrace : WordTrace (prefixWord ++ tailWord_6253817) baseStart_6253817 baseEnd_6253817 := by
    simpa [prefixWord, tailWord_6253817, baseEnd_6253817] using wordTrace_append hprefix tailTrace_6253817
  have hstable : (prefixWord ++ tailWord_6253817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253817).length < 2 ^ (prefixWord ++ tailWord_6253817).sum := by decide
  have hdescent : baseEnd_6253817 < baseStart_6253817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253864 : List Nat := [2, 1, 5, 1, 2, 1, 3, 2, 6]
def baseStart_6253864 : Nat := 118140960795 + 6253864 * 2 ^ 59
def prefixEnd_6253864 : Nat := 4983230072969 + 3 ^ 40 * 6253864 * 2
def baseEnd_6253864 : Nat := 356804242205513884671001

theorem tailTrace_6253864 : CollatzResearch.WordTrace tailWord_6253864 prefixEnd_6253864 356804242205513884671001 := by
  unfold tailWord_6253864
  simp only [CollatzResearch.WordTrace]
  refine ⟨114048579507663138891260323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152064772676884185188347097 114048579507663138891260323)
  ·
    refine ⟨171072869261494708336890485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114048579507663138891260323 171072869261494708336890485)
    ·
      refine ⟨16038081493265128906583483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171072869261494708336890485 16038081493265128906583483)
      ·
        refine ⟨24057122239897693359875225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16038081493265128906583483 24057122239897693359875225)
        ·
          refine ⟨18042841679923270019906419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24057122239897693359875225 18042841679923270019906419)
          ·
            refine ⟨27064262519884905029859629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18042841679923270019906419 27064262519884905029859629)
            ·
              refine ⟨10149098444956839386197361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27064262519884905029859629 10149098444956839386197361)
              ·
                refine ⟨7611823833717629539648021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10149098444956839386197361 7611823833717629539648021)
                ·
                  refine ⟨356804242205513884671001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7611823833717629539648021 356804242205513884671001)
                  ·
                    rfl

theorem cell23_6253864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 6].length) (baseStart_6253864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253864 prefixEnd_6253864 := by exact prefixLift 6253864
  have htrace : WordTrace (prefixWord ++ tailWord_6253864) baseStart_6253864 baseEnd_6253864 := by
    simpa [prefixWord, tailWord_6253864, baseEnd_6253864] using wordTrace_append hprefix tailTrace_6253864
  have hstable : (prefixWord ++ tailWord_6253864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253864).length < 2 ^ (prefixWord ++ tailWord_6253864).sum := by decide
  have hdescent : baseEnd_6253864 < baseStart_6253864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253867 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 2, 9, 2]
def baseStart_6253867 : Nat := 118140960795 + 6253867 * 2 ^ 59
def prefixEnd_6253867 : Nat := 4983230072969 + 3 ^ 40 * 6253867 * 2
def baseEnd_6253867 : Nat := 3211239720291588450301495

theorem tailTrace_6253867 : CollatzResearch.WordTrace tailWord_6253867 prefixEnd_6253867 3211239720291588450301495 := by
  unfold tailWord_6253867
  simp only [CollatzResearch.WordTrace]
  refine ⟨228097268434315409294879855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152064845622876939529919903 228097268434315409294879855)
  ·
    refine ⟨342145902651473113942319783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228097268434315409294879855 342145902651473113942319783)
    ·
      refine ⟨513218853977209670913479675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342145902651473113942319783 513218853977209670913479675)
      ·
        refine ⟨769828280965814506370219513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513218853977209670913479675 769828280965814506370219513)
        ·
          refine ⟨577371210724360879777664635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769828280965814506370219513 577371210724360879777664635)
          ·
            refine ⟨866056816086541319666496953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577371210724360879777664635 866056816086541319666496953)
            ·
              refine ⟨649542612064905989749872715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866056816086541319666496953 649542612064905989749872715)
              ·
                refine ⟨974313918097358984624809073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649542612064905989749872715 974313918097358984624809073)
                ·
                  refine ⟨730735438573019238468606805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 974313918097358984624809073 730735438573019238468606805)
                  ·
                    refine ⟨4281652960388784600401993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 730735438573019238468606805 4281652960388784600401993)
                    ·
                      refine ⟨3211239720291588450301495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4281652960388784600401993 3211239720291588450301495)
                      ·
                        rfl

theorem cell23_6253867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 9, 2].length) (baseStart_6253867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253867 prefixEnd_6253867 := by exact prefixLift 6253867
  have htrace : WordTrace (prefixWord ++ tailWord_6253867) baseStart_6253867 baseEnd_6253867 := by
    simpa [prefixWord, tailWord_6253867, baseEnd_6253867] using wordTrace_append hprefix tailTrace_6253867
  have hstable : (prefixWord ++ tailWord_6253867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253867).length < 2 ^ (prefixWord ++ tailWord_6253867).sum := by decide
  have hdescent : baseEnd_6253867 < baseStart_6253867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253881 : List Nat := [1, 2, 1, 6, 2, 1, 3, 1, 6]
def baseStart_6253881 : Nat := 118140960795 + 6253881 * 2 ^ 59
def prefixEnd_6253881 : Nat := 4983230072969 + 3 ^ 40 * 6253881 * 2
def baseEnd_6253881 : Nat := 356805212113416821725159

theorem tailTrace_6253881 : CollatzResearch.WordTrace tailWord_6253881 prefixEnd_6253881 356805212113416821725159 := by
  unfold tailWord_6253881
  simp only [CollatzResearch.WordTrace]
  refine ⟨228097779056264689685889497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152065186037509793123926331 228097779056264689685889497)
  ·
    refine ⟨171073334292198517264417123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228097779056264689685889497 171073334292198517264417123)
    ·
      refine ⟨256610001438297775896625685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171073334292198517264417123 256610001438297775896625685)
      ·
        refine ⟨12028593817420208245154329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 256610001438297775896625685 12028593817420208245154329)
        ·
          refine ⟨9021445363065156183865747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12028593817420208245154329 9021445363065156183865747)
          ·
            refine ⟨13532168044597734275798621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9021445363065156183865747 13532168044597734275798621)
            ·
              refine ⟨5074563016724150353424483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13532168044597734275798621 5074563016724150353424483)
              ·
                refine ⟨7611844525086225530136725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5074563016724150353424483 7611844525086225530136725)
                ·
                  refine ⟨356805212113416821725159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7611844525086225530136725 356805212113416821725159)
                  ·
                    rfl

theorem cell23_6253881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 6].length) (baseStart_6253881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253881 prefixEnd_6253881 := by exact prefixLift 6253881
  have htrace : WordTrace (prefixWord ++ tailWord_6253881) baseStart_6253881 baseEnd_6253881 := by
    simpa [prefixWord, tailWord_6253881, baseEnd_6253881] using wordTrace_append hprefix tailTrace_6253881
  have hstable : (prefixWord ++ tailWord_6253881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253881).length < 2 ^ (prefixWord ++ tailWord_6253881).sum := by decide
  have hdescent : baseEnd_6253881 < baseStart_6253881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253884 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 1, 5, 2]
def baseStart_6253884 : Nat := 118140960795 + 6253884 * 2 ^ 59
def prefixEnd_6253884 : Nat := 4983230072969 + 3 ^ 40 * 6253884 * 2
def baseEnd_6253884 : Nat := 3211248449462714883788917

theorem tailTrace_6253884 : CollatzResearch.WordTrace tailWord_6253884 prefixEnd_6253884 3211248449462714883788917 := by
  unfold tailWord_6253884
  simp only [CollatzResearch.WordTrace]
  refine ⟨114048944237626910599124353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152065258983502547465499137 114048944237626910599124353)
  ·
    refine ⟨85536708178220182949343265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114048944237626910599124353 85536708178220182949343265)
    ·
      refine ⟨64152531133665137212007449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85536708178220182949343265 64152531133665137212007449)
      ·
        refine ⟨48114398350248852909005587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64152531133665137212007449 48114398350248852909005587)
        ·
          refine ⟨72171597525373279363508381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48114398350248852909005587 72171597525373279363508381)
          ·
            refine ⟨27064349072014979761315643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72171597525373279363508381 27064349072014979761315643)
            ·
              refine ⟨40596523608022469641973465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27064349072014979761315643 40596523608022469641973465)
              ·
                refine ⟨30447392706016852231480099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40596523608022469641973465 30447392706016852231480099)
                ·
                  refine ⟨45671089059025278347220149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30447392706016852231480099 45671089059025278347220149)
                  ·
                    refine ⟨4281664599283619845051889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45671089059025278347220149 4281664599283619845051889)
                    ·
                      refine ⟨3211248449462714883788917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4281664599283619845051889 3211248449462714883788917)
                      ·
                        rfl

theorem cell23_6253884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_6253884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253884 prefixEnd_6253884 := by exact prefixLift 6253884
  have htrace : WordTrace (prefixWord ++ tailWord_6253884) baseStart_6253884 baseEnd_6253884 := by
    simpa [prefixWord, tailWord_6253884, baseEnd_6253884] using wordTrace_append hprefix tailTrace_6253884
  have hstable : (prefixWord ++ tailWord_6253884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253884).length < 2 ^ (prefixWord ++ tailWord_6253884).sum := by decide
  have hdescent : baseEnd_6253884 < baseStart_6253884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253897 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 3, 1, 4]
def baseStart_6253897 : Nat := 118140960795 + 6253897 * 2 ^ 59
def prefixEnd_6253897 : Nat := 4983230072969 + 3 ^ 40 * 6253897 * 2
def baseEnd_6253897 : Nat := 3211255124711223332926357

theorem tailTrace_6253897 : CollatzResearch.WordTrace tailWord_6253897 prefixEnd_6253897 3211255124711223332926357 := by
  unfold tailWord_6253897
  simp only [CollatzResearch.WordTrace]
  refine ⟨228098362624206724418471945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152065575082804482945647963 228098362624206724418471945)
  ·
    refine ⟨171073771968155043313853959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228098362624206724418471945 171073771968155043313853959)
    ·
      refine ⟨256610657952232564970780939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171073771968155043313853959 256610657952232564970780939)
      ·
        refine ⟨384915986928348847456171409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256610657952232564970780939 384915986928348847456171409)
        ·
          refine ⟨288686990196261635592128557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384915986928348847456171409 288686990196261635592128557)
          ·
            refine ⟨108257621323598113347048209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288686990196261635592128557 108257621323598113347048209)
            ·
              refine ⟨81193215992698585010286157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108257621323598113347048209 81193215992698585010286157)
              ·
                refine ⟨30447455997261969378857309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81193215992698585010286157 30447455997261969378857309)
                ·
                  refine ⟨11417795998973238517071491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30447455997261969378857309 11417795998973238517071491)
                  ·
                    refine ⟨17126693998459857775607237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11417795998973238517071491 17126693998459857775607237)
                    ·
                      refine ⟨3211255124711223332926357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17126693998459857775607237 3211255124711223332926357)
                      ·
                        rfl

theorem cell23_6253897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_6253897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253897 prefixEnd_6253897 := by exact prefixLift 6253897
  have htrace : WordTrace (prefixWord ++ tailWord_6253897) baseStart_6253897 baseEnd_6253897 := by
    simpa [prefixWord, tailWord_6253897, baseEnd_6253897] using wordTrace_append hprefix tailTrace_6253897
  have hstable : (prefixWord ++ tailWord_6253897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253897).length < 2 ^ (prefixWord ++ tailWord_6253897).sum := by decide
  have hdescent : baseEnd_6253897 < baseStart_6253897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253907 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 6, 4]
def baseStart_6253907 : Nat := 118140960795 + 6253907 * 2 ^ 59
def prefixEnd_6253907 : Nat := 4983230072969 + 3 ^ 40 * 6253907 * 2
def baseEnd_6253907 : Nat := 1070420086505922764600437

theorem tailTrace_6253907 : CollatzResearch.WordTrace tailWord_6253907 prefixEnd_6253907 1070420086505922764600437 := by
  unfold tailWord_6253907
  simp only [CollatzResearch.WordTrace]
  refine ⟨228098727354170496126335975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152065818236113664084223983 228098727354170496126335975)
  ·
    refine ⟨342148091031255744189503963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228098727354170496126335975 342148091031255744189503963)
    ·
      refine ⟨513222136546883616284255945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342148091031255744189503963 513222136546883616284255945)
      ·
        refine ⟨384916602410162712213191959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513222136546883616284255945 384916602410162712213191959)
        ·
          refine ⟨577374903615244068319787939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384916602410162712213191959 577374903615244068319787939)
          ·
            refine ⟨866062355422866102479681909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577374903615244068319787939 866062355422866102479681909)
            ·
              refine ⟨81193345820893697107470179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 866062355422866102479681909 81193345820893697107470179)
              ·
                refine ⟨121790018731340545661205269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81193345820893697107470179 121790018731340545661205269)
                ·
                  refine ⟨5708907128031588077868997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121790018731340545661205269 5708907128031588077868997)
                  ·
                    refine ⟨1070420086505922764600437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5708907128031588077868997 1070420086505922764600437)
                    ·
                      rfl

theorem cell23_6253907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 4].length) (baseStart_6253907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253907 prefixEnd_6253907 := by exact prefixLift 6253907
  have htrace : WordTrace (prefixWord ++ tailWord_6253907) baseStart_6253907 baseEnd_6253907 := by
    simpa [prefixWord, tailWord_6253907, baseEnd_6253907] using wordTrace_append hprefix tailTrace_6253907
  have hstable : (prefixWord ++ tailWord_6253907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253907).length < 2 ^ (prefixWord ++ tailWord_6253907).sum := by decide
  have hdescent : baseEnd_6253907 < baseStart_6253907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253914 : List Nat := [3, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4]
def baseStart_6253914 : Nat := 118140960795 + 6253914 * 2 ^ 59
def prefixEnd_6253914 : Nat := 4983230072969 + 3 ^ 40 * 6253914 * 2
def baseEnd_6253914 : Nat := 3211263853882349766413779

theorem tailTrace_6253914 : CollatzResearch.WordTrace tailWord_6253914 prefixEnd_6253914 3211263853882349766413779 := by
  unfold tailWord_6253914
  simp only [CollatzResearch.WordTrace]
  refine ⟨57024745666286284080460199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152065988443430090881227197 57024745666286284080460199)
  ·
    refine ⟨85537118499429426120690299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57024745666286284080460199 85537118499429426120690299)
    ·
      refine ⟨128305677749144139181035449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85537118499429426120690299 128305677749144139181035449)
      ·
        refine ⟨96229258311858104385776587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128305677749144139181035449 96229258311858104385776587)
        ·
          refine ⟨144343887467787156578664881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96229258311858104385776587 144343887467787156578664881)
          ·
            refine ⟨108257915600840367433998661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144343887467787156578664881 108257915600840367433998661)
            ·
              refine ⟨20298359175157568893874749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108257915600840367433998661 20298359175157568893874749)
              ·
                refine ⟨7611884690684088335203031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20298359175157568893874749 7611884690684088335203031)
                ·
                  refine ⟨11417827036026132502804547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7611884690684088335203031 11417827036026132502804547)
                  ·
                    refine ⟨17126740554039198754206821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11417827036026132502804547 17126740554039198754206821)
                    ·
                      refine ⟨3211263853882349766413779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17126740554039198754206821 3211263853882349766413779)
                      ·
                        rfl

theorem cell23_6253914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_6253914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253914 prefixEnd_6253914 := by exact prefixLift 6253914
  have htrace : WordTrace (prefixWord ++ tailWord_6253914) baseStart_6253914 baseEnd_6253914 := by
    simpa [prefixWord, tailWord_6253914, baseEnd_6253914] using wordTrace_append hprefix tailTrace_6253914
  have hstable : (prefixWord ++ tailWord_6253914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253914).length < 2 ^ (prefixWord ++ tailWord_6253914).sum := by decide
  have hdescent : baseEnd_6253914 < baseStart_6253914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253924 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_6253924 : Nat := 118140960795 + 6253924 * 2 ^ 59
def prefixEnd_6253924 : Nat := 4983230072969 + 3 ^ 40 * 6253924 * 2
def baseEnd_6253924 : Nat := 1070422996229631575762911

theorem tailTrace_6253924 : CollatzResearch.WordTrace tailWord_6253924 prefixEnd_6253924 1070422996229631575762911 := by
  unfold tailWord_6253924
  simp only [CollatzResearch.WordTrace]
  refine ⟨114049673697554454014852413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152066231596739272019803217 114049673697554454014852413)
  ·
    refine ⟨42768627636582920255569655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114049673697554454014852413 42768627636582920255569655)
    ·
      refine ⟨64152941454874380383354483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42768627636582920255569655 64152941454874380383354483)
      ·
        refine ⟨96229412182311570575031725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64152941454874380383354483 96229412182311570575031725)
        ·
          refine ⟨36086029568366838965636897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96229412182311570575031725 36086029568366838965636897)
          ·
            refine ⟨27064522176275129224227673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36086029568366838965636897 27064522176275129224227673)
            ·
              refine ⟨20298391632206346918170755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27064522176275129224227673 20298391632206346918170755)
              ·
                refine ⟨30447587448309520377256133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20298391632206346918170755 30447587448309520377256133)
                ·
                  refine ⟨5708922646558035070735525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30447587448309520377256133 5708922646558035070735525)
                  ·
                    refine ⟨1070422996229631575762911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5708922646558035070735525 1070422996229631575762911)
                    ·
                      rfl

theorem cell23_6253924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_6253924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253924 prefixEnd_6253924 := by exact prefixLift 6253924
  have htrace : WordTrace (prefixWord ++ tailWord_6253924) baseStart_6253924 baseEnd_6253924 := by
    simpa [prefixWord, tailWord_6253924, baseEnd_6253924] using wordTrace_append hprefix tailTrace_6253924
  have hstable : (prefixWord ++ tailWord_6253924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253924).length < 2 ^ (prefixWord ++ tailWord_6253924).sum := by decide
  have hdescent : baseEnd_6253924 < baseStart_6253924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253964 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 1, 3, 3]
def baseStart_6253964 : Nat := 118140960795 + 6253964 * 2 ^ 59
def prefixEnd_6253964 : Nat := 4983230072969 + 3 ^ 40 * 6253964 * 2
def baseEnd_6253964 : Nat := 3211289527915074570788549

theorem tailTrace_6253964 : CollatzResearch.WordTrace tailWord_6253964 prefixEnd_6253964 3211289527915074570788549 := by
  unfold tailWord_6253964
  simp only [CollatzResearch.WordTrace]
  refine ⟨114050403157481997430580473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152067204209975996574107297 114050403157481997430580473)
  ·
    refine ⟨85537802368111498072935355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114050403157481997430580473 85537802368111498072935355)
    ·
      refine ⟨128306703552167247109403033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85537802368111498072935355 128306703552167247109403033)
      ·
        refine ⟨96230027664125435332052275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128306703552167247109403033 96230027664125435332052275)
        ·
          refine ⟨144345041496188152998078413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96230027664125435332052275 144345041496188152998078413)
          ·
            refine ⟨54129390561070557374279405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144345041496188152998078413 54129390561070557374279405)
            ·
              refine ⟨20298521460401459015354777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54129390561070557374279405 20298521460401459015354777)
              ·
                refine ⟨15223891095301094261516083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20298521460401459015354777 15223891095301094261516083)
                ·
                  refine ⟨22835836642951641392274125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15223891095301094261516083 22835836642951641392274125)
                  ·
                    refine ⟨8563438741106865522102797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22835836642951641392274125 8563438741106865522102797)
                    ·
                      refine ⟨3211289527915074570788549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8563438741106865522102797 3211289527915074570788549)
                      ·
                        rfl

theorem cell23_6253964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_6253964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253964 prefixEnd_6253964 := by exact prefixLift 6253964
  have htrace : WordTrace (prefixWord ++ tailWord_6253964) baseStart_6253964 baseEnd_6253964 := by
    simpa [prefixWord, tailWord_6253964, baseEnd_6253964] using wordTrace_append hprefix tailTrace_6253964
  have hstable : (prefixWord ++ tailWord_6253964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253964).length < 2 ^ (prefixWord ++ tailWord_6253964).sum := by decide
  have hdescent : baseEnd_6253964 < baseStart_6253964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253987 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 4]
def baseStart_6253987 : Nat := 118140960795 + 6253987 * 2 ^ 59
def prefixEnd_6253987 : Nat := 4983230072969 + 3 ^ 40 * 6253987 * 2
def baseEnd_6253987 : Nat := 3211301337970127980800943

theorem tailTrace_6253987 : CollatzResearch.WordTrace tailWord_6253987 prefixEnd_6253987 3211301337970127980800943 := by
  unfold tailWord_6253987
  simp only [CollatzResearch.WordTrace]
  refine ⟨228101645193880669789248215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152067763462587113192832143 228101645193880669789248215)
  ·
    refine ⟨342152467790821004683872323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228101645193880669789248215 342152467790821004683872323)
    ·
      refine ⟨513228701686231507025808485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342152467790821004683872323 513228701686231507025808485)
      ·
        refine ⟨96230381566168407567339091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 513228701686231507025808485 96230381566168407567339091)
        ·
          refine ⟨144345572349252611351008637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96230381566168407567339091 144345572349252611351008637)
          ·
            refine ⟨54129589630969729256628239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144345572349252611351008637 54129589630969729256628239)
            ·
              refine ⟨81194384446454593884942359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54129589630969729256628239 81194384446454593884942359)
              ·
                refine ⟨121791576669681890827413539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81194384446454593884942359 121791576669681890827413539)
                ·
                  refine ⟨182687365004522836241120309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121791576669681890827413539 182687365004522836241120309)
                  ·
                    refine ⟨17126940469174015897605029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 182687365004522836241120309 17126940469174015897605029)
                    ·
                      refine ⟨3211301337970127980800943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17126940469174015897605029 3211301337970127980800943)
                      ·
                        rfl

theorem cell23_6253987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_6253987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253987 prefixEnd_6253987 := by exact prefixLift 6253987
  have htrace : WordTrace (prefixWord ++ tailWord_6253987) baseStart_6253987 baseEnd_6253987 := by
    simpa [prefixWord, tailWord_6253987, baseEnd_6253987] using wordTrace_append hprefix tailTrace_6253987
  have hstable : (prefixWord ++ tailWord_6253987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253987).length < 2 ^ (prefixWord ++ tailWord_6253987).sum := by decide
  have hdescent : baseEnd_6253987 < baseStart_6253987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6253991 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_6253991 : Nat := 118140960795 + 6253991 * 2 ^ 59
def prefixEnd_6253991 : Nat := 4983230072969 + 3 ^ 40 * 6253991 * 2
def baseEnd_6253991 : Nat := 3211303391892745965150925

theorem tailTrace_6253991 : CollatzResearch.WordTrace tailWord_6253991 prefixEnd_6253991 3211303391892745965150925 := by
  unfold tailWord_6253991
  simp only [CollatzResearch.WordTrace]
  refine ⟨228101791085866178472393827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152067860723910785648262551 228101791085866178472393827)
  ·
    refine ⟨342152686628799267708590741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228101791085866178472393827 342152686628799267708590741)
    ·
      refine ⟨16038407185724965673840191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 342152686628799267708590741 16038407185724965673840191)
      ·
        refine ⟨24057610778587448510760287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16038407185724965673840191 24057610778587448510760287)
        ·
          refine ⟨36086416167881172766140431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24057610778587448510760287 36086416167881172766140431)
          ·
            refine ⟨54129624251821759149210647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36086416167881172766140431 54129624251821759149210647)
            ·
              refine ⟨81194436377732638723815971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54129624251821759149210647 81194436377732638723815971)
              ·
                refine ⟨121791654566598958085723957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81194436377732638723815971 121791654566598958085723957)
                ·
                  refine ⟨11417967615618652320536621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121791654566598958085723957 11417967615618652320536621)
                  ·
                    refine ⟨4281737855856994620201233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11417967615618652320536621 4281737855856994620201233)
                    ·
                      refine ⟨3211303391892745965150925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4281737855856994620201233 3211303391892745965150925)
                      ·
                        rfl

theorem cell23_6253991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_6253991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6253991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6253991 prefixEnd_6253991 := by exact prefixLift 6253991
  have htrace : WordTrace (prefixWord ++ tailWord_6253991) baseStart_6253991 baseEnd_6253991 := by
    simpa [prefixWord, tailWord_6253991, baseEnd_6253991] using wordTrace_append hprefix tailTrace_6253991
  have hstable : (prefixWord ++ tailWord_6253991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6253991).length < 2 ^ (prefixWord ++ tailWord_6253991).sum := by decide
  have hdescent : baseEnd_6253991 < baseStart_6253991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6253991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254067 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 7]
def baseStart_6254067 : Nat := 118140960795 + 6254067 * 2 ^ 59
def prefixEnd_6254067 : Nat := 4983230072969 + 3 ^ 40 * 6254067 * 2
def baseEnd_6254067 : Nat := 3211342416422487667800575

theorem tailTrace_6254067 : CollatzResearch.WordTrace tailWord_6254067 prefixEnd_6254067 3211342416422487667800575 := by
  unfold tailWord_6254067
  simp only [CollatzResearch.WordTrace]
  refine ⟨228104563033590843452160455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152069708689060562301440303 228104563033590843452160455)
  ·
    refine ⟨342156844550386265178240683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228104563033590843452160455 342156844550386265178240683)
    ·
      refine ⟨513235266825579397767361025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342156844550386265178240683 513235266825579397767361025)
      ·
        refine ⟨384926450119184548325520769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513235266825579397767361025 384926450119184548325520769)
        ·
          refine ⟨288694837589388411244140577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384926450119184548325520769 288694837589388411244140577)
          ·
            refine ⟨216521128192041308433105433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288694837589388411244140577 216521128192041308433105433)
            ·
              refine ⟨162390846144030981324829075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216521128192041308433105433 162390846144030981324829075)
              ·
                refine ⟨243586269216046471987243613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162390846144030981324829075 243586269216046471987243613)
                ·
                  refine ⟨91344850956017426995216355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243586269216046471987243613 91344850956017426995216355)
                  ·
                    refine ⟨137017276434026140492824533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91344850956017426995216355 137017276434026140492824533)
                    ·
                      refine ⟨3211342416422487667800575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137017276434026140492824533 3211342416422487667800575)
                      ·
                        rfl

theorem cell23_6254067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_6254067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254067 prefixEnd_6254067 := by exact prefixLift 6254067
  have htrace : WordTrace (prefixWord ++ tailWord_6254067) baseStart_6254067 baseEnd_6254067 := by
    simpa [prefixWord, tailWord_6254067, baseEnd_6254067] using wordTrace_append hprefix tailTrace_6254067
  have hstable : (prefixWord ++ tailWord_6254067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254067).length < 2 ^ (prefixWord ++ tailWord_6254067).sum := by decide
  have hdescent : baseEnd_6254067 < baseStart_6254067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254074 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 2, 5]
def baseStart_6254074 : Nat := 118140960795 + 6254074 * 2 ^ 59
def prefixEnd_6254074 : Nat := 4983230072969 + 3 ^ 40 * 6254074 * 2
def baseEnd_6254074 : Nat := 1070448670262356380137681

theorem tailTrace_6254074 : CollatzResearch.WordTrace tailWord_6254074 prefixEnd_6254074 1070448670262356380137681 := by
  unfold tailWord_6254074
  simp only [CollatzResearch.WordTrace]
  refine ⟨57026204586141370911916319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152069878896376989098443517 57026204586141370911916319)
  ·
    refine ⟨85539306879212056367874479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57026204586141370911916319 85539306879212056367874479)
    ·
      refine ⟨128308960318818084551811719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85539306879212056367874479 128308960318818084551811719)
      ·
        refine ⟨192463440478227126827717579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128308960318818084551811719 192463440478227126827717579)
        ·
          refine ⟨288695160717340690241576369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192463440478227126827717579 288695160717340690241576369)
          ·
            refine ⟨216521370538005517681182277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288695160717340690241576369 216521370538005517681182277)
            ·
              refine ⟨40597756975876034565221677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216521370538005517681182277 40597756975876034565221677)
              ·
                refine ⟨15224158865953512961958129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40597756975876034565221677 15224158865953512961958129)
                ·
                  refine ⟨11418119149465134721468597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15224158865953512961958129 11418119149465134721468597)
                  ·
                    refine ⟨1070448670262356380137681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11418119149465134721468597 1070448670262356380137681)
                    ·
                      rfl

theorem cell23_6254074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_6254074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254074 prefixEnd_6254074 := by exact prefixLift 6254074
  have htrace : WordTrace (prefixWord ++ tailWord_6254074) baseStart_6254074 baseEnd_6254074 := by
    simpa [prefixWord, tailWord_6254074, baseEnd_6254074] using wordTrace_append hprefix tailTrace_6254074
  have hstable : (prefixWord ++ tailWord_6254074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254074).length < 2 ^ (prefixWord ++ tailWord_6254074).sum := by decide
  have hdescent : baseEnd_6254074 < baseStart_6254074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254091 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 2, 5]
def baseStart_6254091 : Nat := 118140960795 + 6254091 * 2 ^ 59
def prefixEnd_6254091 : Nat := 4983230072969 + 3 ^ 40 * 6254091 * 2
def baseEnd_6254091 : Nat := 1070451579986065191300155

theorem tailTrace_6254091 : CollatzResearch.WordTrace tailWord_6254091 prefixEnd_6254091 1070451579986065191300155 := by
  unfold tailWord_6254091
  simp only [CollatzResearch.WordTrace]
  refine ⟨228105438385503895551034127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152070292257002597034022751 228105438385503895551034127)
  ·
    refine ⟨342158157578255843326551191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228105438385503895551034127 342158157578255843326551191)
    ·
      refine ⟨513237236367383764989826787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342158157578255843326551191 513237236367383764989826787)
      ·
        refine ⟨769855854551075647484740181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513237236367383764989826787 769855854551075647484740181)
        ·
          refine ⟨9021748295520417743961799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 769855854551075647484740181 9021748295520417743961799)
          ·
            refine ⟨13532622443280626615942699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9021748295520417743961799 13532622443280626615942699)
            ·
              refine ⟨20298933664920939923914049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13532622443280626615942699 20298933664920939923914049)
              ·
                refine ⟨15224200248690704942935537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20298933664920939923914049 15224200248690704942935537)
                ·
                  refine ⟨11418150186518028707201653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15224200248690704942935537 11418150186518028707201653)
                  ·
                    refine ⟨1070451579986065191300155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11418150186518028707201653 1070451579986065191300155)
                    ·
                      rfl

theorem cell23_6254091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 5].length) (baseStart_6254091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254091 prefixEnd_6254091 := by exact prefixLift 6254091
  have htrace : WordTrace (prefixWord ++ tailWord_6254091) baseStart_6254091 baseEnd_6254091 := by
    simpa [prefixWord, tailWord_6254091, baseEnd_6254091] using wordTrace_append hprefix tailTrace_6254091
  have hstable : (prefixWord ++ tailWord_6254091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254091).length < 2 ^ (prefixWord ++ tailWord_6254091).sum := by decide
  have hdescent : baseEnd_6254091 < baseStart_6254091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254111 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 2, 4, 2]
def baseStart_6254111 : Nat := 118140960795 + 6254111 * 2 ^ 59
def prefixEnd_6254111 : Nat := 4983230072969 + 3 ^ 40 * 6254111 * 2
def baseEnd_6254111 : Nat := 3211365009571285495650373

theorem tailTrace_6254111 : CollatzResearch.WordTrace tailWord_6254111 prefixEnd_6254111 3211365009571285495650373 := by
  unfold tailWord_6254111
  simp only [CollatzResearch.WordTrace]
  refine ⟨228106167845431438966762187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152070778563620959311174791 228106167845431438966762187)
  ·
    refine ⟨342159251768147158450143281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228106167845431438966762187 342159251768147158450143281)
    ·
      refine ⟨256619438826110368837607461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342159251768147158450143281 256619438826110368837607461)
      ·
        refine ⟨48116144779895694157051399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256619438826110368837607461 48116144779895694157051399)
        ·
          refine ⟨72174217169843541235577099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48116144779895694157051399 72174217169843541235577099)
          ·
            refine ⟨108261325754765311853365649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72174217169843541235577099 108261325754765311853365649)
            ·
              refine ⟨81195994316073983890024237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108261325754765311853365649 81195994316073983890024237)
              ·
                refine ⟨30448497868527743958759089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81195994316073983890024237 30448497868527743958759089)
                ·
                  refine ⟨22836373401395807969069317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30448497868527743958759089 22836373401395807969069317)
                  ·
                    refine ⟨4281820012761713994200497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22836373401395807969069317 4281820012761713994200497)
                    ·
                      refine ⟨3211365009571285495650373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4281820012761713994200497 3211365009571285495650373)
                      ·
                        rfl

theorem cell23_6254111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_6254111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254111 prefixEnd_6254111 := by exact prefixLift 6254111
  have htrace : WordTrace (prefixWord ++ tailWord_6254111) baseStart_6254111 baseEnd_6254111 := by
    simpa [prefixWord, tailWord_6254111, baseEnd_6254111] using wordTrace_append hprefix tailTrace_6254111
  have hstable : (prefixWord ++ tailWord_6254111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254111).length < 2 ^ (prefixWord ++ tailWord_6254111).sum := by decide
  have hdescent : baseEnd_6254111 < baseStart_6254111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254131 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 3]
def baseStart_6254131 : Nat := 118140960795 + 6254131 * 2 ^ 59
def prefixEnd_6254131 : Nat := 4983230072969 + 3 ^ 40 * 6254131 * 2
def baseEnd_6254131 : Nat := 3211375279184375417400281

theorem tailTrace_6254131 : CollatzResearch.WordTrace tailWord_6254131 prefixEnd_6254131 3211375279184375417400281 := by
  unfold tailWord_6254131
  simp only [CollatzResearch.WordTrace]
  refine ⟨228106897305358982382490247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152071264870239321588326831 228106897305358982382490247)
  ·
    refine ⟨342160345958038473573735371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228106897305358982382490247 342160345958038473573735371)
    ·
      refine ⟨513240518937057710360603057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342160345958038473573735371 513240518937057710360603057)
      ·
        refine ⟨384930389202793282770452293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513240518937057710360603057 384930389202793282770452293)
        ·
          refine ⟨72174447975523740519459805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384930389202793282770452293 72174447975523740519459805)
          ·
            refine ⟨27065417990821402694797427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72174447975523740519459805 27065417990821402694797427)
            ·
              refine ⟨40598126986232104042196141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27065417990821402694797427 40598126986232104042196141)
              ·
                refine ⟨15224297619837039015823553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40598126986232104042196141 15224297619837039015823553)
                ·
                  refine ⟨11418223214877779261867665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15224297619837039015823553 11418223214877779261867665)
                  ·
                    refine ⟨8563667411158334446400749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11418223214877779261867665 8563667411158334446400749)
                    ·
                      refine ⟨3211375279184375417400281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8563667411158334446400749 3211375279184375417400281)
                      ·
                        rfl

theorem cell23_6254131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 3].length) (baseStart_6254131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254131 prefixEnd_6254131 := by exact prefixLift 6254131
  have htrace : WordTrace (prefixWord ++ tailWord_6254131) baseStart_6254131 baseEnd_6254131 := by
    simpa [prefixWord, tailWord_6254131, baseEnd_6254131] using wordTrace_append hprefix tailTrace_6254131
  have hstable : (prefixWord ++ tailWord_6254131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254131).length < 2 ^ (prefixWord ++ tailWord_6254131).sum := by decide
  have hdescent : baseEnd_6254131 < baseStart_6254131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254138 : List Nat := [3, 1, 1, 1, 3, 2, 2, 5, 1, 4]
def baseStart_6254138 : Nat := 118140960795 + 6254138 * 2 ^ 59
def prefixEnd_6254138 : Nat := 4983230072969 + 3 ^ 40 * 6254138 * 2
def baseEnd_6254138 : Nat := 1070459624516318963337583

theorem tailTrace_6254138 : CollatzResearch.WordTrace tailWord_6254138 prefixEnd_6254138 1070459624516318963337583 := by
  unfold tailWord_6254138
  simp only [CollatzResearch.WordTrace]
  refine ⟨57026788154083405644498767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152071435077555748385330045 57026788154083405644498767)
  ·
    refine ⟨85540182231125108466748151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57026788154083405644498767 85540182231125108466748151)
    ·
      refine ⟨128310273346687662700122227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85540182231125108466748151 128310273346687662700122227)
      ·
        refine ⟨192465410020031494050183341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128310273346687662700122227 192465410020031494050183341)
        ·
          refine ⟨72174528757511810268818753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192465410020031494050183341 72174528757511810268818753)
          ·
            refine ⟨54130896568133857701614065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72174528757511810268818753 54130896568133857701614065)
            ·
              refine ⟨40598172426100393276210549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54130896568133857701614065 40598172426100393276210549)
              ·
                refine ⟨3806078664946911869644739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40598172426100393276210549 3806078664946911869644739)
                ·
                  refine ⟨5709117997420367804467109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3806078664946911869644739 5709117997420367804467109)
                  ·
                    refine ⟨1070459624516318963337583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5709117997420367804467109 1070459624516318963337583)
                    ·
                      rfl

theorem cell23_6254138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_6254138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254138 prefixEnd_6254138 := by exact prefixLift 6254138
  have htrace : WordTrace (prefixWord ++ tailWord_6254138) baseStart_6254138 baseEnd_6254138 := by
    simpa [prefixWord, tailWord_6254138, baseEnd_6254138] using wordTrace_append hprefix tailTrace_6254138
  have hstable : (prefixWord ++ tailWord_6254138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254138).length < 2 ^ (prefixWord ++ tailWord_6254138).sum := by decide
  have hdescent : baseEnd_6254138 < baseStart_6254138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254154 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_6254154 : Nat := 118140960795 + 6254154 * 2 ^ 59
def prefixEnd_6254154 : Nat := 4983230072969 + 3 ^ 40 * 6254154 * 2
def baseEnd_6254154 : Nat := 3211387089239428827412675

theorem tailTrace_6254154 : CollatzResearch.WordTrace tailWord_6254154 prefixEnd_6254154 3211387089239428827412675 := by
  unfold tailWord_6254154
  simp only [CollatzResearch.WordTrace]
  refine ⟨57026934046068914327644379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152071824122850438207051677 57026934046068914327644379)
  ·
    refine ⟨85540401069103371491466569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57026934046068914327644379 85540401069103371491466569)
    ·
      refine ⟨64155300801827528618599927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85540401069103371491466569 64155300801827528618599927)
      ·
        refine ⟨96232951202741292927899891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64155300801827528618599927 96232951202741292927899891)
        ·
          refine ⟨144349426804111939391849837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96232951202741292927899891 144349426804111939391849837)
          ·
            refine ⟨54131035051541977271943689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144349426804111939391849837 54131035051541977271943689)
            ·
              refine ⟨40598276288656482953957767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54131035051541977271943689 40598276288656482953957767)
              ·
                refine ⟨60897414432984724430936651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40598276288656482953957767 60897414432984724430936651)
                ·
                  refine ⟨91346121649477086646404977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60897414432984724430936651 91346121649477086646404977)
                  ·
                    refine ⟨68509591237107814984803733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91346121649477086646404977 68509591237107814984803733)
                    ·
                      refine ⟨3211387089239428827412675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68509591237107814984803733 3211387089239428827412675)
                      ·
                        rfl

theorem cell23_6254154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_6254154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254154 prefixEnd_6254154 := by exact prefixLift 6254154
  have htrace : WordTrace (prefixWord ++ tailWord_6254154) baseStart_6254154 baseEnd_6254154 := by
    simpa [prefixWord, tailWord_6254154, baseEnd_6254154] using wordTrace_append hprefix tailTrace_6254154
  have hstable : (prefixWord ++ tailWord_6254154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254154).length < 2 ^ (prefixWord ++ tailWord_6254154).sum := by decide
  have hdescent : baseEnd_6254154 < baseStart_6254154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254181 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 3, 5]
def baseStart_6254181 : Nat := 118140960795 + 6254181 * 2 ^ 59
def prefixEnd_6254181 : Nat := 4983230072969 + 3 ^ 40 * 6254181 * 2
def baseEnd_6254181 : Nat := 1070466984405700073925017

theorem tailTrace_6254181 : CollatzResearch.WordTrace tailWord_6254181 prefixEnd_6254181 1070466984405700073925017 := by
  unfold tailWord_6254181
  simp only [CollatzResearch.WordTrace]
  refine ⟨228108720955177840921810397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152072480636785227281206931 228108720955177840921810397)
  ·
    refine ⟨85540770358191690345678899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228108720955177840921810397 85540770358191690345678899)
    ·
      refine ⟨128311155537287535518518349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85540770358191690345678899 128311155537287535518518349)
      ·
        refine ⟨48116683326482825819444381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128311155537287535518518349 48116683326482825819444381)
        ·
          refine ⟨18043756247431059682291643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48116683326482825819444381 18043756247431059682291643)
          ·
            refine ⟨27065634371146589523437465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18043756247431059682291643 27065634371146589523437465)
            ·
              refine ⟨20299225778359942142578099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27065634371146589523437465 20299225778359942142578099)
              ·
                refine ⟨30448838667539913213867149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20299225778359942142578099 30448838667539913213867149)
                ·
                  refine ⟨11418314500327467455200181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30448838667539913213867149 11418314500327467455200181)
                  ·
                    refine ⟨1070466984405700073925017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11418314500327467455200181 1070466984405700073925017)
                    ·
                      rfl

theorem cell23_6254181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_6254181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254181 prefixEnd_6254181 := by exact prefixLift 6254181
  have htrace : WordTrace (prefixWord ++ tailWord_6254181) baseStart_6254181 baseEnd_6254181 := by
    simpa [prefixWord, tailWord_6254181, baseEnd_6254181] using wordTrace_append hprefix tailTrace_6254181
  have hstable : (prefixWord ++ tailWord_6254181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254181).length < 2 ^ (prefixWord ++ tailWord_6254181).sum := by decide
  have hdescent : baseEnd_6254181 < baseStart_6254181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254231 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 6]
def baseStart_6254231 : Nat := 118140960795 + 6254231 * 2 ^ 59
def prefixEnd_6254231 : Nat := 4983230072969 + 3 ^ 40 * 6254231 * 2
def baseEnd_6254231 : Nat := 3211426627249825026149821

theorem tailTrace_6254231 : CollatzResearch.WordTrace tailWord_6254231 prefixEnd_6254231 3211426627249825026149821 := by
  unfold tailWord_6254231
  simp only [CollatzResearch.WordTrace]
  refine ⟨228110544604996699461130547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152073696403331132974087031 228110544604996699461130547)
  ·
    refine ⟨342165816907495049191695821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228110544604996699461130547 342165816907495049191695821)
    ·
      refine ⟨128312181340310643446885933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342165816907495049191695821 128312181340310643446885933)
      ·
        refine ⟨48117068002616491292582225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128312181340310643446885933 48117068002616491292582225)
        ·
          refine ⟨36087801001962368469436669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48117068002616491292582225 36087801001962368469436669)
          ·
            refine ⟨13532925375735888176038751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36087801001962368469436669 13532925375735888176038751)
            ·
              refine ⟨20299388063603832264058127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13532925375735888176038751 20299388063603832264058127)
              ·
                refine ⟨30449082095405748396087191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20299388063603832264058127 30449082095405748396087191)
                ·
                  refine ⟨45673623143108622594130787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30449082095405748396087191 45673623143108622594130787)
                  ·
                    refine ⟨68510434714662933891196181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45673623143108622594130787 68510434714662933891196181)
                    ·
                      refine ⟨3211426627249825026149821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68510434714662933891196181 3211426627249825026149821)
                      ·
                        rfl

theorem cell23_6254231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_6254231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254231 prefixEnd_6254231 := by exact prefixLift 6254231
  have htrace : WordTrace (prefixWord ++ tailWord_6254231) baseStart_6254231 baseEnd_6254231 := by
    simpa [prefixWord, tailWord_6254231, baseEnd_6254231] using wordTrace_append hprefix tailTrace_6254231
  have hstable : (prefixWord ++ tailWord_6254231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254231).length < 2 ^ (prefixWord ++ tailWord_6254231).sum := by decide
  have hdescent : baseEnd_6254231 < baseStart_6254231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254241 : List Nat := [1, 2, 3, 3, 2, 2, 1, 9]
def baseStart_6254241 : Nat := 118140960795 + 6254241 * 2 ^ 59
def prefixEnd_6254241 : Nat := 4983230072969 + 3 ^ 40 * 6254241 * 2
def baseEnd_6254241 : Nat := 118941917113198888408325

theorem tailTrace_6254241 : CollatzResearch.WordTrace tailWord_6254241 prefixEnd_6254241 118941917113198888408325 := by
  unfold tailWord_6254241
  simp only [CollatzResearch.WordTrace]
  refine ⟨228110909334960471168994577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152073939556640314112663051 228110909334960471168994577)
  ·
    refine ⟨171083182001220353376745933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228110909334960471168994577 171083182001220353376745933)
    ·
      refine ⟨64156193250457632516279725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171083182001220353376745933 64156193250457632516279725)
      ·
        refine ⟨24058572468921612193604897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64156193250457632516279725 24058572468921612193604897)
        ·
          refine ⟨18043929351691209145203673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24058572468921612193604897 18043929351691209145203673)
          ·
            refine ⟨13532947013768406858902755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18043929351691209145203673 13532947013768406858902755)
            ·
              refine ⟨20299420520652610288354133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13532947013768406858902755 20299420520652610288354133)
              ·
                refine ⟨118941917113198888408325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20299420520652610288354133 118941917113198888408325)
                ·
                  rfl

theorem cell23_6254241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 9].length) (baseStart_6254241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254241 prefixEnd_6254241 := by exact prefixLift 6254241
  have htrace : WordTrace (prefixWord ++ tailWord_6254241) baseStart_6254241 baseEnd_6254241 := by
    simpa [prefixWord, tailWord_6254241, baseEnd_6254241] using wordTrace_append hprefix tailTrace_6254241
  have hstable : (prefixWord ++ tailWord_6254241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254241).length < 2 ^ (prefixWord ++ tailWord_6254241).sum := by decide
  have hdescent : baseEnd_6254241 < baseStart_6254241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254269 : List Nat := [1, 4, 1, 2, 1, 2, 5, 2, 1, 2, 2]
def baseStart_6254269 : Nat := 118140960795 + 6254269 * 2 ^ 59
def prefixEnd_6254269 : Nat := 4983230072969 + 3 ^ 40 * 6254269 * 2
def baseEnd_6254269 : Nat := 3211446139514695877474647

theorem tailTrace_6254269 : CollatzResearch.WordTrace tailWord_6254269 prefixEnd_6254269 3211446139514695877474647 := by
  unfold tailWord_6254269
  simp only [CollatzResearch.WordTrace]
  refine ⟨228111930578859031951013861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152074620385906021300675907 228111930578859031951013861)
  ·
    refine ⟨42770986983536068490815099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228111930578859031951013861 42770986983536068490815099)
    ·
      refine ⟨64156480475304102736222649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42770986983536068490815099 64156480475304102736222649)
      ·
        refine ⟨48117360356478077052166987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64156480475304102736222649 48117360356478077052166987)
        ·
          refine ⟨72176040534717115578250481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48117360356478077052166987 72176040534717115578250481)
          ·
            refine ⟨54132030401037836683687861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72176040534717115578250481 54132030401037836683687861)
            ·
              refine ⟨5074877850097297189095737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54132030401037836683687861 5074877850097297189095737)
              ·
                refine ⟨3806158387572972891821803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5074877850097297189095737 3806158387572972891821803)
                ·
                  refine ⟨5709237581359459337732705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3806158387572972891821803 5709237581359459337732705)
                  ·
                    refine ⟨4281928186019594503299529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5709237581359459337732705 4281928186019594503299529)
                    ·
                      refine ⟨3211446139514695877474647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4281928186019594503299529 3211446139514695877474647)
                      ·
                        rfl

theorem cell23_6254269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_6254269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254269 prefixEnd_6254269 := by exact prefixLift 6254269
  have htrace : WordTrace (prefixWord ++ tailWord_6254269) baseStart_6254269 baseEnd_6254269 := by
    simpa [prefixWord, tailWord_6254269, baseEnd_6254269] using wordTrace_append hprefix tailTrace_6254269
  have hstable : (prefixWord ++ tailWord_6254269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254269).length < 2 ^ (prefixWord ++ tailWord_6254269).sum := by decide
  have hdescent : baseEnd_6254269 < baseStart_6254269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254371 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 5]
def baseStart_6254371 : Nat := 118140960795 + 6254371 * 2 ^ 59
def prefixEnd_6254371 : Nat := 4983230072969 + 3 ^ 40 * 6254371 * 2
def baseEnd_6254371 : Nat := 3211498514541454478399177

theorem tailTrace_6254371 : CollatzResearch.WordTrace tailWord_6254371 prefixEnd_6254371 3211498514541454478399177 := by
  unfold tailWord_6254371
  simp only [CollatzResearch.WordTrace]
  refine ⟨228115650824489503371226967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152077100549659668914151311 228115650824489503371226967)
  ·
    refine ⟨342173476236734255056840451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228115650824489503371226967 342173476236734255056840451)
    ·
      refine ⟨513260214355101382585260677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342173476236734255056840451 513260214355101382585260677)
      ·
        refine ⟨96236290191581509234736377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 513260214355101382585260677 96236290191581509234736377)
        ·
          refine ⟨72177217643686131926052283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96236290191581509234736377 72177217643686131926052283)
          ·
            refine ⟨108265826465529197889078425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72177217643686131926052283 108265826465529197889078425)
            ·
              refine ⟨81199369849146898416808819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108265826465529197889078425 81199369849146898416808819)
              ·
                refine ⟨121799054773720347625213229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81199369849146898416808819 121799054773720347625213229)
                ·
                  refine ⟨45674645540145130359454961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121799054773720347625213229 45674645540145130359454961)
                  ·
                    refine ⟨34255984155108847769591221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45674645540145130359454961 34255984155108847769591221)
                    ·
                      refine ⟨3211498514541454478399177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34255984155108847769591221 3211498514541454478399177)
                      ·
                        rfl

theorem cell23_6254371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_6254371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254371 prefixEnd_6254371 := by exact prefixLift 6254371
  have htrace : WordTrace (prefixWord ++ tailWord_6254371) baseStart_6254371 baseEnd_6254371 := by
    simpa [prefixWord, tailWord_6254371, baseEnd_6254371] using wordTrace_append hprefix tailTrace_6254371
  have hstable : (prefixWord ++ tailWord_6254371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254371).length < 2 ^ (prefixWord ++ tailWord_6254371).sum := by decide
  have hdescent : baseEnd_6254371 < baseStart_6254371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254441 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 8]
def baseStart_6254441 : Nat := 118140960795 + 6254441 * 2 ^ 59
def prefixEnd_6254441 : Nat := 4983230072969 + 3 ^ 40 * 6254441 * 2
def baseEnd_6254441 : Nat := 3211534458187269204523855

theorem tailTrace_6254441 : CollatzResearch.WordTrace tailWord_6254441 prefixEnd_6254441 3211534458187269204523855 := by
  unfold tailWord_6254441
  simp only [CollatzResearch.WordTrace]
  refine ⟨228118203934235905326275177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152078802622823936884183451 228118203934235905326275177)
  ·
    refine ⟨171088652950676928994706383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228118203934235905326275177 171088652950676928994706383)
    ·
      refine ⟨256632979426015393492059575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171088652950676928994706383 256632979426015393492059575)
      ·
        refine ⟨384949469139023090238089363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256632979426015393492059575 384949469139023090238089363)
        ·
          refine ⟨577424203708534635357134045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384949469139023090238089363 577424203708534635357134045)
          ·
            refine ⟨216534076390700488258925267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 577424203708534635357134045 216534076390700488258925267)
            ·
              refine ⟨324801114586050732388387901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216534076390700488258925267 324801114586050732388387901)
              ·
                refine ⟨121800417969769024645645463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324801114586050732388387901 121800417969769024645645463)
                ·
                  refine ⟨182700626954653536968468195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121800417969769024645645463 182700626954653536968468195)
                  ·
                    refine ⟨274050940431980305452702293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182700626954653536968468195 274050940431980305452702293)
                    ·
                      refine ⟨3211534458187269204523855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 274050940431980305452702293 3211534458187269204523855)
                      ·
                        rfl

theorem cell23_6254441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_6254441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254441 prefixEnd_6254441 := by exact prefixLift 6254441
  have htrace : WordTrace (prefixWord ++ tailWord_6254441) baseStart_6254441 baseEnd_6254441 := by
    simpa [prefixWord, tailWord_6254441, baseEnd_6254441] using wordTrace_append hprefix tailTrace_6254441
  have hstable : (prefixWord ++ tailWord_6254441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254441).length < 2 ^ (prefixWord ++ tailWord_6254441).sum := by decide
  have hdescent : baseEnd_6254441 < baseStart_6254441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254451 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 2, 9]
def baseStart_6254451 : Nat := 118140960795 + 6254451 * 2 ^ 59
def prefixEnd_6254451 : Nat := 4983230072969 + 3 ^ 40 * 6254451 * 2
def baseEnd_6254451 : Nat := 1070513197664604721799603

theorem tailTrace_6254451 : CollatzResearch.WordTrace tailWord_6254451 prefixEnd_6254451 1070513197664604721799603 := by
  unfold tailWord_6254451
  simp only [CollatzResearch.WordTrace]
  refine ⟨228118568664199677034139207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152079045776133118022759471 228118568664199677034139207)
  ·
    refine ⟨342177852996299515551208811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228118568664199677034139207 342177852996299515551208811)
    ·
      refine ⟨513266779494449273326813217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342177852996299515551208811 513266779494449273326813217)
      ·
        refine ⟨384950084620836954995109913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513266779494449273326813217 384950084620836954995109913)
        ·
          refine ⟨288712563465627716246332435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384950084620836954995109913 288712563465627716246332435)
          ·
            refine ⟨433068845198441574369498653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288712563465627716246332435 433068845198441574369498653)
            ·
              refine ⟨162400816949415590388561995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433068845198441574369498653 162400816949415590388561995)
              ·
                refine ⟨243601225424123385582842993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162400816949415590388561995 243601225424123385582842993)
                ·
                  refine ⟨182700919068092539187132245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243601225424123385582842993 182700919068092539187132245)
                  ·
                    refine ⟨1070513197664604721799603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 182700919068092539187132245 1070513197664604721799603)
                    ·
                      rfl

theorem cell23_6254451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 9].length) (baseStart_6254451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254451 prefixEnd_6254451 := by exact prefixLift 6254451
  have htrace : WordTrace (prefixWord ++ tailWord_6254451) baseStart_6254451 baseEnd_6254451 := by
    simpa [prefixWord, tailWord_6254451, baseEnd_6254451] using wordTrace_append hprefix tailTrace_6254451
  have hstable : (prefixWord ++ tailWord_6254451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254451).length < 2 ^ (prefixWord ++ tailWord_6254451).sum := by decide
  have hdescent : baseEnd_6254451 < baseStart_6254451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254508 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 3]
def baseStart_6254508 : Nat := 118140960795 + 6254508 * 2 ^ 59
def prefixEnd_6254508 : Nat := 4983230072969 + 3 ^ 40 * 6254508 * 2
def baseEnd_6254508 : Nat := 3211568861391120442386047

theorem tailTrace_6254508 : CollatzResearch.WordTrace tailWord_6254508 prefixEnd_6254508 3211568861391120442386047 := by
  unfold tailWord_6254508
  simp only [CollatzResearch.WordTrace]
  refine ⟨114060323812496587884482089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152080431749995450512642785 114060323812496587884482089)
  ·
    refine ⟨85545242859372440913361567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114060323812496587884482089 85545242859372440913361567)
    ·
      refine ⟨128317864289058661370042351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85545242859372440913361567 128317864289058661370042351)
      ·
        refine ⟨192476796433587992055063527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128317864289058661370042351 192476796433587992055063527)
        ·
          refine ⟨288715194650381988082595291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192476796433587992055063527 288715194650381988082595291)
          ·
            refine ⟨433072791975572982123892937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288715194650381988082595291 433072791975572982123892937)
            ·
              refine ⟨324804593981679736592919703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433072791975572982123892937 324804593981679736592919703)
              ·
                refine ⟨487206890972519604889379555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324804593981679736592919703 487206890972519604889379555)
                ·
                  refine ⟨730810336458779407334069333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487206890972519604889379555 730810336458779407334069333)
                  ·
                    refine ⟨8564183630376321179696125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 730810336458779407334069333 8564183630376321179696125)
                    ·
                      refine ⟨3211568861391120442386047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8564183630376321179696125 3211568861391120442386047)
                      ·
                        rfl

theorem cell23_6254508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_6254508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254508 prefixEnd_6254508 := by exact prefixLift 6254508
  have htrace : WordTrace (prefixWord ++ tailWord_6254508) baseStart_6254508 baseEnd_6254508 := by
    simpa [prefixWord, tailWord_6254508, baseEnd_6254508] using wordTrace_append hprefix tailTrace_6254508
  have hstable : (prefixWord ++ tailWord_6254508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254508).length < 2 ^ (prefixWord ++ tailWord_6254508).sum := by decide
  have hdescent : baseEnd_6254508 < baseStart_6254508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254515 : List Nat := [1, 1, 1, 2, 3, 1, 3, 5, 2, 4]
def baseStart_6254515 : Nat := 118140960795 + 6254515 * 2 ^ 59
def prefixEnd_6254515 : Nat := 4983230072969 + 3 ^ 40 * 6254515 * 2
def baseEnd_6254515 : Nat := 1070524151918567304999505

theorem tailTrace_6254515 : CollatzResearch.WordTrace tailWord_6254515 prefixEnd_6254515 1070524151918567304999505 := by
  unfold tailWord_6254515
  simp only [CollatzResearch.WordTrace]
  refine ⟨228120902935967815964468999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152080601957311877309645999 228120902935967815964468999)
  ·
    refine ⟨342181354403951723946703499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228120902935967815964468999 342181354403951723946703499)
    ·
      refine ⟨513272031605927585920055249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342181354403951723946703499 513272031605927585920055249)
      ·
        refine ⟨384954023704445689440041437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513272031605927585920055249 384954023704445689440041437)
        ·
          refine ⟨144357758889167133540015539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 384954023704445689440041437 144357758889167133540015539)
          ·
            refine ⟨216536638333750700310023309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144357758889167133540015539 216536638333750700310023309)
            ·
              refine ⟨81201239375156512616258741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216536638333750700310023309 81201239375156512616258741)
              ·
                refine ⟨7612616191420923057774257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81201239375156512616258741 7612616191420923057774257)
                ·
                  refine ⟨5709462143565692293330693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7612616191420923057774257 5709462143565692293330693)
                  ·
                    refine ⟨1070524151918567304999505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5709462143565692293330693 1070524151918567304999505)
                    ·
                      rfl

theorem cell23_6254515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 4].length) (baseStart_6254515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254515 prefixEnd_6254515 := by exact prefixLift 6254515
  have htrace : WordTrace (prefixWord ++ tailWord_6254515) baseStart_6254515 baseEnd_6254515 := by
    simpa [prefixWord, tailWord_6254515, baseEnd_6254515] using wordTrace_append hprefix tailTrace_6254515
  have hstable : (prefixWord ++ tailWord_6254515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254515).length < 2 ^ (prefixWord ++ tailWord_6254515).sum := by decide
  have hdescent : baseEnd_6254515 < baseStart_6254515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254516 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_6254516 : Nat := 118140960795 + 6254516 * 2 ^ 59
def prefixEnd_6254516 : Nat := 4983230072969 + 3 ^ 40 * 6254516 * 2
def baseEnd_6254516 : Nat := 3211572969236356411086011

theorem tailTrace_6254516 : CollatzResearch.WordTrace tailWord_6254516 prefixEnd_6254516 3211572969236356411086011 := by
  unfold tailWord_6254516
  simp only [CollatzResearch.WordTrace]
  refine ⟨114060469704482096567627701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152080626272642795423503601 114060469704482096567627701)
  ·
    refine ⟨10693169034795196553215097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114060469704482096567627701 10693169034795196553215097)
    ·
      refine ⟨8019876776096397414911323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10693169034795196553215097 8019876776096397414911323)
      ·
        refine ⟨12029815164144596122366985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8019876776096397414911323 12029815164144596122366985)
        ·
          refine ⟨9022361373108447091775239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12029815164144596122366985 9022361373108447091775239)
          ·
            refine ⟨13533542059662670637662859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9022361373108447091775239 13533542059662670637662859)
            ·
              refine ⟨20300313089494005956494289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13533542059662670637662859 20300313089494005956494289)
              ·
                refine ⟨15225234817120504467370717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20300313089494005956494289 15225234817120504467370717)
                ·
                  refine ⟨5709463056420189175264019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15225234817120504467370717 5709463056420189175264019)
                  ·
                    refine ⟨8564194584630283762896029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5709463056420189175264019 8564194584630283762896029)
                    ·
                      refine ⟨3211572969236356411086011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8564194584630283762896029 3211572969236356411086011)
                      ·
                        rfl

theorem cell23_6254516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_6254516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254516 prefixEnd_6254516 := by exact prefixLift 6254516
  have htrace : WordTrace (prefixWord ++ tailWord_6254516) baseStart_6254516 baseEnd_6254516 := by
    simpa [prefixWord, tailWord_6254516, baseEnd_6254516] using wordTrace_append hprefix tailTrace_6254516
  have hstable : (prefixWord ++ tailWord_6254516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254516).length < 2 ^ (prefixWord ++ tailWord_6254516).sum := by decide
  have hdescent : baseEnd_6254516 < baseStart_6254516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254542 : List Nat := [4, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3]
def baseStart_6254542 : Nat := 118140960795 + 6254542 * 2 ^ 59
def prefixEnd_6254542 : Nat := 4983230072969 + 3 ^ 40 * 6254542 * 2
def baseEnd_6254542 : Nat := 3211586319733373309360891

theorem tailTrace_6254542 : CollatzResearch.WordTrace tailWord_6254542 prefixEnd_6254542 3211586319733373309360891 := by
  unfold tailWord_6254542
  simp only [CollatzResearch.WordTrace]
  refine ⟨28515235963358749946962735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152081258471246666383801253 28515235963358749946962735)
  ·
    refine ⟨42772853945038124920444103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28515235963358749946962735 42772853945038124920444103)
    ·
      refine ⟨64159280917557187380666155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42772853945038124920444103 64159280917557187380666155)
      ·
        refine ⟨96238921376335781070999233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64159280917557187380666155 96238921376335781070999233)
        ·
          refine ⟨72179191032251835803249425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96238921376335781070999233 72179191032251835803249425)
          ·
            refine ⟨54134393274188876852437069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72179191032251835803249425 54134393274188876852437069)
            ·
              refine ⟨20300397477820828819663901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54134393274188876852437069 20300397477820828819663901)
              ·
                refine ⟨7612649054182810807373963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20300397477820828819663901 7612649054182810807373963)
                ·
                  refine ⟨11418973581274216211060945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7612649054182810807373963 11418973581274216211060945)
                  ·
                    refine ⟨8564230185955662158295709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11418973581274216211060945 8564230185955662158295709)
                    ·
                      refine ⟨3211586319733373309360891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8564230185955662158295709 3211586319733373309360891)
                      ·
                        rfl

theorem cell23_6254542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_6254542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254542 prefixEnd_6254542 := by exact prefixLift 6254542
  have htrace : WordTrace (prefixWord ++ tailWord_6254542) baseStart_6254542 baseEnd_6254542 := by
    simpa [prefixWord, tailWord_6254542, baseEnd_6254542] using wordTrace_append hprefix tailTrace_6254542
  have hstable : (prefixWord ++ tailWord_6254542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254542).length < 2 ^ (prefixWord ++ tailWord_6254542).sum := by decide
  have hdescent : baseEnd_6254542 < baseStart_6254542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254549 : List Nat := [1, 3, 2, 3, 2, 3, 1, 2, 2, 4]
def baseStart_6254549 : Nat := 118140960795 + 6254549 * 2 ^ 59
def prefixEnd_6254549 : Nat := 4983230072969 + 3 ^ 40 * 6254549 * 2
def baseEnd_6254549 : Nat := 1070529971365984927324453

theorem tailTrace_6254549 : CollatzResearch.WordTrace tailWord_6254549 prefixEnd_6254549 1070529971365984927324453 := by
  unfold tailWord_6254549
  simp only [CollatzResearch.WordTrace]
  refine ⟨228122143017844639771206701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152081428678563093180804467 228122143017844639771206701)
  ·
    refine ⟨85545803631691739914202513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228122143017844639771206701 85545803631691739914202513)
    ·
      refine ⟨64159352723768804935651885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85545803631691739914202513 64159352723768804935651885)
      ·
        refine ⟨24059757271413301850869457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64159352723768804935651885 24059757271413301850869457)
        ·
          refine ⟨18044817953559976388152093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24059757271413301850869457 18044817953559976388152093)
          ·
            refine ⟨6766806732584991145557035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18044817953559976388152093 6766806732584991145557035)
            ·
              refine ⟨10150210098877486718335553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6766806732584991145557035 10150210098877486718335553)
              ·
                refine ⟨7612657574158115038751665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10150210098877486718335553 7612657574158115038751665)
                ·
                  refine ⟨5709493180618586279063749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7612657574158115038751665 5709493180618586279063749)
                  ·
                    refine ⟨1070529971365984927324453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5709493180618586279063749 1070529971365984927324453)
                    ·
                      rfl

theorem cell23_6254549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_6254549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254549 prefixEnd_6254549 := by exact prefixLift 6254549
  have htrace : WordTrace (prefixWord ++ tailWord_6254549) baseStart_6254549 baseEnd_6254549 := by
    simpa [prefixWord, tailWord_6254549, baseEnd_6254549] using wordTrace_append hprefix tailTrace_6254549
  have hstable : (prefixWord ++ tailWord_6254549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254549).length < 2 ^ (prefixWord ++ tailWord_6254549).sum := by decide
  have hdescent : baseEnd_6254549 < baseStart_6254549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254572 : List Nat := [2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 3]
def baseStart_6254572 : Nat := 118140960795 + 6254572 * 2 ^ 59
def prefixEnd_6254572 : Nat := 4983230072969 + 3 ^ 40 * 6254572 * 2
def baseEnd_6254572 : Nat := 3211601724153008191985753

theorem tailTrace_6254572 : CollatzResearch.WordTrace tailWord_6254572 prefixEnd_6254572 3211601724153008191985753 := by
  unfold tailWord_6254572
  simp only [CollatzResearch.WordTrace]
  refine ⟨114061490948380657349646985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152081987931174209799529313 114061490948380657349646985)
  ·
    refine ⟨85546118211285493012235239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114061490948380657349646985 85546118211285493012235239)
    ·
      refine ⟨128319177316928239518352859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85546118211285493012235239 128319177316928239518352859)
      ·
        refine ⟨192478765975392359277529289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128319177316928239518352859 192478765975392359277529289)
        ·
          refine ⟨144359074481544269458146967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192478765975392359277529289 144359074481544269458146967)
          ·
            refine ⟨216538611722316404187220451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144359074481544269458146967 216538611722316404187220451)
            ·
              refine ⟨324807917583474606280830677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216538611722316404187220451 324807917583474606280830677)
              ·
                refine ⟨7612685568362686084706969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 324807917583474606280830677 7612685568362686084706969)
                ·
                  refine ⟨5709514176272014563530227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7612685568362686084706969 5709514176272014563530227)
                  ·
                    refine ⟨8564271264408021845295341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5709514176272014563530227 8564271264408021845295341)
                    ·
                      refine ⟨3211601724153008191985753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8564271264408021845295341 3211601724153008191985753)
                      ·
                        rfl

theorem cell23_6254572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_6254572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254572 prefixEnd_6254572 := by exact prefixLift 6254572
  have htrace : WordTrace (prefixWord ++ tailWord_6254572) baseStart_6254572 baseEnd_6254572 := by
    simpa [prefixWord, tailWord_6254572, baseEnd_6254572] using wordTrace_append hprefix tailTrace_6254572
  have hstable : (prefixWord ++ tailWord_6254572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254572).length < 2 ^ (prefixWord ++ tailWord_6254572).sum := by decide
  have hdescent : baseEnd_6254572 < baseStart_6254572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254590 : List Nat := [4, 2, 2, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_6254590 : Nat := 118140960795 + 6254590 * 2 ^ 59
def prefixEnd_6254590 : Nat := 4983230072969 + 3 ^ 40 * 6254590 * 2
def baseEnd_6254590 : Nat := 3211610966804789121560671

theorem tailTrace_6254590 : CollatzResearch.WordTrace tailWord_6254590 prefixEnd_6254590 3211610966804789121560671 := by
  unfold tailWord_6254590
  simp only [CollatzResearch.WordTrace]
  refine ⟨28515454801337012971681153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152082425607130735848966149 28515454801337012971681153)
  ·
    refine ⟨21386591101002759728760865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28515454801337012971681153 21386591101002759728760865)
    ·
      refine ⟨16039943325752069796570649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21386591101002759728760865 16039943325752069796570649)
      ·
        refine ⟨12029957494314052347427987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16039943325752069796570649 12029957494314052347427987)
        ·
          refine ⟨18044936241471078521141981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12029957494314052347427987 18044936241471078521141981)
          ·
            refine ⟨6766851090551654445428243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18044936241471078521141981 6766851090551654445428243)
            ·
              refine ⟨10150276635827481668142365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6766851090551654445428243 10150276635827481668142365)
              ·
                refine ⟨3806353738435305625553387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10150276635827481668142365 3806353738435305625553387)
                ·
                  refine ⟨5709530607652958438330081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3806353738435305625553387 5709530607652958438330081)
                  ·
                    refine ⟨4282147955739718828747561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5709530607652958438330081 4282147955739718828747561)
                    ·
                      refine ⟨3211610966804789121560671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282147955739718828747561 3211610966804789121560671)
                      ·
                        rfl

theorem cell23_6254590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_6254590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254590 prefixEnd_6254590 := by exact prefixLift 6254590
  have htrace : WordTrace (prefixWord ++ tailWord_6254590) baseStart_6254590 baseEnd_6254590 := by
    simpa [prefixWord, tailWord_6254590, baseEnd_6254590] using wordTrace_append hprefix tailTrace_6254590
  have hstable : (prefixWord ++ tailWord_6254590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254590).length < 2 ^ (prefixWord ++ tailWord_6254590).sum := by decide
  have hdescent : baseEnd_6254590 < baseStart_6254590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254599 : List Nat := [1, 1, 4, 3, 1, 2, 2, 3, 1, 3, 2]
def baseStart_6254599 : Nat := 118140960795 + 6254599 * 2 ^ 59
def prefixEnd_6254599 : Nat := 4983230072969 + 3 ^ 40 * 6254599 * 2
def baseEnd_6254599 : Nat := 3211615588130679586348129

theorem tailTrace_6254599 : CollatzResearch.WordTrace tailWord_6254599 prefixEnd_6254599 3211615588130679586348129 := by
  unfold tailWord_6254599
  simp only [CollatzResearch.WordTrace]
  refine ⟨228123966667663498310526851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152082644445108998873684567 228123966667663498310526851)
  ·
    refine ⟨342185950001495247465790277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228123966667663498310526851 342185950001495247465790277)
    ·
      refine ⟨64159865625280358899835677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 342185950001495247465790277 64159865625280358899835677)
      ·
        refine ⟨24059949609480134587438379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64159865625280358899835677 24059949609480134587438379)
        ·
          refine ⟨36089924414220201881157569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24059949609480134587438379 36089924414220201881157569)
          ·
            refine ⟨27067443310665151410868177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36089924414220201881157569 27067443310665151410868177)
            ·
              refine ⟨20300582482998863558151133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27067443310665151410868177 20300582482998863558151133)
              ·
                refine ⟨7612718431124573834306675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20300582482998863558151133 7612718431124573834306675)
                ·
                  refine ⟨11419077646686860751460013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7612718431124573834306675 11419077646686860751460013)
                  ·
                    refine ⟨4282154117507572781797505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11419077646686860751460013 4282154117507572781797505)
                    ·
                      refine ⟨3211615588130679586348129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282154117507572781797505 3211615588130679586348129)
                      ·
                        rfl

theorem cell23_6254599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_6254599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254599 prefixEnd_6254599 := by exact prefixLift 6254599
  have htrace : WordTrace (prefixWord ++ tailWord_6254599) baseStart_6254599 baseEnd_6254599 := by
    simpa [prefixWord, tailWord_6254599, baseEnd_6254599] using wordTrace_append hprefix tailTrace_6254599
  have hstable : (prefixWord ++ tailWord_6254599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254599).length < 2 ^ (prefixWord ++ tailWord_6254599).sum := by decide
  have hdescent : baseEnd_6254599 < baseStart_6254599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254652 : List Nat := [2, 2, 2, 2, 2, 1, 2, 5, 5]
def baseStart_6254652 : Nat := 118140960795 + 6254652 * 2 ^ 59
def prefixEnd_6254652 : Nat := 4983230072969 + 3 ^ 40 * 6254652 * 2
def baseEnd_6254652 : Nat := 356849200289485319887265

theorem tailTrace_6254652 : CollatzResearch.WordTrace tailWord_6254652 prefixEnd_6254652 356849200289485319887265 := by
  unfold tailWord_6254652
  simp only [CollatzResearch.WordTrace]
  refine ⟨114062949868235744181103105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152083933157647658908137473 114062949868235744181103105)
  ·
    refine ⟨85547212401176808135827329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114062949868235744181103105 85547212401176808135827329)
    ·
      refine ⟨64160409300882606101870497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85547212401176808135827329 64160409300882606101870497)
      ·
        refine ⟨48120306975661954576402873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64160409300882606101870497 48120306975661954576402873)
        ·
          refine ⟨36090230231746465932302155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48120306975661954576402873 36090230231746465932302155)
          ·
            refine ⟨54135345347619698898453233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36090230231746465932302155 54135345347619698898453233)
            ·
              refine ⟨40601509010714774173839925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54135345347619698898453233 40601509010714774173839925)
              ·
                refine ⟨3806391469754510078797493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40601509010714774173839925 3806391469754510078797493)
                ·
                  refine ⟨356849200289485319887265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3806391469754510078797493 356849200289485319887265)
                  ·
                    rfl

theorem cell23_6254652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 5].length) (baseStart_6254652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254652 prefixEnd_6254652 := by exact prefixLift 6254652
  have htrace : WordTrace (prefixWord ++ tailWord_6254652) baseStart_6254652 baseEnd_6254652 := by
    simpa [prefixWord, tailWord_6254652, baseEnd_6254652] using wordTrace_append hprefix tailTrace_6254652
  have hstable : (prefixWord ++ tailWord_6254652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254652).length < 2 ^ (prefixWord ++ tailWord_6254652).sum := by decide
  have hdescent : baseEnd_6254652 < baseStart_6254652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254665 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 2, 5]
def baseStart_6254665 : Nat := 118140960795 + 6254665 * 2 ^ 59
def prefixEnd_6254665 : Nat := 4983230072969 + 3 ^ 40 * 6254665 * 2
def baseEnd_6254665 : Nat := 1070549825951292109374275

theorem tailTrace_6254665 : CollatzResearch.WordTrace tailWord_6254665 prefixEnd_6254665 1070549825951292109374275 := by
  unfold tailWord_6254665
  simp only [CollatzResearch.WordTrace]
  refine ⟨228126373885424391582429449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152084249256949594388286299 228126373885424391582429449)
  ·
    refine ⟨171094780414068293686822087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228126373885424391582429449 171094780414068293686822087)
    ·
      refine ⟨256642170621102440530233131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171094780414068293686822087 256642170621102440530233131)
      ·
        refine ⟨384963255931653660795349697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256642170621102440530233131 384963255931653660795349697)
        ·
          refine ⟨288722441948740245596512273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384963255931653660795349697 288722441948740245596512273)
          ·
            refine ⟨216541831461555184197384205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288722441948740245596512273 216541831461555184197384205)
            ·
              refine ⟨81203186798083194074019077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216541831461555184197384205 81203186798083194074019077)
              ·
                refine ⟨15225597524640598888878577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81203186798083194074019077 15225597524640598888878577)
                ·
                  refine ⟨11419198143480449166658933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15225597524640598888878577 11419198143480449166658933)
                  ·
                    refine ⟨1070549825951292109374275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11419198143480449166658933 1070549825951292109374275)
                    ·
                      rfl

theorem cell23_6254665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 5].length) (baseStart_6254665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254665 prefixEnd_6254665 := by exact prefixLift 6254665
  have htrace : WordTrace (prefixWord ++ tailWord_6254665) baseStart_6254665 baseEnd_6254665 := by
    simpa [prefixWord, tailWord_6254665, baseEnd_6254665] using wordTrace_append hprefix tailTrace_6254665
  have hstable : (prefixWord ++ tailWord_6254665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254665).length < 2 ^ (prefixWord ++ tailWord_6254665).sum := by decide
  have hdescent : baseEnd_6254665 < baseStart_6254665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254669 : List Nat := [1, 6, 1, 1, 1, 1, 3, 4, 5]
def baseStart_6254669 : Nat := 118140960795 + 6254669 * 2 ^ 59
def prefixEnd_6254669 : Nat := 4983230072969 + 3 ^ 40 * 6254669 * 2
def baseEnd_6254669 : Nat := 356850170197388256941423

theorem tailTrace_6254669 : CollatzResearch.WordTrace tailWord_6254669 prefixEnd_6254669 356850170197388256941423 := by
  unfold tailWord_6254669
  simp only [CollatzResearch.WordTrace]
  refine ⟨228126519777409900265575061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152084346518273266843716707 228126519777409900265575061)
  ·
    refine ⟨10693430614566089074948831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 228126519777409900265575061 10693430614566089074948831)
    ·
      refine ⟨16040145921849133612423247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10693430614566089074948831 16040145921849133612423247)
      ·
        refine ⟨24060218882773700418634871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16040145921849133612423247 24060218882773700418634871)
        ·
          refine ⟨36090328324160550627952307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24060218882773700418634871 36090328324160550627952307)
          ·
            refine ⟨54135492486240825941928461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36090328324160550627952307 54135492486240825941928461)
            ·
              refine ⟨20300809682340309728223173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54135492486240825941928461 20300809682340309728223173)
              ·
                refine ⟨3806401815438808074041845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20300809682340309728223173 3806401815438808074041845)
                ·
                  refine ⟨356850170197388256941423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3806401815438808074041845 356850170197388256941423)
                  ·
                    rfl

theorem cell23_6254669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_6254669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254669 prefixEnd_6254669 := by exact prefixLift 6254669
  have htrace : WordTrace (prefixWord ++ tailWord_6254669) baseStart_6254669 baseEnd_6254669 := by
    simpa [prefixWord, tailWord_6254669, baseEnd_6254669] using wordTrace_append hprefix tailTrace_6254669
  have hstable : (prefixWord ++ tailWord_6254669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254669).length < 2 ^ (prefixWord ++ tailWord_6254669).sum := by decide
  have hdescent : baseEnd_6254669 < baseStart_6254669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254686 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 7]
def baseStart_6254686 : Nat := 118140960795 + 6254686 * 2 ^ 59
def prefixEnd_6254686 : Nat := 4983230072969 + 3 ^ 40 * 6254686 * 2
def baseEnd_6254686 : Nat := 356851140105291193995581

theorem tailTrace_6254686 : CollatzResearch.WordTrace tailWord_6254686 prefixEnd_6254686 356851140105291193995581 := by
  unfold tailWord_6254686
  simp only [CollatzResearch.WordTrace]
  refine ⟨28515892477293539021117989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152084759878898874779295941 28515892477293539021117989)
  ·
    refine ⟨5346729839492538566459623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28515892477293539021117989 5346729839492538566459623)
    ·
      refine ⟨8020094759238807849689435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5346729839492538566459623 8020094759238807849689435)
      ·
        refine ⟨12030142138858211774534153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8020094759238807849689435 12030142138858211774534153)
        ·
          refine ⟨9022606604143658830900615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12030142138858211774534153 9022606604143658830900615)
          ·
            refine ⟨13533909906215488246350923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9022606604143658830900615 13533909906215488246350923)
            ·
              refine ⟨20300864859323232369526385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13533909906215488246350923 20300864859323232369526385)
              ·
                refine ⟨15225648644492424277144789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20300864859323232369526385 15225648644492424277144789)
                ·
                  refine ⟨356851140105291193995581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15225648644492424277144789 356851140105291193995581)
                  ·
                    rfl

theorem cell23_6254686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_6254686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254686 prefixEnd_6254686 := by exact prefixLift 6254686
  have htrace : WordTrace (prefixWord ++ tailWord_6254686) baseStart_6254686 baseEnd_6254686 := by
    simpa [prefixWord, tailWord_6254686, baseEnd_6254686] using wordTrace_append hprefix tailTrace_6254686
  have hstable : (prefixWord ++ tailWord_6254686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254686).length < 2 ^ (prefixWord ++ tailWord_6254686).sum := by decide
  have hdescent : baseEnd_6254686 < baseStart_6254686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254702 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_6254702 : Nat := 118140960795 + 6254702 * 2 ^ 59
def prefixEnd_6254702 : Nat := 4983230072969 + 3 ^ 40 * 6254702 * 2
def baseEnd_6254702 : Nat := 3211668476638092683360155

theorem tailTrace_6254702 : CollatzResearch.WordTrace tailWord_6254702 prefixEnd_6254702 3211668476638092683360155 := by
  unfold tailWord_6254702
  simp only [CollatzResearch.WordTrace]
  refine ⟨28515965423286293362690795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152085148924193564601017573 28515965423286293362690795)
  ·
    refine ⟨42773948134929440044036193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28515965423286293362690795 42773948134929440044036193)
    ·
      refine ⟨32080461101197080033027145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42773948134929440044036193 32080461101197080033027145)
      ·
        refine ⟨24060345825897810024770359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32080461101197080033027145 24060345825897810024770359)
        ·
          refine ⟨36090518738846715037155539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24060345825897810024770359 36090518738846715037155539)
          ·
            refine ⟨54135778108270072555733309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36090518738846715037155539 54135778108270072555733309)
            ·
              refine ⟨20300916790601277208399991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54135778108270072555733309 20300916790601277208399991)
              ·
                refine ⟨30451375185901915812599987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20300916790601277208399991 30451375185901915812599987)
                ·
                  refine ⟨45677062778852873718899981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30451375185901915812599987 45677062778852873718899981)
                  ·
                    refine ⟨17128898542069827644587493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45677062778852873718899981 17128898542069827644587493)
                    ·
                      refine ⟨3211668476638092683360155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17128898542069827644587493 3211668476638092683360155)
                      ·
                        rfl

theorem cell23_6254702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_6254702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254702 prefixEnd_6254702 := by exact prefixLift 6254702
  have htrace : WordTrace (prefixWord ++ tailWord_6254702) baseStart_6254702 baseEnd_6254702 := by
    simpa [prefixWord, tailWord_6254702, baseEnd_6254702] using wordTrace_append hprefix tailTrace_6254702
  have hstable : (prefixWord ++ tailWord_6254702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254702).length < 2 ^ (prefixWord ++ tailWord_6254702).sum := by decide
  have hdescent : baseEnd_6254702 < baseStart_6254702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254729 : List Nat := [1, 2, 1, 1, 4, 2, 1, 6, 1, 4]
def baseStart_6254729 : Nat := 118140960795 + 6254729 * 2 ^ 59
def prefixEnd_6254729 : Nat := 4983230072969 + 3 ^ 40 * 6254729 * 2
def baseEnd_6254729 : Nat := 1070560780205254692574177

theorem tailTrace_6254729 : CollatzResearch.WordTrace tailWord_6254729 prefixEnd_6254729 1070560780205254692574177 := by
  unfold tailWord_6254729
  simp only [CollatzResearch.WordTrace]
  refine ⟨228128708157192530512759241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152085805438128353675172827 228128708157192530512759241)
  ·
    refine ⟨171096531117894397884569431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228128708157192530512759241 171096531117894397884569431)
    ·
      refine ⟨256644796676841596826854147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171096531117894397884569431 256644796676841596826854147)
      ·
        refine ⟨384967195015262395240281221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256644796676841596826854147 384967195015262395240281221)
        ·
          refine ⟨72181349065361699107552729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384967195015262395240281221 72181349065361699107552729)
          ·
            refine ⟨54136011799021274330664547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72181349065361699107552729 54136011799021274330664547)
            ·
              refine ⟨81204017698531911495996821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54136011799021274330664547 81204017698531911495996821)
              ·
                refine ⟨3806438329618683351374851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81204017698531911495996821 3806438329618683351374851)
                ·
                  refine ⟨5709657494428025027062277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3806438329618683351374851 5709657494428025027062277)
                  ·
                    refine ⟨1070560780205254692574177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5709657494428025027062277 1070560780205254692574177)
                    ·
                      rfl

theorem cell23_6254729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 1, 4].length) (baseStart_6254729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254729 prefixEnd_6254729 := by exact prefixLift 6254729
  have htrace : WordTrace (prefixWord ++ tailWord_6254729) baseStart_6254729 baseEnd_6254729 := by
    simpa [prefixWord, tailWord_6254729, baseEnd_6254729] using wordTrace_append hprefix tailTrace_6254729
  have hstable : (prefixWord ++ tailWord_6254729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254729).length < 2 ^ (prefixWord ++ tailWord_6254729).sum := by decide
  have hdescent : baseEnd_6254729 < baseStart_6254729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254779 : List Nat := [1, 1, 1, 1, 1, 2, 7, 2, 2, 3, 2]
def baseStart_6254779 : Nat := 118140960795 + 6254779 * 2 ^ 59
def prefixEnd_6254779 : Nat := 4983230072969 + 3 ^ 40 * 6254779 * 2
def baseEnd_6254779 : Nat := 3211708014648488882097301

theorem tailTrace_6254779 : CollatzResearch.WordTrace tailWord_6254779 prefixEnd_6254779 3211708014648488882097301 := by
  unfold tailWord_6254779
  simp only [CollatzResearch.WordTrace]
  refine ⟨228130531807011389052079391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152087021204674259368052927 228130531807011389052079391)
  ·
    refine ⟨342195797710517083578119087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228130531807011389052079391 342195797710517083578119087)
    ·
      refine ⟨513293696565775625367178631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342195797710517083578119087 513293696565775625367178631)
      ·
        refine ⟨769940544848663438050767947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513293696565775625367178631 769940544848663438050767947)
        ·
          refine ⟨1154910817272995157076151921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769940544848663438050767947 1154910817272995157076151921)
          ·
            refine ⟨866183112954746367807113941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1154910817272995157076151921 866183112954746367807113941)
            ·
              refine ⟨20301166709876867995479233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 866183112954746367807113941 20301166709876867995479233)
              ·
                refine ⟨15225875032407650996609425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20301166709876867995479233 15225875032407650996609425)
                ·
                  refine ⟨11419406274305738247457069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15225875032407650996609425 11419406274305738247457069)
                  ·
                    refine ⟨4282277352864651842796401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11419406274305738247457069 4282277352864651842796401)
                    ·
                      refine ⟨3211708014648488882097301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282277352864651842796401 3211708014648488882097301)
                      ·
                        rfl

theorem cell23_6254779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 3, 2].length) (baseStart_6254779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254779 prefixEnd_6254779 := by exact prefixLift 6254779
  have htrace : WordTrace (prefixWord ++ tailWord_6254779) baseStart_6254779 baseEnd_6254779 := by
    simpa [prefixWord, tailWord_6254779, baseEnd_6254779] using wordTrace_append hprefix tailTrace_6254779
  have hstable : (prefixWord ++ tailWord_6254779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254779).length < 2 ^ (prefixWord ++ tailWord_6254779).sum := by decide
  have hdescent : baseEnd_6254779 < baseStart_6254779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254792 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_6254792 : Nat := 118140960795 + 6254792 * 2 ^ 59
def prefixEnd_6254792 : Nat := 4983230072969 + 3 ^ 40 * 6254792 * 2
def baseEnd_6254792 : Nat := 3211714689896997331234741

theorem tailTrace_6254792 : CollatzResearch.WordTrace tailWord_6254792 prefixEnd_6254792 3211714689896997331234741 := by
  unfold tailWord_6254792
  simp only [CollatzResearch.WordTrace]
  refine ⟨114065502977982146136151315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152087337303976194848201753 114065502977982146136151315)
  ·
    refine ⟨171098254466973219204226973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114065502977982146136151315 171098254466973219204226973)
    ·
      refine ⟨64161845425114957201585115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171098254466973219204226973 64161845425114957201585115)
      ·
        refine ⟨96242768137672435802377673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64161845425114957201585115 96242768137672435802377673)
        ·
          refine ⟨72182076103254326851783255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96242768137672435802377673 72182076103254326851783255)
          ·
            refine ⟨108273114154881490277674883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72182076103254326851783255 108273114154881490277674883)
            ·
              refine ⟨162409671232322235416512325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108273114154881490277674883 162409671232322235416512325)
              ·
                refine ⟨30451813356060419140596061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162409671232322235416512325 30451813356060419140596061)
                ·
                  refine ⟨11419430008522657177723523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30451813356060419140596061 11419430008522657177723523)
                  ·
                    refine ⟨17129145012783985766585285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11419430008522657177723523 17129145012783985766585285)
                    ·
                      refine ⟨3211714689896997331234741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17129145012783985766585285 3211714689896997331234741)
                      ·
                        rfl

theorem cell23_6254792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_6254792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254792 prefixEnd_6254792 := by exact prefixLift 6254792
  have htrace : WordTrace (prefixWord ++ tailWord_6254792) baseStart_6254792 baseEnd_6254792 := by
    simpa [prefixWord, tailWord_6254792, baseEnd_6254792] using wordTrace_append hprefix tailTrace_6254792
  have hstable : (prefixWord ++ tailWord_6254792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254792).length < 2 ^ (prefixWord ++ tailWord_6254792).sum := by decide
  have hdescent : baseEnd_6254792 < baseStart_6254792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254806 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_6254806 : Nat := 118140960795 + 6254806 * 2 ^ 59
def prefixEnd_6254806 : Nat := 4983230072969 + 3 ^ 40 * 6254806 * 2
def baseEnd_6254806 : Nat := 1070573959542053425486559

theorem tailTrace_6254806 : CollatzResearch.WordTrace tailWord_6254806 prefixEnd_6254806 1070573959542053425486559 := by
  unfold tailWord_6254806
  simp only [CollatzResearch.WordTrace]
  refine ⟨14258219786119598291457017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152087677718609048442208181 14258219786119598291457017)
  ·
    refine ⟨10693664839589698718592763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14258219786119598291457017 10693664839589698718592763)
    ·
      refine ⟨16040497259384548077889145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10693664839589698718592763 16040497259384548077889145)
      ·
        refine ⟨12030372944538411058416859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16040497259384548077889145 12030372944538411058416859)
        ·
          refine ⟨18045559416807616587625289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12030372944538411058416859 18045559416807616587625289)
          ·
            refine ⟨13534169562605712440718967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18045559416807616587625289 13534169562605712440718967)
            ·
              refine ⟨20301254343908568661078451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13534169562605712440718967 20301254343908568661078451)
              ·
                refine ⟨30451881515862852991617677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20301254343908568661078451 30451881515862852991617677)
                ·
                  refine ⟨11419455568448569871856629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30451881515862852991617677 11419455568448569871856629)
                  ·
                    refine ⟨1070573959542053425486559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11419455568448569871856629 1070573959542053425486559)
                    ·
                      rfl

theorem cell23_6254806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_6254806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254806 prefixEnd_6254806 := by exact prefixLift 6254806
  have htrace : WordTrace (prefixWord ++ tailWord_6254806) baseStart_6254806 baseEnd_6254806 := by
    simpa [prefixWord, tailWord_6254806, baseEnd_6254806] using wordTrace_append hprefix tailTrace_6254806
  have hstable : (prefixWord ++ tailWord_6254806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254806).length < 2 ^ (prefixWord ++ tailWord_6254806).sum := by decide
  have hdescent : baseEnd_6254806 < baseStart_6254806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254809 : List Nat := [1, 2, 1, 2, 3, 1, 5, 2, 1, 1, 4]
def baseStart_6254809 : Nat := 118140960795 + 6254809 * 2 ^ 59
def prefixEnd_6254809 : Nat := 4983230072969 + 3 ^ 40 * 6254809 * 2
def baseEnd_6254809 : Nat := 3211723419068123764722163

theorem tailTrace_6254809 : CollatzResearch.WordTrace tailWord_6254809 prefixEnd_6254809 3211723419068123764722163 := by
  unfold tailWord_6254809
  simp only [CollatzResearch.WordTrace]
  refine ⟨228131625996902704175671481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152087750664601802783780987 228131625996902704175671481)
  ·
    refine ⟨171098719497677028131753611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228131625996902704175671481 171098719497677028131753611)
    ·
      refine ⟨256648079246515542197630417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171098719497677028131753611 256648079246515542197630417)
      ·
        refine ⟨192486059434886656648222813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256648079246515542197630417 192486059434886656648222813)
        ·
          refine ⟨72182272288082496243083555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192486059434886656648222813 72182272288082496243083555)
          ·
            refine ⟨108273408432123744364625333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72182272288082496243083555 108273408432123744364625333)
            ·
              refine ⟨10150632040511601034183625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108273408432123744364625333 10150632040511601034183625)
              ·
                refine ⟨7612974030383700775637719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10150632040511601034183625 7612974030383700775637719)
                ·
                  refine ⟨11419461045575551163456579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7612974030383700775637719 11419461045575551163456579)
                  ·
                    refine ⟨17129191568363326745184869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11419461045575551163456579 17129191568363326745184869)
                    ·
                      refine ⟨3211723419068123764722163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17129191568363326745184869 3211723419068123764722163)
                      ·
                        rfl

theorem cell23_6254809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_6254809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254809 prefixEnd_6254809 := by exact prefixLift 6254809
  have htrace : WordTrace (prefixWord ++ tailWord_6254809) baseStart_6254809 baseEnd_6254809 := by
    simpa [prefixWord, tailWord_6254809, baseEnd_6254809] using wordTrace_append hprefix tailTrace_6254809
  have hstable : (prefixWord ++ tailWord_6254809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254809).length < 2 ^ (prefixWord ++ tailWord_6254809).sum := by decide
  have hdescent : baseEnd_6254809 < baseStart_6254809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254813 : List Nat := [1, 4, 3, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_6254813 : Nat := 118140960795 + 6254813 * 2 ^ 59
def prefixEnd_6254813 : Nat := 4983230072969 + 3 ^ 40 * 6254813 * 2
def baseEnd_6254813 : Nat := 3211725472990741749072145

theorem tailTrace_6254813 : CollatzResearch.WordTrace tailWord_6254813 prefixEnd_6254813 3211725472990741749072145 := by
  unfold tailWord_6254813
  simp only [CollatzResearch.WordTrace]
  refine ⟨228131771888888212858817093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152087847925925475239211395 228131771888888212858817093)
  ·
    refine ⟨42774707229166539911028205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228131771888888212858817093 42774707229166539911028205)
    ·
      refine ⟨16040515210937452466635577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42774707229166539911028205 16040515210937452466635577)
      ·
        refine ⟨12030386408203089349976683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16040515210937452466635577 12030386408203089349976683)
        ·
          refine ⟨18045579612304634024965025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12030386408203089349976683 18045579612304634024965025)
          ·
            refine ⟨13534184709228475518723769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18045579612304634024965025 13534184709228475518723769)
            ·
              refine ⟨10150638531921356639042827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13534184709228475518723769 10150638531921356639042827)
              ·
                refine ⟨15225957797882034958564241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10150638531921356639042827 15225957797882034958564241)
                ·
                  refine ⟨11419468348411526218923181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15225957797882034958564241 11419468348411526218923181)
                  ·
                    refine ⟨4282300630654322332096193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11419468348411526218923181 4282300630654322332096193)
                    ·
                      refine ⟨3211725472990741749072145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282300630654322332096193 3211725472990741749072145)
                      ·
                        rfl

theorem cell23_6254813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_6254813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254813 prefixEnd_6254813 := by exact prefixLift 6254813
  have htrace : WordTrace (prefixWord ++ tailWord_6254813) baseStart_6254813 baseEnd_6254813 := by
    simpa [prefixWord, tailWord_6254813, baseEnd_6254813] using wordTrace_append hprefix tailTrace_6254813
  have hstable : (prefixWord ++ tailWord_6254813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254813).length < 2 ^ (prefixWord ++ tailWord_6254813).sum := by decide
  have hdescent : baseEnd_6254813 < baseStart_6254813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254826 : List Nat := [3, 1, 3, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_6254826 : Nat := 118140960795 + 6254826 * 2 ^ 59
def prefixEnd_6254826 : Nat := 4983230072969 + 3 ^ 40 * 6254826 * 2
def baseEnd_6254826 : Nat := 3211732148239250198209585

theorem tailTrace_6254826 : CollatzResearch.WordTrace tailWord_6254826 prefixEnd_6254826 3211732148239250198209585 := by
  unfold tailWord_6254826
  simp only [CollatzResearch.WordTrace]
  refine ⟨57033061509460279019760083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152088164025227410719360221 57033061509460279019760083)
  ·
    refine ⟨85549592264190418529640125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57033061509460279019760083 85549592264190418529640125)
    ·
      refine ⟨32081097099071406948615047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85549592264190418529640125 32081097099071406948615047)
      ·
        refine ⟨48121645648607110422922571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32081097099071406948615047 48121645648607110422922571)
        ·
          refine ⟨72182468472910665634383857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48121645648607110422922571 72182468472910665634383857)
          ·
            refine ⟨54136851354682999225787893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72182468472910665634383857 54136851354682999225787893)
            ·
              refine ⟨5075329814501531177417615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54136851354682999225787893 5075329814501531177417615)
              ·
                refine ⟨7612994721752296766126423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5075329814501531177417615 7612994721752296766126423)
                ·
                  refine ⟨11419492082628445149189635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7612994721752296766126423 11419492082628445149189635)
                  ·
                    refine ⟨17129238123942667723784453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11419492082628445149189635 17129238123942667723784453)
                    ·
                      refine ⟨3211732148239250198209585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17129238123942667723784453 3211732148239250198209585)
                      ·
                        rfl

theorem cell23_6254826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_6254826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254826 prefixEnd_6254826 := by exact prefixLift 6254826
  have htrace : WordTrace (prefixWord ++ tailWord_6254826) baseStart_6254826 baseEnd_6254826 := by
    simpa [prefixWord, tailWord_6254826, baseEnd_6254826] using wordTrace_append hprefix tailTrace_6254826
  have hstable : (prefixWord ++ tailWord_6254826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254826).length < 2 ^ (prefixWord ++ tailWord_6254826).sum := by decide
  have hdescent : baseEnd_6254826 < baseStart_6254826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254859 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 3]
def baseStart_6254859 : Nat := 118140960795 + 6254859 * 2 ^ 59
def prefixEnd_6254859 : Nat := 4983230072969 + 3 ^ 40 * 6254859 * 2
def baseEnd_6254859 : Nat := 3211749093100848569096933

theorem tailTrace_6254859 : CollatzResearch.WordTrace tailWord_6254859 prefixEnd_6254859 3211749093100848569096933 := by
  unfold tailWord_6254859
  simp only [CollatzResearch.WordTrace]
  refine ⟨228133449646721562714991631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152088966431147708476661087 228133449646721562714991631)
  ·
    refine ⟨342200174470082344072487447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228133449646721562714991631 342200174470082344072487447)
    ·
      refine ⟨513300261705123516108731171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342200174470082344072487447 513300261705123516108731171)
      ·
        refine ⟨769950392557685274163096757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513300261705123516108731171 769950392557685274163096757)
        ·
          refine ⟨72182849302282994452790321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 769950392557685274163096757 72182849302282994452790321)
          ·
            refine ⟨54137136976712245839592741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72182849302282994452790321 54137136976712245839592741)
            ·
              refine ⟨10150713183133546094923639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54137136976712245839592741 10150713183133546094923639)
              ·
                refine ⟨15226069774700319142385459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10150713183133546094923639 15226069774700319142385459)
                ·
                  refine ⟨22839104662050478713578189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15226069774700319142385459 22839104662050478713578189)
                  ·
                    refine ⟨8564664248268929517591821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22839104662050478713578189 8564664248268929517591821)
                    ·
                      refine ⟨3211749093100848569096933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8564664248268929517591821 3211749093100848569096933)
                      ·
                        rfl

theorem cell23_6254859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 3].length) (baseStart_6254859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254859 prefixEnd_6254859 := by exact prefixLift 6254859
  have htrace : WordTrace (prefixWord ++ tailWord_6254859) baseStart_6254859 baseEnd_6254859 := by
    simpa [prefixWord, tailWord_6254859, baseEnd_6254859] using wordTrace_append hprefix tailTrace_6254859
  have hstable : (prefixWord ++ tailWord_6254859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254859).length < 2 ^ (prefixWord ++ tailWord_6254859).sum := by decide
  have hdescent : baseEnd_6254859 < baseStart_6254859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254862 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_6254862 : Nat := 118140960795 + 6254862 * 2 ^ 59
def prefixEnd_6254862 : Nat := 4983230072969 + 3 ^ 40 * 6254862 * 2
def baseEnd_6254862 : Nat := 1070583544514270685786473

theorem tailTrace_6254862 : CollatzResearch.WordTrace tailWord_6254862 prefixEnd_6254862 1070583544514270685786473 := by
  unfold tailWord_6254862
  simp only [CollatzResearch.WordTrace]
  refine ⟨28516694883213836778418855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152089039377140462818233893 28516694883213836778418855)
  ·
    refine ⟨42775042324820755167628283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28516694883213836778418855 42775042324820755167628283)
    ·
      refine ⟨64162563487231132751442425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42775042324820755167628283 64162563487231132751442425)
      ·
        refine ⟨48121922615423349563581819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64162563487231132751442425 48121922615423349563581819)
        ·
          refine ⟨72182883923135024345372729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48121922615423349563581819 72182883923135024345372729)
          ·
            refine ⟨54137162942351268259029547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72182883923135024345372729 54137162942351268259029547)
            ·
              refine ⟨81205744413526902388544321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54137162942351268259029547 81205744413526902388544321)
              ·
                refine ⟨60904308310145176791408241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81205744413526902388544321 60904308310145176791408241)
                ·
                  refine ⟨45678231232608882593556181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60904308310145176791408241 45678231232608882593556181)
                  ·
                    refine ⟨1070583544514270685786473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45678231232608882593556181 1070583544514270685786473)
                    ·
                      rfl

theorem cell23_6254862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_6254862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254862 prefixEnd_6254862 := by exact prefixLift 6254862
  have htrace : WordTrace (prefixWord ++ tailWord_6254862) baseStart_6254862 baseEnd_6254862 := by
    simpa [prefixWord, tailWord_6254862, baseEnd_6254862] using wordTrace_append hprefix tailTrace_6254862
  have hstable : (prefixWord ++ tailWord_6254862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254862).length < 2 ^ (prefixWord ++ tailWord_6254862).sum := by decide
  have hdescent : baseEnd_6254862 < baseStart_6254862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254872 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_6254872 : Nat := 118140960795 + 6254872 * 2 ^ 59
def prefixEnd_6254872 : Nat := 4983230072969 + 3 ^ 40 * 6254872 * 2
def baseEnd_6254872 : Nat := 3211755768349357018234373

theorem tailTrace_6254872 : CollatzResearch.WordTrace tailWord_6254872 prefixEnd_6254872 3211755768349357018234373 := by
  unfold tailWord_6254872
  simp only [CollatzResearch.WordTrace]
  refine ⟨114066961897837232967607435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152089282530449643956809913 114066961897837232967607435)
  ·
    refine ⟨171100442846755849451411153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114066961897837232967607435 171100442846755849451411153)
    ·
      refine ⟨128325332135066887088558365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171100442846755849451411153 128325332135066887088558365)
      ·
        refine ⟨48121999550650082658209387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128325332135066887088558365 48121999550650082658209387)
        ·
          refine ⟨72182999325975123987314081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48121999550650082658209387 72182999325975123987314081)
          ·
            refine ⟨54137249494481342990485561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72182999325975123987314081 54137249494481342990485561)
            ·
              refine ⟨40602937120861007242864171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54137249494481342990485561 40602937120861007242864171)
              ·
                refine ⟨60904405681291510864296257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40602937120861007242864171 60904405681291510864296257)
                ·
                  refine ⟨45678304260968633148222193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60904405681291510864296257 45678304260968633148222193)
                  ·
                    refine ⟨34258728195726474861166645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45678304260968633148222193 34258728195726474861166645)
                    ·
                      refine ⟨3211755768349357018234373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34258728195726474861166645 3211755768349357018234373)
                      ·
                        rfl

theorem cell23_6254872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_6254872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254872 prefixEnd_6254872 := by exact prefixLift 6254872
  have htrace : WordTrace (prefixWord ++ tailWord_6254872) baseStart_6254872 baseEnd_6254872 := by
    simpa [prefixWord, tailWord_6254872, baseEnd_6254872] using wordTrace_append hprefix tailTrace_6254872
  have hstable : (prefixWord ++ tailWord_6254872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254872).length < 2 ^ (prefixWord ++ tailWord_6254872).sum := by decide
  have hdescent : baseEnd_6254872 < baseStart_6254872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254877 : List Nat := [1, 4, 2, 3, 2, 1, 2, 3, 1, 2, 2]
def baseStart_6254877 : Nat := 118140960795 + 6254877 * 2 ^ 59
def prefixEnd_6254877 : Nat := 4983230072969 + 3 ^ 40 * 6254877 * 2
def baseEnd_6254877 : Nat := 3211758335752629498671851

theorem tailTrace_6254877 : CollatzResearch.WordTrace tailWord_6254877 prefixEnd_6254877 3211758335752629498671851 := by
  unfold tailWord_6254877
  simp only [CollatzResearch.WordTrace]
  refine ⟨228134106160656351789146885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152089404107104234526097923 228134106160656351789146885)
  ·
    refine ⟨42775144905123065960465041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228134106160656351789146885 42775144905123065960465041)
    ·
      refine ⟨32081358678842299470348781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42775144905123065960465041 32081358678842299470348781)
      ·
        refine ⟨12030509504565862301380793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32081358678842299470348781 12030509504565862301380793)
        ·
          refine ⟨9022882128424396726035595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12030509504565862301380793 9022882128424396726035595)
          ·
            refine ⟨13534323192636595089053393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9022882128424396726035595 13534323192636595089053393)
            ·
              refine ⟨10150742394477446316790045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13534323192636595089053393 10150742394477446316790045)
              ·
                refine ⟨3806528397929042368796267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10150742394477446316790045 3806528397929042368796267)
                ·
                  refine ⟨5709792596893563553194401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3806528397929042368796267 5709792596893563553194401)
                  ·
                    refine ⟨4282344447670172664895801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5709792596893563553194401 4282344447670172664895801)
                    ·
                      refine ⟨3211758335752629498671851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282344447670172664895801 3211758335752629498671851)
                      ·
                        rfl

theorem cell23_6254877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_6254877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254877 prefixEnd_6254877 := by exact prefixLift 6254877
  have htrace : WordTrace (prefixWord ++ tailWord_6254877) baseStart_6254877 baseEnd_6254877 := by
    simpa [prefixWord, tailWord_6254877, baseEnd_6254877] using wordTrace_append hprefix tailTrace_6254877
  have hstable : (prefixWord ++ tailWord_6254877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254877).length < 2 ^ (prefixWord ++ tailWord_6254877).sum := by decide
  have hdescent : baseEnd_6254877 < baseStart_6254877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254887 : List Nat := [1, 1, 8, 1, 1, 2, 1, 2, 2, 4]
def baseStart_6254887 : Nat := 118140960795 + 6254887 * 2 ^ 59
def prefixEnd_6254887 : Nat := 4983230072969 + 3 ^ 40 * 6254887 * 2
def baseEnd_6254887 : Nat := 1070587823519724819848935

theorem tailTrace_6254887 : CollatzResearch.WordTrace tailWord_6254887 prefixEnd_6254887 1070587823519724819848935 := by
  unfold tailWord_6254887
  simp only [CollatzResearch.WordTrace]
  refine ⟨228134470890620123497010915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152089647260413415664673943 228134470890620123497010915)
  ·
    refine ⟨342201706335930185245516373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228134470890620123497010915 342201706335930185245516373)
    ·
      refine ⟨4010176246124181858345895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 342201706335930185245516373 4010176246124181858345895)
      ·
        refine ⟨6015264369186272787518843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4010176246124181858345895 6015264369186272787518843)
        ·
          refine ⟨9022896553779409181278265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6015264369186272787518843 9022896553779409181278265)
          ·
            refine ⟨6767172415334556885958699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9022896553779409181278265 6767172415334556885958699)
            ·
              refine ⟨10150758623001835328938049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6767172415334556885958699 10150758623001835328938049)
              ·
                refine ⟨7613068967251376496703537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10150758623001835328938049 7613068967251376496703537)
                ·
                  refine ⟨5709801725438532372527653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7613068967251376496703537 5709801725438532372527653)
                  ·
                    refine ⟨1070587823519724819848935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5709801725438532372527653 1070587823519724819848935)
                    ·
                      rfl

theorem cell23_6254887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_6254887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254887 prefixEnd_6254887 := by exact prefixLift 6254887
  have htrace : WordTrace (prefixWord ++ tailWord_6254887) baseStart_6254887 baseEnd_6254887 := by
    simpa [prefixWord, tailWord_6254887, baseEnd_6254887] using wordTrace_append hprefix tailTrace_6254887
  have hstable : (prefixWord ++ tailWord_6254887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254887).length < 2 ^ (prefixWord ++ tailWord_6254887).sum := by decide
  have hdescent : baseEnd_6254887 < baseStart_6254887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254892 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 2, 6]
def baseStart_6254892 : Nat := 118140960795 + 6254892 * 2 ^ 59
def prefixEnd_6254892 : Nat := 4983230072969 + 3 ^ 40 * 6254892 * 2
def baseEnd_6254892 : Nat := 1070588679320815646661427

theorem tailTrace_6254892 : CollatzResearch.WordTrace tailWord_6254892 prefixEnd_6254892 1070588679320815646661427 := by
  unfold tailWord_6254892
  simp only [CollatzResearch.WordTrace]
  refine ⟨114067326627801004675471465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152089768837068006233961953 114067326627801004675471465)
  ·
    refine ⟨85550494970850753506603599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114067326627801004675471465 85550494970850753506603599)
    ·
      refine ⟨128325742456276130259905399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85550494970850753506603599 128325742456276130259905399)
      ·
        refine ⟨192488613684414195389858099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128325742456276130259905399 192488613684414195389858099)
        ·
          refine ⟨288732920526621293084787149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192488613684414195389858099 288732920526621293084787149)
          ·
            refine ⟨108274845197482984906795181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288732920526621293084787149 108274845197482984906795181)
            ·
              refine ⟨40603066949056119340048193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108274845197482984906795181 40603066949056119340048193)
              ·
                refine ⟨30452300211792089505036145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40603066949056119340048193 30452300211792089505036145)
                ·
                  refine ⟨22839225158844067128777109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30452300211792089505036145 22839225158844067128777109)
                  ·
                    refine ⟨1070588679320815646661427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22839225158844067128777109 1070588679320815646661427)
                    ·
                      rfl

theorem cell23_6254892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_6254892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254892 prefixEnd_6254892 := by exact prefixLift 6254892
  have htrace : WordTrace (prefixWord ++ tailWord_6254892) baseStart_6254892 baseEnd_6254892 := by
    simpa [prefixWord, tailWord_6254892, baseEnd_6254892] using wordTrace_append hprefix tailTrace_6254892
  have hstable : (prefixWord ++ tailWord_6254892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254892).length < 2 ^ (prefixWord ++ tailWord_6254892).sum := by decide
  have hdescent : baseEnd_6254892 < baseStart_6254892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254910 : List Nat := [4, 2, 1, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_6254910 : Nat := 118140960795 + 6254910 * 2 ^ 59
def prefixEnd_6254910 : Nat := 4983230072969 + 3 ^ 40 * 6254910 * 2
def baseEnd_6254910 : Nat := 3211775280614227869559199

theorem tailTrace_6254910 : CollatzResearch.WordTrace tailWord_6254910 prefixEnd_6254910 3211775280614227869559199 := by
  unfold tailWord_6254910
  simp only [CollatzResearch.WordTrace]
  refine ⟨28516913721192099803137273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152090206513024532283398789 28516913721192099803137273)
  ·
    refine ⟨21387685290894074852352955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28516913721192099803137273 21387685290894074852352955)
    ·
      refine ⟨32081527936341112278529433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21387685290894074852352955 32081527936341112278529433)
      ·
        refine ⟨24061145952255834208897075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32081527936341112278529433 24061145952255834208897075)
        ·
          refine ⟨36091718928383751313345613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24061145952255834208897075 36091718928383751313345613)
          ·
            refine ⟨13534394598143906742504605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36091718928383751313345613 13534394598143906742504605)
            ·
              refine ⟨5075397974303965028439227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13534394598143906742504605 5075397974303965028439227)
              ·
                refine ⟨7613096961455947542658841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5075397974303965028439227 7613096961455947542658841)
                ·
                  refine ⟨5709822721091960656994131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7613096961455947542658841 5709822721091960656994131)
                  ·
                    refine ⟨8564734081637940985491197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5709822721091960656994131 8564734081637940985491197)
                    ·
                      refine ⟨3211775280614227869559199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8564734081637940985491197 3211775280614227869559199)
                      ·
                        rfl

theorem cell23_6254910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_6254910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254910 prefixEnd_6254910 := by exact prefixLift 6254910
  have htrace : WordTrace (prefixWord ++ tailWord_6254910) baseStart_6254910 baseEnd_6254910 := by
    simpa [prefixWord, tailWord_6254910, baseEnd_6254910] using wordTrace_append hprefix tailTrace_6254910
  have hstable : (prefixWord ++ tailWord_6254910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254910).length < 2 ^ (prefixWord ++ tailWord_6254910).sum := by decide
  have hdescent : baseEnd_6254910 < baseStart_6254910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254912 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 4]
def baseStart_6254912 : Nat := 118140960795 + 6254912 * 2 ^ 59
def prefixEnd_6254912 : Nat := 4983230072969 + 3 ^ 40 * 6254912 * 2
def baseEnd_6254912 : Nat := 3211776307575536861734189

theorem tailTrace_6254912 : CollatzResearch.WordTrace tailWord_6254912 prefixEnd_6254912 3211776307575536861734189 := by
  unfold tailWord_6254912
  simp only [CollatzResearch.WordTrace]
  refine ⟨114067691357764776383335495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152090255143686368511113993 114067691357764776383335495)
  ·
    refine ⟨171101537036647164575003243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114067691357764776383335495 171101537036647164575003243)
    ·
      refine ⟨256652305554970746862504865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171101537036647164575003243 256652305554970746862504865)
      ·
        refine ⟨192489229166228060146878649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256652305554970746862504865 192489229166228060146878649)
        ·
          refine ⟨144366921874671045110158987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192489229166228060146878649 144366921874671045110158987)
          ·
            refine ⟨216550382812006567665238481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144366921874671045110158987 216550382812006567665238481)
            ·
              refine ⟨162412787109004925748928861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216550382812006567665238481 162412787109004925748928861)
              ·
                refine ⟨60904795165876847155848323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162412787109004925748928861 60904795165876847155848323)
                ·
                  refine ⟨91357192748815270733772485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60904795165876847155848323 91357192748815270733772485)
                  ·
                    refine ⟨17129473640402863262582341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91357192748815270733772485 17129473640402863262582341)
                    ·
                      refine ⟨3211776307575536861734189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17129473640402863262582341 3211776307575536861734189)
                      ·
                        rfl

theorem cell23_6254912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_6254912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254912 prefixEnd_6254912 := by exact prefixLift 6254912
  have htrace : WordTrace (prefixWord ++ tailWord_6254912) baseStart_6254912 baseEnd_6254912 := by
    simpa [prefixWord, tailWord_6254912, baseEnd_6254912] using wordTrace_append hprefix tailTrace_6254912
  have hstable : (prefixWord ++ tailWord_6254912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254912).length < 2 ^ (prefixWord ++ tailWord_6254912).sum := by decide
  have hdescent : baseEnd_6254912 < baseStart_6254912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6254956 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 7]
def baseStart_6254956 : Nat := 118140960795 + 6254956 * 2 ^ 59
def prefixEnd_6254956 : Nat := 4983230072969 + 3 ^ 40 * 6254956 * 2
def baseEnd_6254956 : Nat := 356866544524926076620443

theorem tailTrace_6254956 : CollatzResearch.WordTrace tailWord_6254956 prefixEnd_6254956 356866544524926076620443 := by
  unfold tailWord_6254956
  simp only [CollatzResearch.WordTrace]
  refine ⟨114068493763685074140636361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152091325018246765520848481 114068493763685074140636361)
  ·
    refine ⟨85551370322763805605477271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114068493763685074140636361 85551370322763805605477271)
    ·
      refine ⟨128327055484145708408215907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85551370322763805605477271 128327055484145708408215907)
      ·
        refine ⟨192490583226218562612323861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128327055484145708408215907 192490583226218562612323861)
        ·
          refine ⟨9022996088728995122452681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 192490583226218562612323861 9022996088728995122452681)
          ·
            refine ⟨6767247066546746341839511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9022996088728995122452681 6767247066546746341839511)
            ·
              refine ⟨10150870599820119512759267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6767247066546746341839511 10150870599820119512759267)
              ·
                refine ⟨15226305899730179269138901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10150870599820119512759267 15226305899730179269138901)
                ·
                  refine ⟨356866544524926076620443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15226305899730179269138901 356866544524926076620443)
                  ·
                    rfl

theorem cell23_6254956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 7].length) (baseStart_6254956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6254956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6254956 prefixEnd_6254956 := by exact prefixLift 6254956
  have htrace : WordTrace (prefixWord ++ tailWord_6254956) baseStart_6254956 baseEnd_6254956 := by
    simpa [prefixWord, tailWord_6254956, baseEnd_6254956] using wordTrace_append hprefix tailTrace_6254956
  have hstable : (prefixWord ++ tailWord_6254956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6254956).length < 2 ^ (prefixWord ++ tailWord_6254956).sum := by decide
  have hdescent : baseEnd_6254956 < baseStart_6254956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6254956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255073 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 3, 1, 3]
def baseStart_6255073 : Nat := 118140960795 + 6255073 * 2 ^ 59
def prefixEnd_6255073 : Nat := 4983230072969 + 3 ^ 40 * 6255073 * 2
def baseEnd_6255073 : Nat := 3211858977960910731820949

theorem tailTrace_6255073 : CollatzResearch.WordTrace tailWord_6255073 prefixEnd_6255073 3211858977960910731820949 := by
  unfold tailWord_6255073
  simp only [CollatzResearch.WordTrace]
  refine ⟨228141254867946277263281873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152094169911964184842187915 228141254867946277263281873)
  ·
    refine ⟨171105941150959707947461405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228141254867946277263281873 171105941150959707947461405)
    ·
      refine ⟨64164727931609890480298027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171105941150959707947461405 64164727931609890480298027)
      ·
        refine ⟨96247091897414835720447041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64164727931609890480298027 96247091897414835720447041)
        ·
          refine ⟨72185318923061126790335281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96247091897414835720447041 72185318923061126790335281)
          ·
            refine ⟨54138989192295845092751461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72185318923061126790335281 54138989192295845092751461)
            ·
              refine ⟨10151060473555470954890899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54138989192295845092751461 10151060473555470954890899)
              ·
                refine ⟨15226590710333206432336349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10151060473555470954890899 15226590710333206432336349)
                ·
                  refine ⟨5709971516374952412126131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15226590710333206432336349 5709971516374952412126131)
                  ·
                    refine ⟨8564957274562428618189197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5709971516374952412126131 8564957274562428618189197)
                    ·
                      refine ⟨3211858977960910731820949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8564957274562428618189197 3211858977960910731820949)
                      ·
                        rfl

theorem cell23_6255073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_6255073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255073 prefixEnd_6255073 := by exact prefixLift 6255073
  have htrace : WordTrace (prefixWord ++ tailWord_6255073) baseStart_6255073 baseEnd_6255073 := by
    simpa [prefixWord, tailWord_6255073, baseEnd_6255073] using wordTrace_append hprefix tailTrace_6255073
  have hstable : (prefixWord ++ tailWord_6255073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255073).length < 2 ^ (prefixWord ++ tailWord_6255073).sum := by decide
  have hdescent : baseEnd_6255073 < baseStart_6255073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255096 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 2, 6, 2]
def baseStart_6255096 : Nat := 118140960795 + 6255096 * 2 ^ 59
def prefixEnd_6255096 : Nat := 4983230072969 + 3 ^ 40 * 6255096 * 2
def baseEnd_6255096 : Nat := 3211870788015964141833343

theorem tailTrace_6255096 : CollatzResearch.WordTrace tailWord_6255096 prefixEnd_6255096 3211870788015964141833343 := by
  unfold tailWord_6255096
  simp only [CollatzResearch.WordTrace]
  refine ⟨114071046873431476095684571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152094729164575301460912761 114071046873431476095684571)
  ·
    refine ⟨171106570310147214143526857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114071046873431476095684571 171106570310147214143526857)
    ·
      refine ⟨128329927732610410607645143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171106570310147214143526857 128329927732610410607645143)
      ·
        refine ⟨192494891598915615911467715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128329927732610410607645143 192494891598915615911467715)
        ·
          refine ⟨288742337398373423867201573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192494891598915615911467715 288742337398373423867201573)
          ·
            refine ⟨54139188262195016975100295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288742337398373423867201573 54139188262195016975100295)
            ·
              refine ⟨81208782393292525462650443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54139188262195016975100295 81208782393292525462650443)
              ·
                refine ⟨121813173589938788193975665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81208782393292525462650443 121813173589938788193975665)
                ·
                  refine ⟨91359880192454091145481749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121813173589938788193975665 91359880192454091145481749)
                  ·
                    refine ⟨4282494384021285522444457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91359880192454091145481749 4282494384021285522444457)
                    ·
                      refine ⟨3211870788015964141833343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282494384021285522444457 3211870788015964141833343)
                      ·
                        rfl

theorem cell23_6255096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 6, 2].length) (baseStart_6255096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255096 prefixEnd_6255096 := by exact prefixLift 6255096
  have htrace : WordTrace (prefixWord ++ tailWord_6255096) baseStart_6255096 baseEnd_6255096 := by
    simpa [prefixWord, tailWord_6255096, baseEnd_6255096] using wordTrace_append hprefix tailTrace_6255096
  have hstable : (prefixWord ++ tailWord_6255096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255096).length < 2 ^ (prefixWord ++ tailWord_6255096).sum := by decide
  have hdescent : baseEnd_6255096 < baseStart_6255096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255116 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 1, 1, 5]
def baseStart_6255116 : Nat := 118140960795 + 6255116 * 2 ^ 59
def prefixEnd_6255116 : Nat := 4983230072969 + 3 ^ 40 * 6255116 * 2
def baseEnd_6255116 : Nat := 3211881057629054063583251

theorem tailTrace_6255116 : CollatzResearch.WordTrace tailWord_6255116 prefixEnd_6255116 3211881057629054063583251 := by
  unfold tailWord_6255116
  simp only [CollatzResearch.WordTrace]
  refine ⟨114071411603395247803548601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152095215471193663738064801 114071411603395247803548601)
  ·
    refine ⟨85553558702546435852661451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114071411603395247803548601 85553558702546435852661451)
    ·
      refine ⟨128330338053819653778992177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85553558702546435852661451 128330338053819653778992177)
      ·
        refine ⟨96247753540364740334244133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128330338053819653778992177 96247753540364740334244133)
        ·
          refine ⟨18046453788818388812670775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96247753540364740334244133 18046453788818388812670775)
          ·
            refine ⟨27069680683227583219006163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18046453788818388812670775 27069680683227583219006163)
            ·
              refine ⟨40604521024841374828509245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27069680683227583219006163 40604521024841374828509245)
              ·
                refine ⟨15226695384315515560690967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40604521024841374828509245 15226695384315515560690967)
                ·
                  refine ⟨22840043076473273341036451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15226695384315515560690967 22840043076473273341036451)
                  ·
                    refine ⟨34260064614709910011554677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22840043076473273341036451 34260064614709910011554677)
                    ·
                      refine ⟨3211881057629054063583251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34260064614709910011554677 3211881057629054063583251)
                      ·
                        rfl

theorem cell23_6255116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_6255116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255116 prefixEnd_6255116 := by exact prefixLift 6255116
  have htrace : WordTrace (prefixWord ++ tailWord_6255116) baseStart_6255116 baseEnd_6255116 := by
    simpa [prefixWord, tailWord_6255116, baseEnd_6255116] using wordTrace_append hprefix tailTrace_6255116
  have hstable : (prefixWord ++ tailWord_6255116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255116).length < 2 ^ (prefixWord ++ tailWord_6255116).sum := by decide
  have hdescent : baseEnd_6255116 < baseStart_6255116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255117 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_6255117 : Nat := 118140960795 + 6255117 * 2 ^ 59
def prefixEnd_6255117 : Nat := 4983230072969 + 3 ^ 40 * 6255117 * 2
def baseEnd_6255117 : Nat := 3211881571109708559670747

theorem tailTrace_6255117 : CollatzResearch.WordTrace tailWord_6255117 prefixEnd_6255117 3211881571109708559670747 := by
  unfold tailWord_6255117
  simp only [CollatzResearch.WordTrace]
  refine ⟨228142859679786872777883605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152095239786524581851922403 228142859679786872777883605)
  ·
    refine ⟨5347098273745004830731647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 228142859679786872777883605 5347098273745004830731647)
    ·
      refine ⟨8020647410617507246097471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5347098273745004830731647 8020647410617507246097471)
      ·
        refine ⟨12030971115926260869146207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8020647410617507246097471 12030971115926260869146207)
        ·
          refine ⟨18046456673889391303719311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12030971115926260869146207 18046456673889391303719311)
          ·
            refine ⟨27069685010834086955578967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18046456673889391303719311 27069685010834086955578967)
            ·
              refine ⟨40604527516251130433368451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27069685010834086955578967 40604527516251130433368451)
              ·
                refine ⟨60906791274376695650052677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40604527516251130433368451 60906791274376695650052677)
                ·
                  refine ⟨11420023363945630434384877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60906791274376695650052677 11420023363945630434384877)
                  ·
                    refine ⟨4282508761479611412894329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11420023363945630434384877 4282508761479611412894329)
                    ·
                      refine ⟨3211881571109708559670747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282508761479611412894329 3211881571109708559670747)
                      ·
                        rfl

theorem cell23_6255117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_6255117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255117 prefixEnd_6255117 := by exact prefixLift 6255117
  have htrace : WordTrace (prefixWord ++ tailWord_6255117) baseStart_6255117 baseEnd_6255117 := by
    simpa [prefixWord, tailWord_6255117, baseEnd_6255117] using wordTrace_append hprefix tailTrace_6255117
  have hstable : (prefixWord ++ tailWord_6255117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255117).length < 2 ^ (prefixWord ++ tailWord_6255117).sum := by decide
  have hdescent : baseEnd_6255117 < baseStart_6255117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255130 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2]
def baseStart_6255130 : Nat := 118140960795 + 6255130 * 2 ^ 59
def prefixEnd_6255130 : Nat := 4983230072969 + 3 ^ 40 * 6255130 * 2
def baseEnd_6255130 : Nat := 3211888246358217008808187

theorem tailTrace_6255130 : CollatzResearch.WordTrace tailWord_6255130 prefixEnd_6255130 3211888246358217008808187 := by
  unfold tailWord_6255130
  simp only [CollatzResearch.WordTrace]
  refine ⟨57035833457184943999526711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152095555885826517332071229 57035833457184943999526711)
  ·
    refine ⟨85553750185777415999290067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57035833457184943999526711 85553750185777415999290067)
    ·
      refine ⟨128330625278666123998935101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85553750185777415999290067 128330625278666123998935101)
      ·
        refine ⟨48123984479499796499600663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128330625278666123998935101 48123984479499796499600663)
        ·
          refine ⟨72185976719249694749400995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48123984479499796499600663 72185976719249694749400995)
          ·
            refine ⟨108278965078874542124101493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72185976719249694749400995 108278965078874542124101493)
            ·
              refine ⟨10151152976144488324134515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108278965078874542124101493 10151152976144488324134515)
              ·
                refine ⟨15226729464216732486201773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10151152976144488324134515 15226729464216732486201773)
                ·
                  refine ⟨5710023549081274682325665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15226729464216732486201773 5710023549081274682325665)
                  ·
                    refine ⟨4282517661810956011744249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5710023549081274682325665 4282517661810956011744249)
                    ·
                      refine ⟨3211888246358217008808187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282517661810956011744249 3211888246358217008808187)
                      ·
                        rfl

theorem cell23_6255130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_6255130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255130 prefixEnd_6255130 := by exact prefixLift 6255130
  have htrace : WordTrace (prefixWord ++ tailWord_6255130) baseStart_6255130 baseEnd_6255130 := by
    simpa [prefixWord, tailWord_6255130, baseEnd_6255130] using wordTrace_append hprefix tailTrace_6255130
  have hstable : (prefixWord ++ tailWord_6255130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255130).length < 2 ^ (prefixWord ++ tailWord_6255130).sum := by decide
  have hdescent : baseEnd_6255130 < baseStart_6255130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255150 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_6255150 : Nat := 118140960795 + 6255150 * 2 ^ 59
def prefixEnd_6255150 : Nat := 4983230072969 + 3 ^ 40 * 6255150 * 2
def baseEnd_6255150 : Nat := 3211898515971306930558095

theorem tailTrace_6255150 : CollatzResearch.WordTrace tailWord_6255150 prefixEnd_6255150 3211898515971306930558095 := by
  unfold tailWord_6255150
  simp only [CollatzResearch.WordTrace]
  refine ⟨28518007911083414926729363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152096042192444879609223269 28518007911083414926729363)
  ·
    refine ⟨42777011866625122390094045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28518007911083414926729363 42777011866625122390094045)
    ·
      refine ⟨16041379449984420896285267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42777011866625122390094045 16041379449984420896285267)
      ·
        refine ⟨24062069174976631344427901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16041379449984420896285267 24062069174976631344427901)
        ·
          refine ⟨9023275940616236754160463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24062069174976631344427901 9023275940616236754160463)
          ·
            refine ⟨13534913910924355131240695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9023275940616236754160463 13534913910924355131240695)
            ·
              refine ⟨20302370866386532696861043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13534913910924355131240695 20302370866386532696861043)
              ·
                refine ⟨30453556299579799045291565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20302370866386532696861043 30453556299579799045291565)
                ·
                  refine ⟨11420083612342424641984337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30453556299579799045291565 11420083612342424641984337)
                  ·
                    refine ⟨8565062709256818481488253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11420083612342424641984337 8565062709256818481488253)
                    ·
                      refine ⟨3211898515971306930558095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8565062709256818481488253 3211898515971306930558095)
                      ·
                        rfl

theorem cell23_6255150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_6255150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255150 prefixEnd_6255150 := by exact prefixLift 6255150
  have htrace : WordTrace (prefixWord ++ tailWord_6255150) baseStart_6255150 baseEnd_6255150 := by
    simpa [prefixWord, tailWord_6255150, baseEnd_6255150] using wordTrace_append hprefix tailTrace_6255150
  have hstable : (prefixWord ++ tailWord_6255150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255150).length < 2 ^ (prefixWord ++ tailWord_6255150).sum := by decide
  have hdescent : baseEnd_6255150 < baseStart_6255150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255180 : List Nat := [2, 2, 1, 3, 1, 2, 4, 2, 2, 1, 3]
def baseStart_6255180 : Nat := 118140960795 + 6255180 * 2 ^ 59
def prefixEnd_6255180 : Nat := 4983230072969 + 3 ^ 40 * 6255180 * 2
def baseEnd_6255180 : Nat := 3211913920390941813182957

theorem tailTrace_6255180 : CollatzResearch.WordTrace tailWord_6255180 prefixEnd_6255180 3211913920390941813182957 := by
  unfold tailWord_6255180
  simp only [CollatzResearch.WordTrace]
  refine ⟨114072578739279317268713497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152096771652372423024951329 114072578739279317268713497)
  ·
    refine ⟨85554434054459487951535123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114072578739279317268713497 85554434054459487951535123)
    ·
      refine ⟨128331651081689231927302685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85554434054459487951535123 128331651081689231927302685)
      ·
        refine ⟨48124369155633461972738507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128331651081689231927302685 48124369155633461972738507)
        ·
          refine ⟨72186553733450192959107761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48124369155633461972738507 72186553733450192959107761)
          ·
            refine ⟨54139915300087644719330821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72186553733450192959107761 54139915300087644719330821)
            ·
              refine ⟨10151234118766433384874529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54139915300087644719330821 10151234118766433384874529)
              ·
                refine ⟨7613425589074825038655897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10151234118766433384874529 7613425589074825038655897)
                ·
                  refine ⟨5710069191806118778991923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7613425589074825038655897 5710069191806118778991923)
                  ·
                    refine ⟨8565103787709178168487885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5710069191806118778991923 8565103787709178168487885)
                    ·
                      refine ⟨3211913920390941813182957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8565103787709178168487885 3211913920390941813182957)
                      ·
                        rfl

theorem cell23_6255180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_6255180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255180 prefixEnd_6255180 := by exact prefixLift 6255180
  have htrace : WordTrace (prefixWord ++ tailWord_6255180) baseStart_6255180 baseEnd_6255180 := by
    simpa [prefixWord, tailWord_6255180, baseEnd_6255180] using wordTrace_append hprefix tailTrace_6255180
  have hstable : (prefixWord ++ tailWord_6255180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255180).length < 2 ^ (prefixWord ++ tailWord_6255180).sum := by decide
  have hdescent : baseEnd_6255180 < baseStart_6255180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255181 : List Nat := [1, 6, 1, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_6255181 : Nat := 118140960795 + 6255181 * 2 ^ 59
def prefixEnd_6255181 : Nat := 4983230072969 + 3 ^ 40 * 6255181 * 2
def baseEnd_6255181 : Nat := 3211914433871596309270453

theorem tailTrace_6255181 : CollatzResearch.WordTrace tailWord_6255181 prefixEnd_6255181 3211914433871596309270453 := by
  unfold tailWord_6255181
  simp only [CollatzResearch.WordTrace]
  refine ⟨228145193951555011708213397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152096795967703341138808931 228145193951555011708213397)
  ·
    refine ⟨10694305966479141173822503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 228145193951555011708213397 10694305966479141173822503)
    ·
      refine ⟨16041458949718711760733755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10694305966479141173822503 16041458949718711760733755)
      ·
        refine ⟨24062188424578067641100633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16041458949718711760733755 24062188424578067641100633)
        ·
          refine ⟨18046641318433550730825475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24062188424578067641100633 18046641318433550730825475)
          ·
            refine ⟨27069961977650326096238213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18046641318433550730825475 27069961977650326096238213)
            ·
              refine ⟨5075617870809436143044665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27069961977650326096238213 5075617870809436143044665)
              ·
                refine ⟨3806713403107077107283499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5075617870809436143044665 3806713403107077107283499)
                ·
                  refine ⟨5710070104660615660925249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3806713403107077107283499 5710070104660615660925249)
                  ·
                    refine ⟨4282552578495461745693937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5710070104660615660925249 4282552578495461745693937)
                    ·
                      refine ⟨3211914433871596309270453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282552578495461745693937 3211914433871596309270453)
                      ·
                        rfl

theorem cell23_6255181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_6255181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255181 prefixEnd_6255181 := by exact prefixLift 6255181
  have htrace : WordTrace (prefixWord ++ tailWord_6255181) baseStart_6255181 baseEnd_6255181 := by
    simpa [prefixWord, tailWord_6255181, baseEnd_6255181] using wordTrace_append hprefix tailTrace_6255181
  have hstable : (prefixWord ++ tailWord_6255181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255181).length < 2 ^ (prefixWord ++ tailWord_6255181).sum := by decide
  have hdescent : baseEnd_6255181 < baseStart_6255181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255186 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_6255186 : Nat := 118140960795 + 6255186 * 2 ^ 59
def prefixEnd_6255186 : Nat := 4983230072969 + 3 ^ 40 * 6255186 * 2
def baseEnd_6255186 : Nat := 3211917001274868789707929

theorem tailTrace_6255186 : CollatzResearch.WordTrace tailWord_6255186 prefixEnd_6255186 3211917001274868789707929 := by
  unfold tailWord_6255186
  simp only [CollatzResearch.WordTrace]
  refine ⟨57036344079134224390536353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152096917544357931708096941 57036344079134224390536353)
  ·
    refine ⟨42777258059350668292902265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57036344079134224390536353 42777258059350668292902265)
    ·
      refine ⟨32082943544513001219676699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42777258059350668292902265 32082943544513001219676699)
      ·
        refine ⟨48124415316769501829515049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32082943544513001219676699 48124415316769501829515049)
        ·
          refine ⟨36093311487577126372136287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48124415316769501829515049 36093311487577126372136287)
          ·
            refine ⟨54139967231365689558204431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36093311487577126372136287 54139967231365689558204431)
            ·
              refine ⟨81209950847048534337306647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54139967231365689558204431 81209950847048534337306647)
              ·
                refine ⟨121814926270572801505959971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81209950847048534337306647 121814926270572801505959971)
                ·
                  refine ⟨182722389405859202258939957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121814926270572801505959971 182722389405859202258939957)
                  ·
                    refine ⟨17130224006799300211775621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 182722389405859202258939957 17130224006799300211775621)
                    ·
                      refine ⟨3211917001274868789707929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17130224006799300211775621 3211917001274868789707929)
                      ·
                        rfl

theorem cell23_6255186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_6255186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255186 prefixEnd_6255186 := by exact prefixLift 6255186
  have htrace : WordTrace (prefixWord ++ tailWord_6255186) baseStart_6255186 baseEnd_6255186 := by
    simpa [prefixWord, tailWord_6255186, baseEnd_6255186] using wordTrace_append hprefix tailTrace_6255186
  have hstable : (prefixWord ++ tailWord_6255186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255186).length < 2 ^ (prefixWord ++ tailWord_6255186).sum := by decide
  have hdescent : baseEnd_6255186 < baseStart_6255186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255237 : List Nat := [1, 3, 1, 1, 4, 2, 3, 2, 2, 2, 2]
def baseStart_6255237 : Nat := 118140960795 + 6255237 * 2 ^ 59
def prefixEnd_6255237 : Nat := 4983230072969 + 3 ^ 40 * 6255237 * 2
def baseEnd_6255237 : Nat := 3211943188788248090170195

theorem tailTrace_6255237 : CollatzResearch.WordTrace tailWord_6255237 prefixEnd_6255237 3211943188788248090170195 := by
  unfold tailWord_6255237
  simp only [CollatzResearch.WordTrace]
  refine ⟨228147236439352133272251965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152098157626234755514834643 228147236439352133272251965)
  ·
    refine ⟨85555213664757049977094487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228147236439352133272251965 85555213664757049977094487)
    ·
      refine ⟨128332820497135574965641731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85555213664757049977094487 128332820497135574965641731)
      ·
        refine ⟨192499230745703362448462597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128332820497135574965641731 192499230745703362448462597)
        ·
          refine ⟨36093605764819380459086737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192499230745703362448462597 36093605764819380459086737)
          ·
            refine ⟨27070204323614535344315053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36093605764819380459086737 27070204323614535344315053)
            ·
              refine ⟨10151326621355450754118145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27070204323614535344315053 10151326621355450754118145)
              ·
                refine ⟨7613494966016588065588609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10151326621355450754118145 7613494966016588065588609)
                ·
                  refine ⟨5710121224512441049191457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7613494966016588065588609 5710121224512441049191457)
                  ·
                    refine ⟨4282590918384330786893593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5710121224512441049191457 4282590918384330786893593)
                    ·
                      refine ⟨3211943188788248090170195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282590918384330786893593 3211943188788248090170195)
                      ·
                        rfl

theorem cell23_6255237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 2, 2].length) (baseStart_6255237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255237 prefixEnd_6255237 := by exact prefixLift 6255237
  have htrace : WordTrace (prefixWord ++ tailWord_6255237) baseStart_6255237 baseEnd_6255237 := by
    simpa [prefixWord, tailWord_6255237, baseEnd_6255237] using wordTrace_append hprefix tailTrace_6255237
  have hstable : (prefixWord ++ tailWord_6255237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255237).length < 2 ^ (prefixWord ++ tailWord_6255237).sum := by decide
  have hdescent : baseEnd_6255237 < baseStart_6255237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255256 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 3, 7]
def baseStart_6255256 : Nat := 118140960795 + 6255256 * 2 ^ 59
def prefixEnd_6255256 : Nat := 4983230072969 + 3 ^ 40 * 6255256 * 2
def baseEnd_6255256 : Nat := 1070650981640227838610869

theorem tailTrace_6255256 : CollatzResearch.WordTrace tailWord_6255256 prefixEnd_6255256 1070650981640227838610869 := by
  unfold tailWord_6255256
  simp only [CollatzResearch.WordTrace]
  refine ⟨114073964713141649758596811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152098619617522199678129081 114073964713141649758596811)
  ·
    refine ⟨171110947069712474637895217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114073964713141649758596811 171110947069712474637895217)
    ·
      refine ⟨128333210302284355978421413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171110947069712474637895217 128333210302284355978421413)
      ·
        refine ⟨24062476931678316745954015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128333210302284355978421413 24062476931678316745954015)
        ·
          refine ⟨36093715397517475118931023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24062476931678316745954015 36093715397517475118931023)
          ·
            refine ⟨54140573096276212678396535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36093715397517475118931023 54140573096276212678396535)
            ·
              refine ⟨81210859644414319017594803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54140573096276212678396535 81210859644414319017594803)
              ·
                refine ⟨121816289466621478526392205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81210859644414319017594803 121816289466621478526392205)
                ·
                  refine ⟨45681108549983054447397077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121816289466621478526392205 45681108549983054447397077)
                  ·
                    refine ⟨1070650981640227838610869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45681108549983054447397077 1070650981640227838610869)
                    ·
                      rfl

theorem cell23_6255256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_6255256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255256 prefixEnd_6255256 := by exact prefixLift 6255256
  have htrace : WordTrace (prefixWord ++ tailWord_6255256) baseStart_6255256 baseEnd_6255256 := by
    simpa [prefixWord, tailWord_6255256, baseEnd_6255256] using wordTrace_append hprefix tailTrace_6255256
  have hstable : (prefixWord ++ tailWord_6255256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255256).length < 2 ^ (prefixWord ++ tailWord_6255256).sum := by decide
  have hdescent : baseEnd_6255256 < baseStart_6255256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255277 : List Nat := [1, 5, 2, 1, 1, 4, 1, 3, 5]
def baseStart_6255277 : Nat := 118140960795 + 6255277 * 2 ^ 59
def prefixEnd_6255277 : Nat := 4983230072969 + 3 ^ 40 * 6255277 * 2
def baseEnd_6255277 : Nat := 356884858668269770407779

theorem tailTrace_6255277 : CollatzResearch.WordTrace tailWord_6255277 prefixEnd_6255277 356884858668269770407779 := by
  unfold tailWord_6255277
  simp only [CollatzResearch.WordTrace]
  refine ⟨228148695359207220103708085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152099130239471480069138723 228148695359207220103708085)
  ·
    refine ⟨21388940189925676884722633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228148695359207220103708085 21388940189925676884722633)
    ·
      refine ⟨16041705142444257663541975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21388940189925676884722633 16041705142444257663541975)
      ·
        refine ⟨24062557713666386495312963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16041705142444257663541975 24062557713666386495312963)
        ·
          refine ⟨36093836570499579742969445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24062557713666386495312963 36093836570499579742969445)
          ·
            refine ⟨6767594356968671201806771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36093836570499579742969445 6767594356968671201806771)
            ·
              refine ⟨10151391535453006802710157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6767594356968671201806771 10151391535453006802710157)
              ·
                refine ⟨3806771825794877551016309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10151391535453006802710157 3806771825794877551016309)
                ·
                  refine ⟨356884858668269770407779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3806771825794877551016309 356884858668269770407779)
                  ·
                    rfl

theorem cell23_6255277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_6255277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255277 prefixEnd_6255277 := by exact prefixLift 6255277
  have htrace : WordTrace (prefixWord ++ tailWord_6255277) baseStart_6255277 baseEnd_6255277 := by
    simpa [prefixWord, tailWord_6255277, baseEnd_6255277] using wordTrace_append hprefix tailTrace_6255277
  have hstable : (prefixWord ++ tailWord_6255277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255277).length < 2 ^ (prefixWord ++ tailWord_6255277).sum := by decide
  have hdescent : baseEnd_6255277 < baseStart_6255277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255293 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_6255293 : Nat := 118140960795 + 6255293 * 2 ^ 59
def prefixEnd_6255293 : Nat := 4983230072969 + 3 ^ 40 * 6255293 * 2
def baseEnd_6255293 : Nat := 3211971943704899871069937

theorem tailTrace_6255293 : CollatzResearch.WordTrace tailWord_6255293 prefixEnd_6255293 3211971943704899871069937 := by
  unfold tailWord_6255293
  simp only [CollatzResearch.WordTrace]
  refine ⟨228149278927149254836290533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152099519284766169890860355 228149278927149254836290533)
  ·
    refine ⟨42777989798840485281804475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228149278927149254836290533 42777989798840485281804475)
    ·
      refine ⟨64166984698260727922706713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42777989798840485281804475 64166984698260727922706713)
      ·
        refine ⟨48125238523695545942030035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64166984698260727922706713 48125238523695545942030035)
        ·
          refine ⟨72187857785543318913045053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48125238523695545942030035 72187857785543318913045053)
          ·
            refine ⟨27070446669578744592391895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72187857785543318913045053 27070446669578744592391895)
            ·
              refine ⟨40605670004368116888587843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27070446669578744592391895 40605670004368116888587843)
              ·
                refine ⟨60908505006552175332881765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40605670004368116888587843 60908505006552175332881765)
                ·
                  refine ⟨11420344688728532874915331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60908505006552175332881765 11420344688728532874915331)
                  ·
                    refine ⟨17130517033092799312372997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11420344688728532874915331 17130517033092799312372997)
                    ·
                      refine ⟨3211971943704899871069937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17130517033092799312372997 3211971943704899871069937)
                      ·
                        rfl

theorem cell23_6255293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_6255293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255293 prefixEnd_6255293 := by exact prefixLift 6255293
  have htrace : WordTrace (prefixWord ++ tailWord_6255293) baseStart_6255293 baseEnd_6255293 := by
    simpa [prefixWord, tailWord_6255293, baseEnd_6255293] using wordTrace_append hprefix tailTrace_6255293
  have hstable : (prefixWord ++ tailWord_6255293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255293).length < 2 ^ (prefixWord ++ tailWord_6255293).sum := by decide
  have hdescent : baseEnd_6255293 < baseStart_6255293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255303 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 3, 4]
def baseStart_6255303 : Nat := 118140960795 + 6255303 * 2 ^ 59
def prefixEnd_6255303 : Nat := 4983230072969 + 3 ^ 40 * 6255303 * 2
def baseEnd_6255303 : Nat := 1070659026170481610648297

theorem tailTrace_6255303 : CollatzResearch.WordTrace tailWord_6255303 prefixEnd_6255303 1070659026170481610648297 := by
  unfold tailWord_6255303
  simp only [CollatzResearch.WordTrace]
  refine ⟨228149643657113026544154563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152099762438075351029436375 228149643657113026544154563)
  ·
    refine ⟨342224465485669539816231845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228149643657113026544154563 342224465485669539816231845)
    ·
      refine ⟨64167087278563038715543471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 342224465485669539816231845 64167087278563038715543471)
      ·
        refine ⟨96250630917844558073315207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64167087278563038715543471 96250630917844558073315207)
        ·
          refine ⟨144375946376766837109972811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96250630917844558073315207 144375946376766837109972811)
          ·
            refine ⟨216563919565150255664959217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144375946376766837109972811 216563919565150255664959217)
            ·
              refine ⟨162422939673862691748719413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216563919565150255664959217 162422939673862691748719413)
              ·
                refine ⟨15227150594424627351442445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162422939673862691748719413 15227150594424627351442445)
                ·
                  refine ⟨5710181472909235256790917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15227150594424627351442445 5710181472909235256790917)
                  ·
                    refine ⟨1070659026170481610648297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5710181472909235256790917 1070659026170481610648297)
                    ·
                      rfl

theorem cell23_6255303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_6255303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255303 prefixEnd_6255303 := by exact prefixLift 6255303
  have htrace : WordTrace (prefixWord ++ tailWord_6255303) baseStart_6255303 baseEnd_6255303 := by
    simpa [prefixWord, tailWord_6255303, baseEnd_6255303] using wordTrace_append hprefix tailTrace_6255303
  have hstable : (prefixWord ++ tailWord_6255303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255303).length < 2 ^ (prefixWord ++ tailWord_6255303).sum := by decide
  have hdescent : baseEnd_6255303 < baseStart_6255303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255313 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 4, 2, 3]
def baseStart_6255313 : Nat := 118140960795 + 6255313 * 2 ^ 59
def prefixEnd_6255313 : Nat := 4983230072969 + 3 ^ 40 * 6255313 * 2
def baseEnd_6255313 : Nat := 3211982213317989792819845

theorem tailTrace_6255313 : CollatzResearch.WordTrace tailWord_6255313 prefixEnd_6255313 3211982213317989792819845 := by
  unfold tailWord_6255313
  simp only [CollatzResearch.WordTrace]
  refine ⟨228150008387076798252018593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152100005591384532168012395 228150008387076798252018593)
  ·
    refine ⟨171112506290307598689013945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228150008387076798252018593 171112506290307598689013945)
    ·
      refine ⟨128334379717730699016760459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171112506290307598689013945 128334379717730699016760459)
      ·
        refine ⟨192501569576596048525140689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128334379717730699016760459 192501569576596048525140689)
        ·
          refine ⟨144376177182447036393855517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192501569576596048525140689 144376177182447036393855517)
          ·
            refine ⟨54141066443417638647695819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144376177182447036393855517 54141066443417638647695819)
            ·
              refine ⟨81211599665126457971543729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54141066443417638647695819 81211599665126457971543729)
              ·
                refine ⟨60908699748844843478657797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81211599665126457971543729 60908699748844843478657797)
                ·
                  refine ⟨11420381202908408152248337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60908699748844843478657797 11420381202908408152248337)
                  ·
                    refine ⟨8565285902181306114186253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11420381202908408152248337 8565285902181306114186253)
                    ·
                      refine ⟨3211982213317989792819845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8565285902181306114186253 3211982213317989792819845)
                      ·
                        rfl

theorem cell23_6255313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_6255313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255313 prefixEnd_6255313 := by exact prefixLift 6255313
  have htrace : WordTrace (prefixWord ++ tailWord_6255313) baseStart_6255313 baseEnd_6255313 := by
    simpa [prefixWord, tailWord_6255313, baseEnd_6255313] using wordTrace_append hprefix tailTrace_6255313
  have hstable : (prefixWord ++ tailWord_6255313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255313).length < 2 ^ (prefixWord ++ tailWord_6255313).sum := by decide
  have hdescent : baseEnd_6255313 < baseStart_6255313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255350 : List Nat := [5, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_6255350 : Nat := 118140960795 + 6255350 * 2 ^ 59
def prefixEnd_6255350 : Nat := 4983230072969 + 3 ^ 40 * 6255350 * 2
def baseEnd_6255350 : Nat := 356889023566911794228575

theorem tailTrace_6255350 : CollatzResearch.WordTrace tailWord_6255350 prefixEnd_6255350 356889023566911794228575 := by
  unfold tailWord_6255350
  simp only [CollatzResearch.WordTrace]
  refine ⟨14259459867996422098194719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152100905258628502380743669 14259459867996422098194719)
  ·
    refine ⟨21389189801994633147292079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14259459867996422098194719 21389189801994633147292079)
    ·
      refine ⟨32083784702991949720938119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21389189801994633147292079 32083784702991949720938119)
      ·
        refine ⟨48125677054487924581407179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32083784702991949720938119 48125677054487924581407179)
        ·
          refine ⟨72188515581731886872110769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48125677054487924581407179 72188515581731886872110769)
          ·
            refine ⟨54141386686298915154083077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72188515581731886872110769 54141386686298915154083077)
            ·
              refine ⟨10151510003681046591390577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54141386686298915154083077 10151510003681046591390577)
              ·
                refine ⟨7613632502760784943542933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10151510003681046591390577 7613632502760784943542933)
                ·
                  refine ⟨356889023566911794228575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7613632502760784943542933 356889023566911794228575)
                  ·
                    rfl

theorem cell23_6255350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_6255350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255350 prefixEnd_6255350 := by exact prefixLift 6255350
  have htrace : WordTrace (prefixWord ++ tailWord_6255350) baseStart_6255350 baseEnd_6255350 := by
    simpa [prefixWord, tailWord_6255350, baseEnd_6255350] using wordTrace_append hprefix tailTrace_6255350
  have hstable : (prefixWord ++ tailWord_6255350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255350).length < 2 ^ (prefixWord ++ tailWord_6255350).sum := by decide
  have hdescent : baseEnd_6255350 < baseStart_6255350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255370 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 1, 5, 2]
def baseStart_6255370 : Nat := 118140960795 + 6255370 * 2 ^ 59
def prefixEnd_6255370 : Nat := 4983230072969 + 3 ^ 40 * 6255370 * 2
def baseEnd_6255370 : Nat := 3212011481715296069807083

theorem tailTrace_6255370 : CollatzResearch.WordTrace tailWord_6255370 prefixEnd_6255370 3212011481715296069807083 := by
  unfold tailWord_6255370
  simp only [CollatzResearch.WordTrace]
  refine ⟨57038021836967574246710891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152101391565246864657895709 57038021836967574246710891)
  ·
    refine ⟨85557032755451361370066337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57038021836967574246710891 85557032755451361370066337)
    ·
      refine ⟨64167774566588521027549753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85557032755451361370066337 64167774566588521027549753)
      ·
        refine ⟨48125830924941390770662315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64167774566588521027549753 48125830924941390770662315)
        ·
          refine ⟨72188746387412086155993473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48125830924941390770662315 72188746387412086155993473)
          ·
            refine ⟨54141559790559064616995105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72188746387412086155993473 54141559790559064616995105)
            ·
              refine ⟨40606169842919298462746329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54141559790559064616995105 40606169842919298462746329)
              ·
                refine ⟨30454627382189473847059747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40606169842919298462746329 30454627382189473847059747)
                ·
                  refine ⟨45681941073284210770589621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30454627382189473847059747 45681941073284210770589621)
                  ·
                    refine ⟨4282681975620394759742777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45681941073284210770589621 4282681975620394759742777)
                    ·
                      refine ⟨3212011481715296069807083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282681975620394759742777 3212011481715296069807083)
                      ·
                        rfl

theorem cell23_6255370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_6255370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255370 prefixEnd_6255370 := by exact prefixLift 6255370
  have htrace : WordTrace (prefixWord ++ tailWord_6255370) baseStart_6255370 baseEnd_6255370 := by
    simpa [prefixWord, tailWord_6255370, baseEnd_6255370] using wordTrace_append hprefix tailTrace_6255370
  have hstable : (prefixWord ++ tailWord_6255370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255370).length < 2 ^ (prefixWord ++ tailWord_6255370).sum := by decide
  have hdescent : baseEnd_6255370 < baseStart_6255370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255393 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 1, 6]
def baseStart_6255393 : Nat := 118140960795 + 6255393 * 2 ^ 59
def prefixEnd_6255393 : Nat := 4983230072969 + 3 ^ 40 * 6255393 * 2
def baseEnd_6255393 : Nat := 1070674430590116493273159

theorem tailTrace_6255393 : CollatzResearch.WordTrace tailWord_6255393 prefixEnd_6255393 1070674430590116493273159 := by
  unfold tailWord_6255393
  simp only [CollatzResearch.WordTrace]
  refine ⟨228152926226786971914930833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152101950817857981276620555 228152926226786971914930833)
  ·
    refine ⟨171114694670090228936198125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228152926226786971914930833 171114694670090228936198125)
    ·
      refine ⟨64168010501283835851074297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171114694670090228936198125 64168010501283835851074297)
      ·
        refine ⟨48126007875962876888305723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64168010501283835851074297 48126007875962876888305723)
        ·
          refine ⟨72189011813944315332458585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48126007875962876888305723 72189011813944315332458585)
          ·
            refine ⟨54141758860458236499343939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72189011813944315332458585 54141758860458236499343939)
            ·
              refine ⟨81212638290687354749015909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54141758860458236499343939 81212638290687354749015909)
              ·
                refine ⟨15227369679503879015440483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81212638290687354749015909 15227369679503879015440483)
                ·
                  refine ⟨22841054519255818523160725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15227369679503879015440483 22841054519255818523160725)
                  ·
                    refine ⟨1070674430590116493273159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22841054519255818523160725 1070674430590116493273159)
                    ·
                      rfl

theorem cell23_6255393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_6255393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255393 prefixEnd_6255393 := by exact prefixLift 6255393
  have htrace : WordTrace (prefixWord ++ tailWord_6255393) baseStart_6255393 baseEnd_6255393 := by
    simpa [prefixWord, tailWord_6255393, baseEnd_6255393] using wordTrace_append hprefix tailTrace_6255393
  have hstable : (prefixWord ++ tailWord_6255393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255393).length < 2 ^ (prefixWord ++ tailWord_6255393).sum := by decide
  have hdescent : baseEnd_6255393 < baseStart_6255393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255394 : List Nat := [3, 3, 1, 1, 2, 2, 1, 5, 1, 1, 3]
def baseStart_6255394 : Nat := 118140960795 + 6255394 * 2 ^ 59
def prefixEnd_6255394 : Nat := 4983230072969 + 3 ^ 40 * 6255394 * 2
def baseEnd_6255394 : Nat := 3212023805251003975906973

theorem tailTrace_6255394 : CollatzResearch.WordTrace tailWord_6255394 prefixEnd_6255394 3212023805251003975906973 := by
  unfold tailWord_6255394
  simp only [CollatzResearch.WordTrace]
  refine ⟨57038240674945837271429309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152101975133188899390478157 57038240674945837271429309)
  ·
    refine ⟨21389340253104688976785991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57038240674945837271429309 21389340253104688976785991)
    ·
      refine ⟨32084010379657033465178987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21389340253104688976785991 32084010379657033465178987)
      ·
        refine ⟨48126015569485550197768481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32084010379657033465178987 48126015569485550197768481)
        ·
          refine ⟨36094511677114162648326361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48126015569485550197768481 36094511677114162648326361)
          ·
            refine ⟨27070883757835621986244771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36094511677114162648326361 27070883757835621986244771)
            ·
              refine ⟨40606325636753432979367157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27070883757835621986244771 40606325636753432979367157)
              ·
                refine ⟨3806843028445634341815671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40606325636753432979367157 3806843028445634341815671)
                ·
                  refine ⟨5710264542668451512723507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3806843028445634341815671 5710264542668451512723507)
                  ·
                    refine ⟨8565396814002677269085261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5710264542668451512723507 8565396814002677269085261)
                    ·
                      refine ⟨3212023805251003975906973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8565396814002677269085261 3212023805251003975906973)
                      ·
                        rfl

theorem cell23_6255394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_6255394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255394 prefixEnd_6255394 := by exact prefixLift 6255394
  have htrace : WordTrace (prefixWord ++ tailWord_6255394) baseStart_6255394 baseEnd_6255394 := by
    simpa [prefixWord, tailWord_6255394, baseEnd_6255394] using wordTrace_append hprefix tailTrace_6255394
  have hstable : (prefixWord ++ tailWord_6255394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255394).length < 2 ^ (prefixWord ++ tailWord_6255394).sum := by decide
  have hdescent : baseEnd_6255394 < baseStart_6255394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255410 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_6255410 : Nat := 118140960795 + 6255410 * 2 ^ 59
def prefixEnd_6255410 : Nat := 4983230072969 + 3 ^ 40 * 6255410 * 2
def baseEnd_6255410 : Nat := 1070677340313825304435633

theorem tailTrace_6255410 : CollatzResearch.WordTrace tailWord_6255410 prefixEnd_6255410 1070677340313825304435633 := by
  unfold tailWord_6255410
  simp only [CollatzResearch.WordTrace]
  refine ⟨57038386566931345954574921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152102364178483589212199789 57038386566931345954574921)
  ·
    refine ⟨42778789925198509465931191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57038386566931345954574921 42778789925198509465931191)
    ·
      refine ⟨64168184887797764198896787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42778789925198509465931191 64168184887797764198896787)
      ·
        refine ⟨96252277331696646298345181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64168184887797764198896787 96252277331696646298345181)
        ·
          refine ⟨36094603999386242361879443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96252277331696646298345181 36094603999386242361879443)
          ·
            refine ⟨54141905999079363542819165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36094603999386242361879443 54141905999079363542819165)
            ·
              refine ⟨20303214749654761328557187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54141905999079363542819165 20303214749654761328557187)
              ·
                refine ⟨30454822124482141992835781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20303214749654761328557187 30454822124482141992835781)
                ·
                  refine ⟨5710279148340401623656709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30454822124482141992835781 5710279148340401623656709)
                  ·
                    refine ⟨1070677340313825304435633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5710279148340401623656709 1070677340313825304435633)
                    ·
                      rfl

theorem cell23_6255410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_6255410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255410 prefixEnd_6255410 := by exact prefixLift 6255410
  have htrace : WordTrace (prefixWord ++ tailWord_6255410) baseStart_6255410 baseEnd_6255410 := by
    simpa [prefixWord, tailWord_6255410, baseEnd_6255410] using wordTrace_append hprefix tailTrace_6255410
  have hstable : (prefixWord ++ tailWord_6255410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255410).length < 2 ^ (prefixWord ++ tailWord_6255410).sum := by decide
  have hdescent : baseEnd_6255410 < baseStart_6255410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255427 : List Nat := [1, 1, 1, 3, 1, 4, 5, 1, 2, 4]
def baseStart_6255427 : Nat := 118140960795 + 6255427 * 2 ^ 59
def prefixEnd_6255427 : Nat := 4983230072969 + 3 ^ 40 * 6255427 * 2
def baseEnd_6255427 : Nat := 1070680250037534115598107

theorem tailTrace_6255427 : CollatzResearch.WordTrace tailWord_6255427 prefixEnd_6255427 1070680250037534115598107 := by
  unfold tailWord_6255427
  simp only [CollatzResearch.WordTrace]
  refine ⟨228154166308663795721668535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152102777539109197147779023 228154166308663795721668535)
  ·
    refine ⟨342231249462995693582502803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228154166308663795721668535 342231249462995693582502803)
    ·
      refine ⟨513346874194493540373754205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342231249462995693582502803 513346874194493540373754205)
      ·
        refine ⟨192505077822935077640157827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 513346874194493540373754205 192505077822935077640157827)
        ·
          refine ⟨288757616734402616460236741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192505077822935077640157827 288757616734402616460236741)
          ·
            refine ⟨54142053137700490586294389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288757616734402616460236741 54142053137700490586294389)
            ·
              refine ⟨5075817481659420992465099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54142053137700490586294389 5075817481659420992465099)
              ·
                refine ⟨7613726222489131488697649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5075817481659420992465099 7613726222489131488697649)
                ·
                  refine ⟨5710294666866848616523237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7613726222489131488697649 5710294666866848616523237)
                  ·
                    refine ⟨1070680250037534115598107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5710294666866848616523237 1070680250037534115598107)
                    ·
                      rfl

theorem cell23_6255427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 2, 4].length) (baseStart_6255427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255427 prefixEnd_6255427 := by exact prefixLift 6255427
  have htrace : WordTrace (prefixWord ++ tailWord_6255427) baseStart_6255427 baseEnd_6255427 := by
    simpa [prefixWord, tailWord_6255427, baseEnd_6255427] using wordTrace_append hprefix tailTrace_6255427
  have hstable : (prefixWord ++ tailWord_6255427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255427).length < 2 ^ (prefixWord ++ tailWord_6255427).sum := by decide
  have hdescent : baseEnd_6255427 < baseStart_6255427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255483 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 2, 6]
def baseStart_6255483 : Nat := 118140960795 + 6255483 * 2 ^ 59
def prefixEnd_6255483 : Nat := 4983230072969 + 3 ^ 40 * 6255483 * 2
def baseEnd_6255483 : Nat := 1070689835009751375898021

theorem tailTrace_6255483 : CollatzResearch.WordTrace tailWord_6255483 prefixEnd_6255483 1070689835009751375898021 := by
  unfold tailWord_6255483
  simp only [CollatzResearch.WordTrace]
  refine ⟨228156208796460917285707103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152104139197640611523804735 228156208796460917285707103)
  ·
    refine ⟨342234313194691375928560655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228156208796460917285707103 342234313194691375928560655)
    ·
      refine ⟨513351469792037063892840983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342234313194691375928560655 513351469792037063892840983)
      ·
        refine ⟨770027204688055595839261475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513351469792037063892840983 770027204688055595839261475)
        ·
          refine ⟨1155040807032083393758892213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770027204688055595839261475 1155040807032083393758892213)
          ·
            refine ⟨108285075659257818164896145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1155040807032083393758892213 108285075659257818164896145)
            ·
              refine ⟨81213806744443363623672109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108285075659257818164896145 81213806744443363623672109)
              ·
                refine ⟨30455177529166261358877041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81213806744443363623672109 30455177529166261358877041)
                ·
                  refine ⟨22841383146874696019157781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30455177529166261358877041 22841383146874696019157781)
                  ·
                    refine ⟨1070689835009751375898021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22841383146874696019157781 1070689835009751375898021)
                    ·
                      rfl

theorem cell23_6255483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 6].length) (baseStart_6255483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255483 prefixEnd_6255483 := by exact prefixLift 6255483
  have htrace : WordTrace (prefixWord ++ tailWord_6255483) baseStart_6255483 baseEnd_6255483 := by
    simpa [prefixWord, tailWord_6255483, baseEnd_6255483] using wordTrace_append hprefix tailTrace_6255483
  have hstable : (prefixWord ++ tailWord_6255483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255483).length < 2 ^ (prefixWord ++ tailWord_6255483).sum := by decide
  have hdescent : baseEnd_6255483 < baseStart_6255483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255507 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 4, 2, 2]
def baseStart_6255507 : Nat := 118140960795 + 6255507 * 2 ^ 59
def prefixEnd_6255507 : Nat := 4983230072969 + 3 ^ 40 * 6255507 * 2
def baseEnd_6255507 : Nat := 3212081828564962033793953

theorem tailTrace_6255507 : CollatzResearch.WordTrace tailWord_6255507 prefixEnd_6255507 3212081828564962033793953 := by
  unfold tailWord_6255507
  simp only [CollatzResearch.WordTrace]
  refine ⟨228157084148373969384580775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152104722765582646256387183 228157084148373969384580775)
  ·
    refine ⟨342235626222560954076871163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228157084148373969384580775 342235626222560954076871163)
    ·
      refine ⟨513353439333841431115306745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342235626222560954076871163 513353439333841431115306745)
      ·
        refine ⟨385015079500381073336480059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513353439333841431115306745 385015079500381073336480059)
        ·
          refine ⟨577522619250571610004720089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385015079500381073336480059 577522619250571610004720089)
          ·
            refine ⟨433141964437928707503540067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577522619250571610004720089 433141964437928707503540067)
            ·
              refine ⟨649712946656893061255310101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433141964437928707503540067 649712946656893061255310101)
              ·
                refine ⟨30455294374541862246342661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 649712946656893061255310101 30455294374541862246342661)
                ·
                  refine ⟨5710367695226599171189249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30455294374541862246342661 5710367695226599171189249)
                  ·
                    refine ⟨4282775771419949378391937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5710367695226599171189249 4282775771419949378391937)
                    ·
                      refine ⟨3212081828564962033793953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282775771419949378391937 3212081828564962033793953)
                      ·
                        rfl

theorem cell23_6255507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 2, 2].length) (baseStart_6255507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255507 prefixEnd_6255507 := by exact prefixLift 6255507
  have htrace : WordTrace (prefixWord ++ tailWord_6255507) baseStart_6255507 baseEnd_6255507 := by
    simpa [prefixWord, tailWord_6255507, baseEnd_6255507] using wordTrace_append hprefix tailTrace_6255507
  have hstable : (prefixWord ++ tailWord_6255507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255507).length < 2 ^ (prefixWord ++ tailWord_6255507).sum := by decide
  have hdescent : baseEnd_6255507 < baseStart_6255507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255523 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 7]
def baseStart_6255523 : Nat := 118140960795 + 6255523 * 2 ^ 59
def prefixEnd_6255523 : Nat := 4983230072969 + 3 ^ 40 * 6255523 * 2
def baseEnd_6255523 : Nat := 3212090044255433971193879

theorem tailTrace_6255523 : CollatzResearch.WordTrace tailWord_6255523 prefixEnd_6255523 3212090044255433971193879 := by
  unfold tailWord_6255523
  simp only [CollatzResearch.WordTrace]
  refine ⟨228157667716316004117163223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152105111810877336078108815 228157667716316004117163223)
  ·
    refine ⟨342236501574474006175744835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228157667716316004117163223 342236501574474006175744835)
    ·
      refine ⟨513354752361711009263617253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342236501574474006175744835 513354752361711009263617253)
      ·
        refine ⟨96254016067820814236928235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 513354752361711009263617253 96254016067820814236928235)
        ·
          refine ⟨144381024101731221355392353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96254016067820814236928235 144381024101731221355392353)
          ·
            refine ⟨108285768076298416016544265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144381024101731221355392353 108285768076298416016544265)
            ·
              refine ⟨81214326057223812012408199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108285768076298416016544265 81214326057223812012408199)
              ·
                refine ⟨121821489085835718018612299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81214326057223812012408199 121821489085835718018612299)
                ·
                  refine ⟨182732233628753577027918449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121821489085835718018612299 182732233628753577027918449)
                  ·
                    refine ⟨137049175221565182770938837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 182732233628753577027918449 137049175221565182770938837)
                    ·
                      refine ⟨3212090044255433971193879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137049175221565182770938837 3212090044255433971193879)
                      ·
                        rfl

theorem cell23_6255523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_6255523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255523 prefixEnd_6255523 := by exact prefixLift 6255523
  have htrace : WordTrace (prefixWord ++ tailWord_6255523) baseStart_6255523 baseEnd_6255523 := by
    simpa [prefixWord, tailWord_6255523, baseEnd_6255523] using wordTrace_append hprefix tailTrace_6255523
  have hstable : (prefixWord ++ tailWord_6255523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255523).length < 2 ^ (prefixWord ++ tailWord_6255523).sum := by decide
  have hdescent : baseEnd_6255523 < baseStart_6255523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255537 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 2, 2, 4]
def baseStart_6255537 : Nat := 118140960795 + 6255537 * 2 ^ 59
def prefixEnd_6255537 : Nat := 4983230072969 + 3 ^ 40 * 6255537 * 2
def baseEnd_6255537 : Nat := 3212097232984596916418815

theorem tailTrace_6255537 : CollatzResearch.WordTrace tailWord_6255537 prefixEnd_6255537 3212097232984596916418815 := by
  unfold tailWord_6255537
  simp only [CollatzResearch.WordTrace]
  refine ⟨228158178338265284508172865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152105452225510189672115243 228158178338265284508172865)
  ·
    refine ⟨171118633753698963381129649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228158178338265284508172865 171118633753698963381129649)
    ·
      refine ⟨128338975315274222535847237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171118633753698963381129649 128338975315274222535847237)
      ·
        refine ⟨24063557871613916725471357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128338975315274222535847237 24063557871613916725471357)
        ·
          refine ⟨9023834201855218772051759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24063557871613916725471357 9023834201855218772051759)
          ·
            refine ⟨13535751302782828158077639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9023834201855218772051759 13535751302782828158077639)
            ·
              refine ⟨20303626954174242237116459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13535751302782828158077639 20303626954174242237116459)
              ·
                refine ⟨30455440431261363355674689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20303626954174242237116459 30455440431261363355674689)
                ·
                  refine ⟨22841580323446022516756017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30455440431261363355674689 22841580323446022516756017)
                  ·
                    refine ⟨17131185242584516887567013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22841580323446022516756017 17131185242584516887567013)
                    ·
                      refine ⟨3212097232984596916418815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17131185242584516887567013 3212097232984596916418815)
                      ·
                        rfl

theorem cell23_6255537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_6255537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255537 prefixEnd_6255537 := by exact prefixLift 6255537
  have htrace : WordTrace (prefixWord ++ tailWord_6255537) baseStart_6255537 baseEnd_6255537 := by
    simpa [prefixWord, tailWord_6255537, baseEnd_6255537] using wordTrace_append hprefix tailTrace_6255537
  have hstable : (prefixWord ++ tailWord_6255537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255537).length < 2 ^ (prefixWord ++ tailWord_6255537).sum := by decide
  have hdescent : baseEnd_6255537 < baseStart_6255537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255574 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_6255574 : Nat := 118140960795 + 6255574 * 2 ^ 59
def prefixEnd_6255574 : Nat := 4983230072969 + 3 ^ 40 * 6255574 * 2
def baseEnd_6255574 : Nat := 3212116231768813271656145

theorem tailTrace_6255574 : CollatzResearch.WordTrace tailWord_6255574 prefixEnd_6255574 3212116231768813271656145 := by
  unfold tailWord_6255574
  simp only [CollatzResearch.WordTrace]
  refine ⟨14259970489945702489204361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152106351892754159884846517 14259970489945702489204361)
  ·
    refine ⟨10694977867459276866903271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14259970489945702489204361 10694977867459276866903271)
    ·
      refine ⟨16042466801188915300354907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10694977867459276866903271 16042466801188915300354907)
      ·
        refine ⟨24063700201783372950532361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16042466801188915300354907 24063700201783372950532361)
        ·
          refine ⟨18047775151337529712899271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24063700201783372950532361 18047775151337529712899271)
          ·
            refine ⟨27071662727006294569348907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18047775151337529712899271 27071662727006294569348907)
            ·
              refine ⟨40607494090509441854023361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27071662727006294569348907 40607494090509441854023361)
              ·
                refine ⟨30455620567882081390517521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40607494090509441854023361 30455620567882081390517521)
                ·
                  refine ⟨22841715425911561042888141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30455620567882081390517521 22841715425911561042888141)
                  ·
                    refine ⟨8565643284716835391083053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22841715425911561042888141 8565643284716835391083053)
                    ·
                      refine ⟨3212116231768813271656145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8565643284716835391083053 3212116231768813271656145)
                      ·
                        rfl

theorem cell23_6255574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_6255574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255574 prefixEnd_6255574 := by exact prefixLift 6255574
  have htrace : WordTrace (prefixWord ++ tailWord_6255574) baseStart_6255574 baseEnd_6255574 := by
    simpa [prefixWord, tailWord_6255574, baseEnd_6255574] using wordTrace_append hprefix tailTrace_6255574
  have hstable : (prefixWord ++ tailWord_6255574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255574).length < 2 ^ (prefixWord ++ tailWord_6255574).sum := by decide
  have hdescent : baseEnd_6255574 < baseStart_6255574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255617 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_6255617 : Nat := 118140960795 + 6255617 * 2 ^ 59
def prefixEnd_6255617 : Nat := 4983230072969 + 3 ^ 40 * 6255617 * 2
def baseEnd_6255617 : Nat := 3212138311436956603418447

theorem tailTrace_6255617 : CollatzResearch.WordTrace tailWord_6255617 prefixEnd_6255617 3212138311436956603418447 := by
  unfold tailWord_6255617
  simp only [CollatzResearch.WordTrace]
  refine ⟨228161096177975458171085105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152107397451983638780723403 228161096177975458171085105)
  ·
    refine ⟨171120822133481593628313829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228161096177975458171085105 171120822133481593628313829)
    ·
      refine ⟨32085154150027798805308843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171120822133481593628313829 32085154150027798805308843)
      ·
        refine ⟨48127731225041698207963265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32085154150027798805308843 48127731225041698207963265)
        ·
          refine ⟨36095798418781273655972449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48127731225041698207963265 36095798418781273655972449)
          ·
            refine ⟨27071848814085955241979337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36095798418781273655972449 27071848814085955241979337)
            ·
              refine ⟨20303886610564466431484503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27071848814085955241979337 20303886610564466431484503)
              ·
                refine ⟨30455829915846699647226755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20303886610564466431484503 30455829915846699647226755)
                ·
                  refine ⟨45683744873770049470840133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30455829915846699647226755 45683744873770049470840133)
                  ·
                    refine ⟨8565702163831884275782525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45683744873770049470840133 8565702163831884275782525)
                    ·
                      refine ⟨3212138311436956603418447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8565702163831884275782525 3212138311436956603418447)
                      ·
                        rfl

theorem cell23_6255617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_6255617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255617 prefixEnd_6255617 := by exact prefixLift 6255617
  have htrace : WordTrace (prefixWord ++ tailWord_6255617) baseStart_6255617 baseEnd_6255617 := by
    simpa [prefixWord, tailWord_6255617, baseEnd_6255617] using wordTrace_append hprefix tailTrace_6255617
  have hstable : (prefixWord ++ tailWord_6255617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255617).length < 2 ^ (prefixWord ++ tailWord_6255617).sum := by decide
  have hdescent : baseEnd_6255617 < baseStart_6255617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255674 : List Nat := [3, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2]
def baseStart_6255674 : Nat := 118140960795 + 6255674 * 2 ^ 59
def prefixEnd_6255674 : Nat := 4983230072969 + 3 ^ 40 * 6255674 * 2
def baseEnd_6255674 : Nat := 3212167579834262880405685

theorem tailTrace_6255674 : CollatzResearch.WordTrace tailWord_6255674 prefixEnd_6255674 3212167579834262880405685 := by
  unfold tailWord_6255674
  simp only [CollatzResearch.WordTrace]
  refine ⟨57040793784692239226477519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152108783425845971270606717 57040793784692239226477519)
  ·
    refine ⟨85561190677038358839716279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57040793784692239226477519 85561190677038358839716279)
    ·
      refine ⟨128341786015557538259574419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85561190677038358839716279 128341786015557538259574419)
      ·
        refine ⟨192512679023336307389361629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128341786015557538259574419 192512679023336307389361629)
        ·
          refine ⟨72192254633751115271010611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192512679023336307389361629 72192254633751115271010611)
          ·
            refine ⟨108288381950626672906515917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72192254633751115271010611 108288381950626672906515917)
            ·
              refine ⟨40608143231485002339943469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108288381950626672906515917 40608143231485002339943469)
              ·
                refine ⟨15228053711806875877478801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40608143231485002339943469 15228053711806875877478801)
                ·
                  refine ⟨11421040283855156908109101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15228053711806875877478801 11421040283855156908109101)
                  ·
                    refine ⟨4282890106445683840540913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11421040283855156908109101 4282890106445683840540913)
                    ·
                      refine ⟨3212167579834262880405685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282890106445683840540913 3212167579834262880405685)
                      ·
                        rfl

theorem cell23_6255674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2].length) (baseStart_6255674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255674 prefixEnd_6255674 := by exact prefixLift 6255674
  have htrace : WordTrace (prefixWord ++ tailWord_6255674) baseStart_6255674 baseEnd_6255674 := by
    simpa [prefixWord, tailWord_6255674, baseEnd_6255674] using wordTrace_append hprefix tailTrace_6255674
  have hstable : (prefixWord ++ tailWord_6255674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255674).length < 2 ^ (prefixWord ++ tailWord_6255674).sum := by decide
  have hdescent : baseEnd_6255674 < baseStart_6255674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255697 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 4, 4]
def baseStart_6255697 : Nat := 118140960795 + 6255697 * 2 ^ 59
def prefixEnd_6255697 : Nat := 4983230072969 + 3 ^ 40 * 6255697 * 2
def baseEnd_6255697 : Nat := 1070726463296438763472693

theorem tailTrace_6255697 : CollatzResearch.WordTrace tailWord_6255697 prefixEnd_6255697 1070726463296438763472693 := by
  unfold tailWord_6255697
  simp only [CollatzResearch.WordTrace]
  refine ⟨228164014017685631833997345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152109342678457087889331563 228164014017685631833997345)
  ·
    refine ⟨171123010513264223875498009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228164014017685631833997345 171123010513264223875498009)
    ·
      refine ⟨128342257884948167906623507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171123010513264223875498009 128342257884948167906623507)
      ·
        refine ⟨192513386827422251859935261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128342257884948167906623507 192513386827422251859935261)
        ·
          refine ⟨72192520060283344447475723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192513386827422251859935261 72192520060283344447475723)
          ·
            refine ⟨108288780090425016671213585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72192520060283344447475723 108288780090425016671213585)
            ·
              refine ⟨81216585067818762503410189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108288780090425016671213585 81216585067818762503410189)
              ·
                refine ⟨30456219400432035938778821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81216585067818762503410189 30456219400432035938778821)
                ·
                  refine ⟨5710541137581006738521029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30456219400432035938778821 5710541137581006738521029)
                  ·
                    refine ⟨1070726463296438763472693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5710541137581006738521029 1070726463296438763472693)
                    ·
                      rfl

theorem cell23_6255697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_6255697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255697 prefixEnd_6255697 := by exact prefixLift 6255697
  have htrace : WordTrace (prefixWord ++ tailWord_6255697) baseStart_6255697 baseEnd_6255697 := by
    simpa [prefixWord, tailWord_6255697, baseEnd_6255697] using wordTrace_append hprefix tailTrace_6255697
  have hstable : (prefixWord ++ tailWord_6255697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255697).length < 2 ^ (prefixWord ++ tailWord_6255697).sum := by decide
  have hdescent : baseEnd_6255697 < baseStart_6255697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255698 : List Nat := [3, 2, 2, 1, 3, 2, 1, 4, 1, 1, 3]
def baseStart_6255698 : Nat := 118140960795 + 6255698 * 2 ^ 59
def prefixEnd_6255698 : Nat := 4983230072969 + 3 ^ 40 * 6255698 * 2
def baseEnd_6255698 : Nat := 3212179903369970786505575

theorem tailTrace_6255698 : CollatzResearch.WordTrace tailWord_6255698 prefixEnd_6255698 3212179903369970786505575 := by
  unfold tailWord_6255698
  simp only [CollatzResearch.WordTrace]
  refine ⟨57041012622670502251195937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152109366993788006003189165 57041012622670502251195937)
  ·
    refine ⟨42780759467002876688396953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57041012622670502251195937 42780759467002876688396953)
    ·
      refine ⟨32085569600252157516297715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42780759467002876688396953 32085569600252157516297715)
      ·
        refine ⟨48128354400378236274446573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32085569600252157516297715 48128354400378236274446573)
        ·
          refine ⟨18048132900141838602917465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48128354400378236274446573 18048132900141838602917465)
          ·
            refine ⟨13536099675106378952188099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18048132900141838602917465 13536099675106378952188099)
            ·
              refine ⟨20304149512659568428282149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13536099675106378952188099 20304149512659568428282149)
              ·
                refine ⟨3807028033623669080302903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20304149512659568428282149 3807028033623669080302903)
                ·
                  refine ⟨5710542050435503620454355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3807028033623669080302903 5710542050435503620454355)
                  ·
                    refine ⟨8565813075653255430681533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5710542050435503620454355 8565813075653255430681533)
                    ·
                      refine ⟨3212179903369970786505575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8565813075653255430681533 3212179903369970786505575)
                      ·
                        rfl

theorem cell23_6255698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_6255698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255698 prefixEnd_6255698 := by exact prefixLift 6255698
  have htrace : WordTrace (prefixWord ++ tailWord_6255698) baseStart_6255698 baseEnd_6255698 := by
    simpa [prefixWord, tailWord_6255698, baseEnd_6255698] using wordTrace_append hprefix tailTrace_6255698
  have hstable : (prefixWord ++ tailWord_6255698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255698).length < 2 ^ (prefixWord ++ tailWord_6255698).sum := by decide
  have hdescent : baseEnd_6255698 < baseStart_6255698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255714 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_6255714 : Nat := 118140960795 + 6255714 * 2 ^ 59
def prefixEnd_6255714 : Nat := 4983230072969 + 3 ^ 40 * 6255714 * 2
def baseEnd_6255714 : Nat := 1070729373020147574635167

theorem tailTrace_6255714 : CollatzResearch.WordTrace tailWord_6255714 prefixEnd_6255714 1070729373020147574635167 := by
  unfold tailWord_6255714
  simp only [CollatzResearch.WordTrace]
  refine ⟨57041158514656010934341549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152109756039082695824910797 57041158514656010934341549)
  ·
    refine ⟨21390434442996004100378081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57041158514656010934341549 21390434442996004100378081)
    ·
      refine ⟨16042825832247003075283561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21390434442996004100378081 16042825832247003075283561)
      ·
        refine ⟨12032119374185252306462671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16042825832247003075283561 12032119374185252306462671)
        ·
          refine ⟨18048179061277878459694007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12032119374185252306462671 18048179061277878459694007)
          ·
            refine ⟨27072268591916817689541011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18048179061277878459694007 27072268591916817689541011)
            ·
              refine ⟨40608402887875226534311517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27072268591916817689541011 40608402887875226534311517)
              ·
                refine ⟨15228151082953209950366819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40608402887875226534311517 15228151082953209950366819)
                ·
                  refine ⟨22842226624429814925550229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15228151082953209950366819 22842226624429814925550229)
                  ·
                    refine ⟨1070729373020147574635167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22842226624429814925550229 1070729373020147574635167)
                    ·
                      rfl

theorem cell23_6255714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_6255714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255714 prefixEnd_6255714 := by exact prefixLift 6255714
  have htrace : WordTrace (prefixWord ++ tailWord_6255714) baseStart_6255714 baseEnd_6255714 := by
    simpa [prefixWord, tailWord_6255714, baseEnd_6255714] using wordTrace_append hprefix tailTrace_6255714
  have hstable : (prefixWord ++ tailWord_6255714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255714).length < 2 ^ (prefixWord ++ tailWord_6255714).sum := by decide
  have hdescent : baseEnd_6255714 < baseStart_6255714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255721 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 3, 2, 2]
def baseStart_6255721 : Nat := 118140960795 + 6255721 * 2 ^ 59
def prefixEnd_6255721 : Nat := 4983230072969 + 3 ^ 40 * 6255721 * 2
def baseEnd_6255721 : Nat := 3212191713425024196517969

theorem tailTrace_6255721 : CollatzResearch.WordTrace tailWord_6255721 prefixEnd_6255721 3212191713425024196517969 := by
  unfold tailWord_6255721
  simp only [CollatzResearch.WordTrace]
  refine ⟨228164889369598683932871017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152109926246399122621914011 228164889369598683932871017)
  ·
    refine ⟨171123667027199012949653263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228164889369598683932871017 171123667027199012949653263)
    ·
      refine ⟨256685500540798519424479895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171123667027199012949653263 256685500540798519424479895)
      ·
        refine ⟨385028250811197779136719843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256685500540798519424479895 385028250811197779136719843)
        ·
          refine ⟨577542376216796668705079765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385028250811197779136719843 577542376216796668705079765)
          ·
            refine ⟨13536149442581171922775307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 577542376216796668705079765 13536149442581171922775307)
            ·
              refine ⟨20304224163871757884162961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13536149442581171922775307 20304224163871757884162961)
              ·
                refine ⟨15228168122903818413122221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20304224163871757884162961 15228168122903818413122221)
                ·
                  refine ⟨5710563046088931904920833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15228168122903818413122221 5710563046088931904920833)
                  ·
                    refine ⟨4282922284566698928690625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5710563046088931904920833 4282922284566698928690625)
                    ·
                      refine ⟨3212191713425024196517969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282922284566698928690625 3212191713425024196517969)
                      ·
                        rfl

theorem cell23_6255721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 2, 2].length) (baseStart_6255721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255721 prefixEnd_6255721 := by exact prefixLift 6255721
  have htrace : WordTrace (prefixWord ++ tailWord_6255721) baseStart_6255721 baseEnd_6255721 := by
    simpa [prefixWord, tailWord_6255721, baseEnd_6255721] using wordTrace_append hprefix tailTrace_6255721
  have hstable : (prefixWord ++ tailWord_6255721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255721).length < 2 ^ (prefixWord ++ tailWord_6255721).sum := by decide
  have hdescent : baseEnd_6255721 < baseStart_6255721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255724 : List Nat := [2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 3]
def baseStart_6255724 : Nat := 118140960795 + 6255724 * 2 ^ 59
def prefixEnd_6255724 : Nat := 4983230072969 + 3 ^ 40 * 6255724 * 2
def baseEnd_6255724 : Nat := 3212193253866987684780455

theorem tailTrace_6255724 : CollatzResearch.WordTrace tailWord_6255724 prefixEnd_6255724 3212193253866987684780455 := by
  unfold tailWord_6255724
  simp only [CollatzResearch.WordTrace]
  refine ⟨114082499394293907722615113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152109999192391876963486817 114082499394293907722615113)
  ·
    refine ⟨85561874545720430791961335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114082499394293907722615113 85561874545720430791961335)
    ·
      refine ⟨128342811818580646187942003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85561874545720430791961335 128342811818580646187942003)
      ·
        refine ⟨192514217727870969281913005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128342811818580646187942003 192514217727870969281913005)
        ·
          refine ⟨72192831647951613480717377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192514217727870969281913005 72192831647951613480717377)
          ·
            refine ⟨54144623735963710110538033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72192831647951613480717377 54144623735963710110538033)
            ·
              refine ⟨40608467801972782582903525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54144623735963710110538033 40608467801972782582903525)
              ·
                refine ⟨7614087712869896734294411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40608467801972782582903525 7614087712869896734294411)
                ·
                  refine ⟨11421131569304845101441617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7614087712869896734294411 11421131569304845101441617)
                  ·
                    refine ⟨8565848676978633826081213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11421131569304845101441617 8565848676978633826081213)
                    ·
                      refine ⟨3212193253866987684780455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8565848676978633826081213 3212193253866987684780455)
                      ·
                        rfl

theorem cell23_6255724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_6255724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255724 prefixEnd_6255724 := by exact prefixLift 6255724
  have htrace : WordTrace (prefixWord ++ tailWord_6255724) baseStart_6255724 baseEnd_6255724 := by
    simpa [prefixWord, tailWord_6255724, baseEnd_6255724] using wordTrace_append hprefix tailTrace_6255724
  have hstable : (prefixWord ++ tailWord_6255724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255724).length < 2 ^ (prefixWord ++ tailWord_6255724).sum := by decide
  have hdescent : baseEnd_6255724 < baseStart_6255724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255727 : List Nat := [1, 1, 2, 1, 3, 3, 5, 7]
def baseStart_6255727 : Nat := 118140960795 + 6255727 * 2 ^ 59
def prefixEnd_6255727 : Nat := 4983230072969 + 3 ^ 40 * 6255727 * 2
def baseEnd_6255727 : Nat := 118970177566998191594183

theorem tailTrace_6255727 : CollatzResearch.WordTrace tailWord_6255727 prefixEnd_6255727 118970177566998191594183 := by
  unfold tailWord_6255727
  simp only [CollatzResearch.WordTrace]
  refine ⟨228165108207576946957589435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152110072138384631305059623 228165108207576946957589435)
  ·
    refine ⟨342247662311365420436384153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228165108207576946957589435 342247662311365420436384153)
    ·
      refine ⟨256685746733524065327288115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342247662311365420436384153 256685746733524065327288115)
      ·
        refine ⟨385028620100286097990932173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256685746733524065327288115 385028620100286097990932173)
        ·
          refine ⟨144385732537607286746599565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385028620100286097990932173 144385732537607286746599565)
          ·
            refine ⟨54144649701602732529974837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144385732537607286746599565 54144649701602732529974837)
            ·
              refine ⟨5076060909525256174685141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54144649701602732529974837 5076060909525256174685141)
              ·
                refine ⟨118970177566998191594183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5076060909525256174685141 118970177566998191594183)
                ·
                  rfl

theorem cell23_6255727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 7].length) (baseStart_6255727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255727 prefixEnd_6255727 := by exact prefixLift 6255727
  have htrace : WordTrace (prefixWord ++ tailWord_6255727) baseStart_6255727 baseEnd_6255727 := by
    simpa [prefixWord, tailWord_6255727, baseEnd_6255727] using wordTrace_append hprefix tailTrace_6255727
  have hstable : (prefixWord ++ tailWord_6255727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255727).length < 2 ^ (prefixWord ++ tailWord_6255727).sum := by decide
  have hdescent : baseEnd_6255727 < baseStart_6255727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255734 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_6255734 : Nat := 118140960795 + 6255734 * 2 ^ 59
def prefixEnd_6255734 : Nat := 4983230072969 + 3 ^ 40 * 6255734 * 2
def baseEnd_6255734 : Nat := 3212198388673532645655409

theorem tailTrace_6255734 : CollatzResearch.WordTrace tailWord_6255734 prefixEnd_6255734 3212198388673532645655409 := by
  unfold tailWord_6255734
  simp only [CollatzResearch.WordTrace]
  refine ⟨14260335219909474197068391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152110242345701058102062837 14260335219909474197068391)
  ·
    refine ⟨21390502829864211295602587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14260335219909474197068391 21390502829864211295602587)
    ·
      refine ⟨32085754244796316943403881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21390502829864211295602587 32085754244796316943403881)
      ·
        refine ⟨24064315683597237707552911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32085754244796316943403881 24064315683597237707552911)
        ·
          refine ⟨36096473525395856561329367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24064315683597237707552911 36096473525395856561329367)
          ·
            refine ⟨54144710288093784841994051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36096473525395856561329367 54144710288093784841994051)
            ·
              refine ⟨81217065432140677262991077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54144710288093784841994051 81217065432140677262991077)
              ·
                refine ⟨15228199768526376986810827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81217065432140677262991077 15228199768526376986810827)
                ·
                  refine ⟨22842299652789565480216241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15228199768526376986810827 22842299652789565480216241)
                  ·
                    refine ⟨17131724739592174110162181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22842299652789565480216241 17131724739592174110162181)
                    ·
                      refine ⟨3212198388673532645655409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17131724739592174110162181 3212198388673532645655409)
                      ·
                        rfl

theorem cell23_6255734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_6255734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255734 prefixEnd_6255734 := by exact prefixLift 6255734
  have htrace : WordTrace (prefixWord ++ tailWord_6255734) baseStart_6255734 baseEnd_6255734 := by
    simpa [prefixWord, tailWord_6255734, baseEnd_6255734] using wordTrace_append hprefix tailTrace_6255734
  have hstable : (prefixWord ++ tailWord_6255734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255734).length < 2 ^ (prefixWord ++ tailWord_6255734).sum := by decide
  have hdescent : baseEnd_6255734 < baseStart_6255734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255778 : List Nat := [3, 3, 1, 3, 3, 1, 2, 7]
def baseStart_6255778 : Nat := 118140960795 + 6255778 * 2 ^ 59
def prefixEnd_6255778 : Nat := 4983230072969 + 3 ^ 40 * 6255778 * 2
def baseEnd_6255778 : Nat := 118971147474901128648341

theorem tailTrace_6255778 : CollatzResearch.WordTrace tailWord_6255778 prefixEnd_6255778 118971147474901128648341 := by
  unfold tailWord_6255778
  simp only [CollatzResearch.WordTrace]
  refine ⟨57041742082598045666923997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152111312220261455111797325 57041742082598045666923997)
  ·
    refine ⟨21390653280974267125096499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57041742082598045666923997 21390653280974267125096499)
    ·
      refine ⟨32085979921461400687644749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21390653280974267125096499 32085979921461400687644749)
      ·
        refine ⟨12032242470548025257866781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32085979921461400687644749 12032242470548025257866781)
        ·
          refine ⟨4512090926455509471700043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12032242470548025257866781 4512090926455509471700043)
          ·
            refine ⟨6768136389683264207550065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4512090926455509471700043 6768136389683264207550065)
            ·
              refine ⟨5076102292262448155662549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6768136389683264207550065 5076102292262448155662549)
              ·
                refine ⟨118971147474901128648341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5076102292262448155662549 118971147474901128648341)
                ·
                  rfl

theorem cell23_6255778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 7].length) (baseStart_6255778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255778 prefixEnd_6255778 := by exact prefixLift 6255778
  have htrace : WordTrace (prefixWord ++ tailWord_6255778) baseStart_6255778 baseEnd_6255778 := by
    simpa [prefixWord, tailWord_6255778, baseEnd_6255778] using wordTrace_append hprefix tailTrace_6255778
  have hstable : (prefixWord ++ tailWord_6255778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255778).length < 2 ^ (prefixWord ++ tailWord_6255778).sum := by decide
  have hdescent : baseEnd_6255778 < baseStart_6255778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255781 : List Nat := [1, 3, 1, 2, 1, 4, 1, 4, 1, 3, 2]
def baseStart_6255781 : Nat := 118140960795 + 6255781 * 2 ^ 59
def prefixEnd_6255781 : Nat := 4983230072969 + 3 ^ 40 * 6255781 * 2
def baseEnd_6255781 : Nat := 3212222522264293961767693

theorem tailTrace_6255781 : CollatzResearch.WordTrace tailWord_6255781 prefixEnd_6255781 3212222522264293961767693 := by
  unfold tailWord_6255781
  simp only [CollatzResearch.WordTrace]
  refine ⟨228167077749381314180055197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152111385166254209453370131 228167077749381314180055197)
  ·
    refine ⟨85562654156017992817520699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228167077749381314180055197 85562654156017992817520699)
    ·
      refine ⟨128343981234026989226281049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85562654156017992817520699 128343981234026989226281049)
      ·
        refine ⟨96257985925520241919710787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128343981234026989226281049 96257985925520241919710787)
        ·
          refine ⟨144386978888280362879566181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96257985925520241919710787 144386978888280362879566181)
          ·
            refine ⟨27072558541552568039918659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144386978888280362879566181 27072558541552568039918659)
            ·
              refine ⟨40608837812328852059877989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27072558541552568039918659 40608837812328852059877989)
              ·
                refine ⟨7614157089811659761227123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40608837812328852059877989 7614157089811659761227123)
                ·
                  refine ⟨11421235634717489641840685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7614157089811659761227123 11421235634717489641840685)
                  ·
                    refine ⟨4282963363019058615690257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11421235634717489641840685 4282963363019058615690257)
                    ·
                      refine ⟨3212222522264293961767693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282963363019058615690257 3212222522264293961767693)
                      ·
                        rfl

theorem cell23_6255781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_6255781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255781 prefixEnd_6255781 := by exact prefixLift 6255781
  have htrace : WordTrace (prefixWord ++ tailWord_6255781) baseStart_6255781 baseEnd_6255781 := by
    simpa [prefixWord, tailWord_6255781, baseEnd_6255781] using wordTrace_append hprefix tailTrace_6255781
  have hstable : (prefixWord ++ tailWord_6255781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255781).length < 2 ^ (prefixWord ++ tailWord_6255781).sum := by decide
  have hdescent : baseEnd_6255781 < baseStart_6255781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255789 : List Nat := [1, 5, 2, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_6255789 : Nat := 118140960795 + 6255789 * 2 ^ 59
def prefixEnd_6255789 : Nat := 4983230072969 + 3 ^ 40 * 6255789 * 2
def baseEnd_6255789 : Nat := 3212226630109529930467657

theorem tailTrace_6255789 : CollatzResearch.WordTrace tailWord_6255789 prefixEnd_6255789 3212226630109529930467657 := by
  unfold tailWord_6255789
  simp only [CollatzResearch.WordTrace]
  refine ⟨228167369533352331546346421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152111579688901554364230947 228167369533352331546346421)
  ·
    refine ⟨21390690893751781082469977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228167369533352331546346421 21390690893751781082469977)
    ·
      refine ⟨16043018170313835811852483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21390690893751781082469977 16043018170313835811852483)
      ·
        refine ⟨24064527255470753717778725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16043018170313835811852483 24064527255470753717778725)
        ·
          refine ⟨4512098860400766322083511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24064527255470753717778725 4512098860400766322083511)
          ·
            refine ⟨6768148290601149483125267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4512098860400766322083511 6768148290601149483125267)
            ·
              refine ⟨10152222435901724224687901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6768148290601149483125267 10152222435901724224687901)
              ·
                refine ⟨3807083413463146584257963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10152222435901724224687901 3807083413463146584257963)
                ·
                  refine ⟨5710625120194719876386945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3807083413463146584257963 5710625120194719876386945)
                  ·
                    refine ⟨4282968840146039907290209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5710625120194719876386945 4282968840146039907290209)
                    ·
                      refine ⟨3212226630109529930467657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4282968840146039907290209 3212226630109529930467657)
                      ·
                        rfl

theorem cell23_6255789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_6255789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255789 prefixEnd_6255789 := by exact prefixLift 6255789
  have htrace : WordTrace (prefixWord ++ tailWord_6255789) baseStart_6255789 baseEnd_6255789 := by
    simpa [prefixWord, tailWord_6255789, baseEnd_6255789] using wordTrace_append hprefix tailTrace_6255789
  have hstable : (prefixWord ++ tailWord_6255789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255789).length < 2 ^ (prefixWord ++ tailWord_6255789).sum := by decide
  have hdescent : baseEnd_6255789 < baseStart_6255789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255807 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 4]
def baseStart_6255807 : Nat := 118140960795 + 6255807 * 2 ^ 59
def prefixEnd_6255807 : Nat := 4983230072969 + 3 ^ 40 * 6255807 * 2
def baseEnd_6255807 : Nat := 3212235872761310860042573

theorem tailTrace_6255807 : CollatzResearch.WordTrace tailWord_6255807 prefixEnd_6255807 3212235872761310860042573 := by
  unfold tailWord_6255807
  simp only [CollatzResearch.WordTrace]
  refine ⟨228168026047287120620501675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152112017364858080413667783 228168026047287120620501675)
  ·
    refine ⟨342252039070930680930752513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228168026047287120620501675 342252039070930680930752513)
    ·
      refine ⟨256689029303198010698064385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342252039070930680930752513 256689029303198010698064385)
      ·
        refine ⟨192516771977398508023548289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256689029303198010698064385 192516771977398508023548289)
        ·
          refine ⟨144387578983048881017661217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192516771977398508023548289 144387578983048881017661217)
          ·
            refine ⟨108290684237286660763245913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144387578983048881017661217 108290684237286660763245913)
            ·
              refine ⟨81218013177964995572434435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108290684237286660763245913 81218013177964995572434435)
              ·
                refine ⟨121827019766947493358651653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81218013177964995572434435 121827019766947493358651653)
                ·
                  refine ⟨22842566206302655004747185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121827019766947493358651653 22842566206302655004747185)
                  ·
                    refine ⟨17131924654726991253560389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22842566206302655004747185 17131924654726991253560389)
                    ·
                      refine ⟨3212235872761310860042573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17131924654726991253560389 3212235872761310860042573)
                      ·
                        rfl

theorem cell23_6255807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_6255807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255807 prefixEnd_6255807 := by exact prefixLift 6255807
  have htrace : WordTrace (prefixWord ++ tailWord_6255807) baseStart_6255807 baseEnd_6255807 := by
    simpa [prefixWord, tailWord_6255807, baseEnd_6255807] using wordTrace_append hprefix tailTrace_6255807
  have hstable : (prefixWord ++ tailWord_6255807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255807).length < 2 ^ (prefixWord ++ tailWord_6255807).sum := by decide
  have hdescent : baseEnd_6255807 < baseStart_6255807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255822 : List Nat := [4, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3]
def baseStart_6255822 : Nat := 118140960795 + 6255822 * 2 ^ 59
def prefixEnd_6255822 : Nat := 4983230072969 + 3 ^ 40 * 6255822 * 2
def baseEnd_6255822 : Nat := 3212243574971128301355005

theorem tailTrace_6255822 : CollatzResearch.WordTrace tailWord_6255822 prefixEnd_6255822 3212243574971128301355005 := by
  unfold tailWord_6255822
  simp only [CollatzResearch.WordTrace]
  refine ⟨28521071642779097272787215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152112382094821852121531813 28521071642779097272787215)
  ·
    refine ⟨42781607464168645909180823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28521071642779097272787215 42781607464168645909180823)
    ·
      refine ⟨64172411196252968863771235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42781607464168645909180823 64172411196252968863771235)
      ·
        refine ⟨96258616794379453295656853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64172411196252968863771235 96258616794379453295656853)
        ·
          refine ⟨4512122662236536873233915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96258616794379453295656853 4512122662236536873233915)
          ·
            refine ⟨6768183993354805309850873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4512122662236536873233915 6768183993354805309850873)
            ·
              refine ⟨5076137995016103982388155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6768183993354805309850873 5076137995016103982388155)
              ·
                refine ⟨7614206992524155973582233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5076137995016103982388155 7614206992524155973582233)
                ·
                  refine ⟨5710655244393116980186675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7614206992524155973582233 5710655244393116980186675)
                  ·
                    refine ⟨8565982866589675470280013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5710655244393116980186675 8565982866589675470280013)
                    ·
                      refine ⟨3212243574971128301355005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8565982866589675470280013 3212243574971128301355005)
                      ·
                        rfl

theorem cell23_6255822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_6255822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255822 prefixEnd_6255822 := by exact prefixLift 6255822
  have htrace : WordTrace (prefixWord ++ tailWord_6255822) baseStart_6255822 baseEnd_6255822 := by
    simpa [prefixWord, tailWord_6255822, baseEnd_6255822] using wordTrace_append hprefix tailTrace_6255822
  have hstable : (prefixWord ++ tailWord_6255822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255822).length < 2 ^ (prefixWord ++ tailWord_6255822).sum := by decide
  have hdescent : baseEnd_6255822 < baseStart_6255822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255897 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 6]
def baseStart_6255897 : Nat := 118140960795 + 6255897 * 2 ^ 59
def prefixEnd_6255897 : Nat := 4983230072969 + 3 ^ 40 * 6255897 * 2
def baseEnd_6255897 : Nat := 3212282086020215507917159

theorem tailTrace_6255897 : CollatzResearch.WordTrace tailWord_6255897 prefixEnd_6255897 3212282086020215507917159 := by
  unfold tailWord_6255897
  simp only [CollatzResearch.WordTrace]
  refine ⟨228171308616961065991277945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152114205744640710660851963 228171308616961065991277945)
  ·
    refine ⟨171128481462720799493458459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228171308616961065991277945 171128481462720799493458459)
    ·
      refine ⟨256692722194081199240187689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171128481462720799493458459 256692722194081199240187689)
      ·
        refine ⟨192519541645560899430140767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256692722194081199240187689 192519541645560899430140767)
        ·
          refine ⟨288779312468341349145211151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192519541645560899430140767 288779312468341349145211151)
          ·
            refine ⟨433168968702512023717816727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288779312468341349145211151 433168968702512023717816727)
            ·
              refine ⟨649753453053768035576725091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433168968702512023717816727 649753453053768035576725091)
              ·
                refine ⟨974630179580652053365087637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649753453053768035576725091 974630179580652053365087637)
                ·
                  refine ⟨45685789667843065001488483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 974630179580652053365087637 45685789667843065001488483)
                  ·
                    refine ⟨68528684501764597502232725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45685789667843065001488483 68528684501764597502232725)
                    ·
                      refine ⟨3212282086020215507917159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68528684501764597502232725 3212282086020215507917159)
                      ·
                        rfl

theorem cell23_6255897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_6255897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255897 prefixEnd_6255897 := by exact prefixLift 6255897
  have htrace : WordTrace (prefixWord ++ tailWord_6255897) baseStart_6255897 baseEnd_6255897 := by
    simpa [prefixWord, tailWord_6255897, baseEnd_6255897] using wordTrace_append hprefix tailTrace_6255897
  have hstable : (prefixWord ++ tailWord_6255897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255897).length < 2 ^ (prefixWord ++ tailWord_6255897).sum := by decide
  have hdescent : baseEnd_6255897 < baseStart_6255897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255901 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_6255901 : Nat := 118140960795 + 6255901 * 2 ^ 59
def prefixEnd_6255901 : Nat := 4983230072969 + 3 ^ 40 * 6255901 * 2
def baseEnd_6255901 : Nat := 3212284139942833492267141

theorem tailTrace_6255901 : CollatzResearch.WordTrace tailWord_6255901 prefixEnd_6255901 3212284139942833492267141 := by
  unfold tailWord_6255901
  simp only [CollatzResearch.WordTrace]
  refine ⟨228171454508946574674423557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152114303005964383116282371 228171454508946574674423557)
  ·
    refine ⟨42782147720427482751454417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228171454508946574674423557 42782147720427482751454417)
    ·
      refine ⟨32086610790320612063590813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42782147720427482751454417 32086610790320612063590813)
      ·
        refine ⟨12032479046370229523846555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32086610790320612063590813 12032479046370229523846555)
        ·
          refine ⟨18048718569555344285769833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12032479046370229523846555 18048718569555344285769833)
          ·
            refine ⟨13536538927166508214327375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18048718569555344285769833 13536538927166508214327375)
            ·
              refine ⟨20304808390749762321491063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13536538927166508214327375 20304808390749762321491063)
              ·
                refine ⟨30457212586124643482236595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20304808390749762321491063 30457212586124643482236595)
                ·
                  refine ⟨45685818879186965223354893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30457212586124643482236595 45685818879186965223354893)
                  ·
                    refine ⟨17132182079695111958758085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45685818879186965223354893 17132182079695111958758085)
                    ·
                      refine ⟨3212284139942833492267141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17132182079695111958758085 3212284139942833492267141)
                      ·
                        rfl

theorem cell23_6255901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_6255901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255901 prefixEnd_6255901 := by exact prefixLift 6255901
  have htrace : WordTrace (prefixWord ++ tailWord_6255901) baseStart_6255901 baseEnd_6255901 := by
    simpa [prefixWord, tailWord_6255901, baseEnd_6255901] using wordTrace_append hprefix tailTrace_6255901
  have hstable : (prefixWord ++ tailWord_6255901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255901).length < 2 ^ (prefixWord ++ tailWord_6255901).sum := by decide
  have hdescent : baseEnd_6255901 < baseStart_6255901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255961 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 1, 5, 2]
def baseStart_6255961 : Nat := 118140960795 + 6255961 * 2 ^ 59
def prefixEnd_6255961 : Nat := 4983230072969 + 3 ^ 40 * 6255961 * 2
def baseEnd_6255961 : Nat := 3212314948782103257516865

theorem tailTrace_6255961 : CollatzResearch.WordTrace tailWord_6255961 prefixEnd_6255961 3212314948782103257516865 := by
  unfold tailWord_6255961
  simp only [CollatzResearch.WordTrace]
  refine ⟨228173642888729204921607737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152115761925819469947738491 228173642888729204921607737)
  ·
    refine ⟨171130232166546903691205803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228173642888729204921607737 171130232166546903691205803)
    ·
      refine ⟨256695348249820355536808705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171130232166546903691205803 256695348249820355536808705)
      ·
        refine ⟨192521511187365266652606529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256695348249820355536808705 192521511187365266652606529)
        ·
          refine ⟨144391133390523949989454897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192521511187365266652606529 144391133390523949989454897)
          ·
            refine ⟨108293350042892962492091173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144391133390523949989454897 108293350042892962492091173)
            ·
              refine ⟨20305003133042430467267095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108293350042892962492091173 20305003133042430467267095)
              ·
                refine ⟨30457504699563645700900643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20305003133042430467267095 30457504699563645700900643)
                ·
                  refine ⟨45686257049345468551350965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30457504699563645700900643 45686257049345468551350965)
                  ·
                    refine ⟨4283086598376137676689153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45686257049345468551350965 4283086598376137676689153)
                    ·
                      refine ⟨3212314948782103257516865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4283086598376137676689153 3212314948782103257516865)
                      ·
                        rfl

theorem cell23_6255961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 5, 2].length) (baseStart_6255961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255961 prefixEnd_6255961 := by exact prefixLift 6255961
  have htrace : WordTrace (prefixWord ++ tailWord_6255961) baseStart_6255961 baseEnd_6255961 := by
    simpa [prefixWord, tailWord_6255961, baseEnd_6255961] using wordTrace_append hprefix tailTrace_6255961
  have hstable : (prefixWord ++ tailWord_6255961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255961).length < 2 ^ (prefixWord ++ tailWord_6255961).sum := by decide
  have hdescent : baseEnd_6255961 < baseStart_6255961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6255971 : List Nat := [1, 1, 1, 5, 2, 2, 2, 3, 1, 5]
def baseStart_6255971 : Nat := 118140960795 + 6255971 * 2 ^ 59
def prefixEnd_6255971 : Nat := 4983230072969 + 3 ^ 40 * 6255971 * 2
def baseEnd_6255971 : Nat := 1070773361196216072797273

theorem tailTrace_6255971 : CollatzResearch.WordTrace tailWord_6255971 prefixEnd_6255971 1070773361196216072797273 := by
  unfold tailWord_6255971
  simp only [CollatzResearch.WordTrace]
  refine ⟨228174007618692976629471767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152116005079128651086314511 228174007618692976629471767)
  ·
    refine ⟨342261011428039464944207651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228174007618692976629471767 342261011428039464944207651)
    ·
      refine ⟨513391517142059197416311477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342261011428039464944207651 513391517142059197416311477)
      ·
        refine ⟨48130454732068049757779201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 513391517142059197416311477 48130454732068049757779201)
        ·
          refine ⟨36097841049051037318334401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48130454732068049757779201 36097841049051037318334401)
          ·
            refine ⟨27073380786788277988750801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36097841049051037318334401 27073380786788277988750801)
            ·
              refine ⟨20305035590091208491563101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27073380786788277988750801 20305035590091208491563101)
              ·
                refine ⟨7614388346284203184336163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20305035590091208491563101 7614388346284203184336163)
                ·
                  refine ⟨11421582519426304776504245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7614388346284203184336163 11421582519426304776504245)
                  ·
                    refine ⟨1070773361196216072797273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11421582519426304776504245 1070773361196216072797273)
                    ·
                      rfl

theorem cell23_6255971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 5].length) (baseStart_6255971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6255971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6255971 prefixEnd_6255971 := by exact prefixLift 6255971
  have htrace : WordTrace (prefixWord ++ tailWord_6255971) baseStart_6255971 baseEnd_6255971 := by
    simpa [prefixWord, tailWord_6255971, baseEnd_6255971] using wordTrace_append hprefix tailTrace_6255971
  have hstable : (prefixWord ++ tailWord_6255971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6255971).length < 2 ^ (prefixWord ++ tailWord_6255971).sum := by decide
  have hdescent : baseEnd_6255971 < baseStart_6255971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6255971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256008 : List Nat := [2, 1, 3, 3, 1, 2, 3, 2, 1, 1, 4]
def baseStart_6256008 : Nat := 118140960795 + 6256008 * 2 ^ 59
def prefixEnd_6256008 : Nat := 4983230072969 + 3 ^ 40 * 6256008 * 2
def baseEnd_6256008 : Nat := 3212339082372864573629149

theorem tailTrace_6256008 : CollatzResearch.WordTrace tailWord_6256008 prefixEnd_6256008 3212339082372864573629149 := by
  unfold tailWord_6256008
  simp only [CollatzResearch.WordTrace]
  refine ⟨114087678559779465974284339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152116904746372621299045785 114087678559779465974284339)
  ·
    refine ⟨171131517839669198961426509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114087678559779465974284339 171131517839669198961426509)
    ·
      refine ⟨64174319189875949610534941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171131517839669198961426509 64174319189875949610534941)
      ·
        refine ⟨24065369696203481103950603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64174319189875949610534941 24065369696203481103950603)
        ·
          refine ⟨36098054544305221655925905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24065369696203481103950603 36098054544305221655925905)
          ·
            refine ⟨27073540908228916241944429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36098054544305221655925905 27073540908228916241944429)
            ·
              refine ⟨10152577840585843590729161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27073540908228916241944429 10152577840585843590729161)
              ·
                refine ⟨7614433380439382693046871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10152577840585843590729161 7614433380439382693046871)
                ·
                  refine ⟨11421650070659074039570307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7614433380439382693046871 11421650070659074039570307)
                  ·
                    refine ⟨17132475105988611059355461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11421650070659074039570307 17132475105988611059355461)
                    ·
                      refine ⟨3212339082372864573629149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17132475105988611059355461 3212339082372864573629149)
                      ·
                        rfl

theorem cell23_6256008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_6256008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256008 prefixEnd_6256008 := by exact prefixLift 6256008
  have htrace : WordTrace (prefixWord ++ tailWord_6256008) baseStart_6256008 baseEnd_6256008 := by
    simpa [prefixWord, tailWord_6256008, baseEnd_6256008] using wordTrace_append hprefix tailTrace_6256008
  have hstable : (prefixWord ++ tailWord_6256008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256008).length < 2 ^ (prefixWord ++ tailWord_6256008).sum := by decide
  have hdescent : baseEnd_6256008 < baseStart_6256008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256011 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 3]
def baseStart_6256011 : Nat := 118140960795 + 6256011 * 2 ^ 59
def prefixEnd_6256011 : Nat := 4983230072969 + 3 ^ 40 * 6256011 * 2
def baseEnd_6256011 : Nat := 3212340622814828061891635

theorem tailTrace_6256011 : CollatzResearch.WordTrace tailWord_6256011 prefixEnd_6256011 3212340622814828061891635 := by
  unfold tailWord_6256011
  simp only [CollatzResearch.WordTrace]
  refine ⟨228175466538548063460927887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152116977692365375640618591 228175466538548063460927887)
  ·
    refine ⟨342263199807822095191391831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228175466538548063460927887 342263199807822095191391831)
    ·
      refine ⟨513394799711733142787087747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342263199807822095191391831 513394799711733142787087747)
      ·
        refine ⟨770092199567599714180631621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513394799711733142787087747 770092199567599714180631621)
        ·
          refine ⟨144392287418924946408868429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 770092199567599714180631621 144392287418924946408868429)
          ·
            refine ⟨54147107782096854903325661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144392287418924946408868429 54147107782096854903325661)
            ·
              refine ⟨20305165418286320588747123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54147107782096854903325661 20305165418286320588747123)
              ·
                refine ⟨30457748127429480883120685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20305165418286320588747123 30457748127429480883120685)
                ·
                  refine ⟨11421655547786055331170257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30457748127429480883120685 11421655547786055331170257)
                  ·
                    refine ⟨8566241660839541498377693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11421655547786055331170257 8566241660839541498377693)
                    ·
                      refine ⟨3212340622814828061891635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8566241660839541498377693 3212340622814828061891635)
                      ·
                        rfl

theorem cell23_6256011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 3].length) (baseStart_6256011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256011 prefixEnd_6256011 := by exact prefixLift 6256011
  have htrace : WordTrace (prefixWord ++ tailWord_6256011) baseStart_6256011 baseEnd_6256011 := by
    simpa [prefixWord, tailWord_6256011, baseEnd_6256011] using wordTrace_append hprefix tailTrace_6256011
  have hstable : (prefixWord ++ tailWord_6256011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256011).length < 2 ^ (prefixWord ++ tailWord_6256011).sum := by decide
  have hdescent : baseEnd_6256011 < baseStart_6256011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256044 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 2, 7]
def baseStart_6256044 : Nat := 118140960795 + 6256044 * 2 ^ 59
def prefixEnd_6256044 : Nat := 4983230072969 + 3 ^ 40 * 6256044 * 2
def baseEnd_6256044 : Nat := 1070785855892142144259661

theorem tailTrace_6256044 : CollatzResearch.WordTrace tailWord_6256044 prefixEnd_6256044 1070785855892142144259661 := by
  unfold tailWord_6256044
  simp only [CollatzResearch.WordTrace]
  refine ⟨114088335073714255048439593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152117780098285673397919457 114088335073714255048439593)
  ·
    refine ⟨85566251305285691286329695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114088335073714255048439593 85566251305285691286329695)
    ·
      refine ⟨128349376957928536929494543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85566251305285691286329695 128349376957928536929494543)
      ·
        refine ⟨192524065436892805394241815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128349376957928536929494543 192524065436892805394241815)
        ·
          refine ⟨288786098155339208091362723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192524065436892805394241815 288786098155339208091362723)
          ·
            refine ⟨433179147233008812137044085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288786098155339208091362723 433179147233008812137044085)
            ·
              refine ⟨40610545053094576137847883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 433179147233008812137044085 40610545053094576137847883)
              ·
                refine ⟨60915817579641864206771825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40610545053094576137847883 60915817579641864206771825)
                ·
                  refine ⟨45686863184731398155078869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60915817579641864206771825 45686863184731398155078869)
                  ·
                    refine ⟨1070785855892142144259661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45686863184731398155078869 1070785855892142144259661)
                    ·
                      rfl

theorem cell23_6256044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_6256044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256044 prefixEnd_6256044 := by exact prefixLift 6256044
  have htrace : WordTrace (prefixWord ++ tailWord_6256044) baseStart_6256044 baseEnd_6256044 := by
    simpa [prefixWord, tailWord_6256044, baseEnd_6256044] using wordTrace_append hprefix tailTrace_6256044
  have hstable : (prefixWord ++ tailWord_6256044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256044).length < 2 ^ (prefixWord ++ tailWord_6256044).sum := by decide
  have hdescent : baseEnd_6256044 < baseStart_6256044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256085 : List Nat := [1, 3, 2, 3, 1, 1, 3, 3, 1, 3, 2]
def baseStart_6256085 : Nat := 118140960795 + 6256085 * 2 ^ 59
def prefixEnd_6256085 : Nat := 4983230072969 + 3 ^ 40 * 6256085 * 2
def baseEnd_6256085 : Nat := 3212378620383260772366295

theorem tailTrace_6256085 : CollatzResearch.WordTrace tailWord_6256085 prefixEnd_6256085 3212378620383260772366295 := by
  unfold tailWord_6256085
  simp only [CollatzResearch.WordTrace]
  refine ⟨228178165540279974099121709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152118777026853316066081139 228178165540279974099121709)
  ·
    refine ⟨85566812077604990287170641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228178165540279974099121709 85566812077604990287170641)
    ·
      refine ⟨64175109058203742715377981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85566812077604990287170641 64175109058203742715377981)
      ·
        refine ⟨24065665896826403518266743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64175109058203742715377981 24065665896826403518266743)
        ·
          refine ⟨36098498845239605277400115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24065665896826403518266743 36098498845239605277400115)
          ·
            refine ⟨54147748267859407916100173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36098498845239605277400115 54147748267859407916100173)
            ·
              refine ⟨20305405600447277968537565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54147748267859407916100173 20305405600447277968537565)
              ·
                refine ⟨7614527100167729238201587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20305405600447277968537565 7614527100167729238201587)
                ·
                  refine ⟨11421790650251593857302381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7614527100167729238201587 11421790650251593857302381)
                  ·
                    refine ⟨4283171493844347696488393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11421790650251593857302381 4283171493844347696488393)
                    ·
                      refine ⟨3212378620383260772366295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4283171493844347696488393 3212378620383260772366295)
                      ·
                        rfl

theorem cell23_6256085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_6256085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256085 prefixEnd_6256085 := by exact prefixLift 6256085
  have htrace : WordTrace (prefixWord ++ tailWord_6256085) baseStart_6256085 baseEnd_6256085 := by
    simpa [prefixWord, tailWord_6256085, baseEnd_6256085] using wordTrace_append hprefix tailTrace_6256085
  have hstable : (prefixWord ++ tailWord_6256085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256085).length < 2 ^ (prefixWord ++ tailWord_6256085).sum := by decide
  have hdescent : baseEnd_6256085 < baseStart_6256085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256109 : List Nat := [1, 5, 1, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_6256109 : Nat := 118140960795 + 6256109 * 2 ^ 59
def prefixEnd_6256109 : Nat := 4983230072969 + 3 ^ 40 * 6256109 * 2
def baseEnd_6256109 : Nat := 3212390943918968678466185

theorem tailTrace_6256109 : CollatzResearch.WordTrace tailWord_6256109 prefixEnd_6256109 3212390943918968678466185 := by
  unfold tailWord_6256109
  simp only [CollatzResearch.WordTrace]
  refine ⟨228179040892193026197995381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152119360594795350798663587 228179040892193026197995381)
  ·
    refine ⟨21391785083643096206062067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228179040892193026197995381 21391785083643096206062067)
    ·
      refine ⟨32087677625464644309093101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21391785083643096206062067 32087677625464644309093101)
      ·
        refine ⟨12032879109549241615909913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32087677625464644309093101 12032879109549241615909913)
        ·
          refine ⟨9024659332161931211932435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12032879109549241615909913 9024659332161931211932435)
          ·
            refine ⟨13536988998242896817898653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9024659332161931211932435 13536988998242896817898653)
            ·
              refine ⟨5076370874341086306711995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13536988998242896817898653 5076370874341086306711995)
              ·
                refine ⟨7614556311511629460067993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5076370874341086306711995 7614556311511629460067993)
                ·
                  refine ⟨5710917233633722095050995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7614556311511629460067993 5710917233633722095050995)
                  ·
                    refine ⟨8566375850450583142576493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5710917233633722095050995 8566375850450583142576493)
                    ·
                      refine ⟨3212390943918968678466185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8566375850450583142576493 3212390943918968678466185)
                      ·
                        rfl

theorem cell23_6256109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_6256109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256109 prefixEnd_6256109 := by exact prefixLift 6256109
  have htrace : WordTrace (prefixWord ++ tailWord_6256109) baseStart_6256109 baseEnd_6256109 := by
    simpa [prefixWord, tailWord_6256109, baseEnd_6256109] using wordTrace_append hprefix tailTrace_6256109
  have hstable : (prefixWord ++ tailWord_6256109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256109).length < 2 ^ (prefixWord ++ tailWord_6256109).sum := by decide
  have hdescent : baseEnd_6256109 < baseStart_6256109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256111 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 4]
def baseStart_6256111 : Nat := 118140960795 + 6256111 * 2 ^ 59
def prefixEnd_6256111 : Nat := 4983230072969 + 3 ^ 40 * 6256111 * 2
def baseEnd_6256111 : Nat := 3212391970880277670641175

theorem tailTrace_6256111 : CollatzResearch.WordTrace tailWord_6256111 prefixEnd_6256111 3212391970880277670641175 := by
  unfold tailWord_6256111
  simp only [CollatzResearch.WordTrace]
  refine ⟨228179113838185780539568187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152119409225457187026378791 228179113838185780539568187)
  ·
    refine ⟨342268670757278670809352281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228179113838185780539568187 342268670757278670809352281)
    ·
      refine ⟨256701503067959003107014211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342268670757278670809352281 256701503067959003107014211)
      ·
        refine ⟨385052254601938504660521317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256701503067959003107014211 385052254601938504660521317)
        ·
          refine ⟨72197297737863469623847747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 385052254601938504660521317 72197297737863469623847747)
          ·
            refine ⟨108295946606795204435771621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72197297737863469623847747 108295946606795204435771621)
            ·
              refine ⟨20305489988774100831707179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108295946606795204435771621 20305489988774100831707179)
              ·
                refine ⟨30458234983161151247560769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20305489988774100831707179 30458234983161151247560769)
                ·
                  refine ⟨22843676237370863435670577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30458234983161151247560769 22843676237370863435670577)
                  ·
                    refine ⟨17132757178028147576752933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22843676237370863435670577 17132757178028147576752933)
                    ·
                      refine ⟨3212391970880277670641175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17132757178028147576752933 3212391970880277670641175)
                      ·
                        rfl

theorem cell23_6256111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_6256111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256111 prefixEnd_6256111 := by exact prefixLift 6256111
  have htrace : WordTrace (prefixWord ++ tailWord_6256111) baseStart_6256111 baseEnd_6256111 := by
    simpa [prefixWord, tailWord_6256111, baseEnd_6256111] using wordTrace_append hprefix tailTrace_6256111
  have hstable : (prefixWord ++ tailWord_6256111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256111).length < 2 ^ (prefixWord ++ tailWord_6256111).sum := by decide
  have hdescent : baseEnd_6256111 < baseStart_6256111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256131 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 3]
def baseStart_6256131 : Nat := 118140960795 + 6256131 * 2 ^ 59
def prefixEnd_6256131 : Nat := 4983230072969 + 3 ^ 40 * 6256131 * 2
def baseEnd_6256131 : Nat := 3212402240493367592391083

theorem tailTrace_6256131 : CollatzResearch.WordTrace tailWord_6256131 prefixEnd_6256131 3212402240493367592391083 := by
  unfold tailWord_6256131
  simp only [CollatzResearch.WordTrace]
  refine ⟨228179843298113323955296247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152119895532075549303530831 228179843298113323955296247)
  ·
    refine ⟨342269764947169985932944371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228179843298113323955296247 342269764947169985932944371)
    ·
      refine ⟨513404647420754978899416557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342269764947169985932944371 513404647420754978899416557)
      ·
        refine ⟨192526742782783117087281209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 513404647420754978899416557 192526742782783117087281209)
        ·
          refine ⟨144395057087087337815460907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192526742782783117087281209 144395057087087337815460907)
          ·
            refine ⟨216592585630631006723191361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144395057087087337815460907 216592585630631006723191361)
            ·
              refine ⟨162444439222973255042393521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216592585630631006723191361 162444439222973255042393521)
              ·
                refine ⟨121833329417229941281795141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162444439222973255042393521 121833329417229941281795141)
                ·
                  refine ⟨22843749265730613990336589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121833329417229941281795141 22843749265730613990336589)
                  ·
                    refine ⟨8566405974648980246376221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22843749265730613990336589 8566405974648980246376221)
                    ·
                      refine ⟨3212402240493367592391083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8566405974648980246376221 3212402240493367592391083)
                      ·
                        rfl

theorem cell23_6256131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_6256131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256131 prefixEnd_6256131 := by exact prefixLift 6256131
  have htrace : WordTrace (prefixWord ++ tailWord_6256131) baseStart_6256131 baseEnd_6256131 := by
    simpa [prefixWord, tailWord_6256131, baseEnd_6256131] using wordTrace_append hprefix tailTrace_6256131
  have hstable : (prefixWord ++ tailWord_6256131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256131).length < 2 ^ (prefixWord ++ tailWord_6256131).sum := by decide
  have hdescent : baseEnd_6256131 < baseStart_6256131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256161 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_6256161 : Nat := 118140960795 + 6256161 * 2 ^ 59
def prefixEnd_6256161 : Nat := 4983230072969 + 3 ^ 40 * 6256161 * 2
def baseEnd_6256161 : Nat := 3212417644913002475015945

theorem tailTrace_6256161 : CollatzResearch.WordTrace tailWord_6256161 prefixEnd_6256161 3212417644913002475015945 := by
  unfold tailWord_6256161
  simp only [CollatzResearch.WordTrace]
  refine ⟨228180937488004639078888337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152120624992003092719258891 228180937488004639078888337)
  ·
    refine ⟨171135703116003479309166253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228180937488004639078888337 171135703116003479309166253)
    ·
      refine ⟨64175888668501304740937345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171135703116003479309166253 64175888668501304740937345)
      ·
        refine ⟨48131916501375978555703009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64175888668501304740937345 48131916501375978555703009)
        ·
          refine ⟨36098937376031983916777257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48131916501375978555703009 36098937376031983916777257)
          ·
            refine ⟨27074203032023987937582943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36098937376031983916777257 27074203032023987937582943)
            ·
              refine ⟨40611304548035981906374415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27074203032023987937582943 40611304548035981906374415)
              ·
                refine ⟨60916956822053972859561623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40611304548035981906374415 60916956822053972859561623)
                ·
                  refine ⟨91375435233080959289342435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60916956822053972859561623 91375435233080959289342435)
                  ·
                    refine ⟨137063152849621438934013653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91375435233080959289342435 137063152849621438934013653)
                    ·
                      refine ⟨3212417644913002475015945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137063152849621438934013653 3212417644913002475015945)
                      ·
                        rfl

theorem cell23_6256161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_6256161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256161 prefixEnd_6256161 := by exact prefixLift 6256161
  have htrace : WordTrace (prefixWord ++ tailWord_6256161) baseStart_6256161 baseEnd_6256161 := by
    simpa [prefixWord, tailWord_6256161, baseEnd_6256161] using wordTrace_append hprefix tailTrace_6256161
  have hstable : (prefixWord ++ tailWord_6256161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256161).length < 2 ^ (prefixWord ++ tailWord_6256161).sum := by decide
  have hdescent : baseEnd_6256161 < baseStart_6256161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256208 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 3]
def baseStart_6256208 : Nat := 118140960795 + 6256208 * 2 ^ 59
def prefixEnd_6256208 : Nat := 4983230072969 + 3 ^ 40 * 6256208 * 2
def baseEnd_6256208 : Nat := 3212441778503763791128229

theorem tailTrace_6256208 : CollatzResearch.WordTrace tailWord_6256208 prefixEnd_6256208 3212441778503763791128229 := by
  unfold tailWord_6256208
  simp only [CollatzResearch.WordTrace]
  refine ⟨114091325859417183052924639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152121767812556244070566185 114091325859417183052924639)
  ·
    refine ⟨171136988789125774579386959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114091325859417183052924639 171136988789125774579386959)
    ·
      refine ⟨256705483183688661869080439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171136988789125774579386959 256705483183688661869080439)
      ·
        refine ⟨385058224775532992803620659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256705483183688661869080439 385058224775532992803620659)
        ·
          refine ⟨577587337163299489205430989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385058224775532992803620659 577587337163299489205430989)
          ·
            refine ⟨216595251436237308452036621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 577587337163299489205430989 216595251436237308452036621)
            ·
              refine ⟨81223219288588990669513733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216595251436237308452036621 81223219288588990669513733)
              ·
                refine ⟨15229353616610435750533825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81223219288588990669513733 15229353616610435750533825)
                ·
                  refine ⟨11422015212457826812900369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15229353616610435750533825 11422015212457826812900369)
                  ·
                    refine ⟨8566511409343370109675277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11422015212457826812900369 8566511409343370109675277)
                    ·
                      refine ⟨3212441778503763791128229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8566511409343370109675277 3212441778503763791128229)
                      ·
                        rfl

theorem cell23_6256208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 3].length) (baseStart_6256208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256208 prefixEnd_6256208 := by exact prefixLift 6256208
  have htrace : WordTrace (prefixWord ++ tailWord_6256208) baseStart_6256208 baseEnd_6256208 := by
    simpa [prefixWord, tailWord_6256208, baseEnd_6256208] using wordTrace_append hprefix tailTrace_6256208
  have hstable : (prefixWord ++ tailWord_6256208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256208).length < 2 ^ (prefixWord ++ tailWord_6256208).sum := by decide
  have hdescent : baseEnd_6256208 < baseStart_6256208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256228 : List Nat := [2, 3, 1, 1, 2, 3, 2, 3, 6]
def baseStart_6256228 : Nat := 118140960795 + 6256228 * 2 ^ 59
def prefixEnd_6256228 : Nat := 4983230072969 + 3 ^ 40 * 6256228 * 2
def baseEnd_6256228 : Nat := 356939116457428190319793

theorem tailTrace_6256228 : CollatzResearch.WordTrace tailWord_6256228 prefixEnd_6256228 356939116457428190319793 := by
  unfold tailWord_6256228
  simp only [CollatzResearch.WordTrace]
  refine ⟨114091690589380954760788669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152122254119174606347718225 114091690589380954760788669)
  ·
    refine ⟨42784383971017858035295751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114091690589380954760788669 42784383971017858035295751)
    ·
      refine ⟨64176575956526787052943627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42784383971017858035295751 64176575956526787052943627)
      ·
        refine ⟨96264863934790180579415441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64176575956526787052943627 96264863934790180579415441)
        ·
          refine ⟨72198647951092635434561581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96264863934790180579415441 72198647951092635434561581)
          ·
            refine ⟨27074492981659738287960593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72198647951092635434561581 27074492981659738287960593)
            ·
              refine ⟨20305869736244803715970445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27074492981659738287960593 20305869736244803715970445)
              ·
                refine ⟨7614701151091801393488917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20305869736244803715970445 7614701151091801393488917)
                ·
                  refine ⟨356939116457428190319793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7614701151091801393488917 356939116457428190319793)
                  ·
                    rfl

theorem cell23_6256228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_6256228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256228 prefixEnd_6256228 := by exact prefixLift 6256228
  have htrace : WordTrace (prefixWord ++ tailWord_6256228) baseStart_6256228 baseEnd_6256228 := by
    simpa [prefixWord, tailWord_6256228, baseEnd_6256228] using wordTrace_append hprefix tailTrace_6256228
  have hstable : (prefixWord ++ tailWord_6256228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256228).length < 2 ^ (prefixWord ++ tailWord_6256228).sum := by decide
  have hdescent : baseEnd_6256228 < baseStart_6256228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256242 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 2, 2, 3]
def baseStart_6256242 : Nat := 118140960795 + 6256242 * 2 ^ 59
def prefixEnd_6256242 : Nat := 4983230072969 + 3 ^ 40 * 6256242 * 2
def baseEnd_6256242 : Nat := 3212459236846016658103073

theorem tailTrace_6256242 : CollatzResearch.WordTrace tailWord_6256242 prefixEnd_6256242 3212459236846016658103073 := by
  unfold tailWord_6256242
  simp only [CollatzResearch.WordTrace]
  refine ⟨57045972950177797478146745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152122594533807459941724653 57045972950177797478146745)
  ·
    refine ⟨42784479712633348108610059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57045972950177797478146745 42784479712633348108610059)
    ·
      refine ⟨64176719568950022162915089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42784479712633348108610059 64176719568950022162915089)
      ·
        refine ⟨48132539676712516622186317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64176719568950022162915089 48132539676712516622186317)
        ·
          refine ⟨18049702378767193733319869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48132539676712516622186317 18049702378767193733319869)
          ·
            refine ⟨6768638392037697649994951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18049702378767193733319869 6768638392037697649994951)
            ·
              refine ⟨10152957588056546474992427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6768638392037697649994951 10152957588056546474992427)
              ·
                refine ⟨15229436382084819712488641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10152957588056546474992427 15229436382084819712488641)
                ·
                  refine ⟨11422077286563614784366481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15229436382084819712488641 11422077286563614784366481)
                  ·
                    refine ⟨8566557964922711088274861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11422077286563614784366481 8566557964922711088274861)
                    ·
                      refine ⟨3212459236846016658103073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8566557964922711088274861 3212459236846016658103073)
                      ·
                        rfl

theorem cell23_6256242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_6256242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256242 prefixEnd_6256242 := by exact prefixLift 6256242
  have htrace : WordTrace (prefixWord ++ tailWord_6256242) baseStart_6256242 baseEnd_6256242 := by
    simpa [prefixWord, tailWord_6256242, baseEnd_6256242] using wordTrace_append hprefix tailTrace_6256242
  have hstable : (prefixWord ++ tailWord_6256242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256242).length < 2 ^ (prefixWord ++ tailWord_6256242).sum := by decide
  have hdescent : baseEnd_6256242 < baseStart_6256242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256265 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 2, 3, 2]
def baseStart_6256265 : Nat := 118140960795 + 6256265 * 2 ^ 59
def prefixEnd_6256265 : Nat := 4983230072969 + 3 ^ 40 * 6256265 * 2
def baseEnd_6256265 : Nat := 3212471046901070068115467

theorem tailTrace_6256265 : CollatzResearch.WordTrace tailWord_6256265 prefixEnd_6256265 3212471046901070068115467 := by
  unfold tailWord_6256265
  simp only [CollatzResearch.WordTrace]
  refine ⟨228184730679627864840674249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152123153786418576560449499 228184730679627864840674249)
  ·
    refine ⟨171138548009720898630505687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228184730679627864840674249 171138548009720898630505687)
    ·
      refine ⟨256707822014581347945758531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171138548009720898630505687 256707822014581347945758531)
      ·
        refine ⟨385061733021872021918637797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256707822014581347945758531 385061733021872021918637797)
        ·
          refine ⟨72199074941601004109744587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 385061733021872021918637797 72199074941601004109744587)
          ·
            refine ⟨108298612412401506164616881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72199074941601004109744587 108298612412401506164616881)
            ·
              refine ⟨81223959309301129623462661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108298612412401506164616881 81223959309301129623462661)
              ·
                refine ⟨15229492370493961804399249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81223959309301129623462661 15229492370493961804399249)
                ·
                  refine ⟨11422119277870471353299437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15229492370493961804399249 11422119277870471353299437)
                  ·
                    refine ⟨4283294729201426757487289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11422119277870471353299437 4283294729201426757487289)
                    ·
                      refine ⟨3212471046901070068115467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4283294729201426757487289 3212471046901070068115467)
                      ·
                        rfl

theorem cell23_6256265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 3, 2].length) (baseStart_6256265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256265 prefixEnd_6256265 := by exact prefixLift 6256265
  have htrace : WordTrace (prefixWord ++ tailWord_6256265) baseStart_6256265 baseEnd_6256265 := by
    simpa [prefixWord, tailWord_6256265, baseEnd_6256265] using wordTrace_append hprefix tailTrace_6256265
  have hstable : (prefixWord ++ tailWord_6256265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256265).length < 2 ^ (prefixWord ++ tailWord_6256265).sum := by decide
  have hdescent : baseEnd_6256265 < baseStart_6256265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256318 : List Nat := [4, 2, 1, 1, 2, 2, 11]
def baseStart_6256318 : Nat := 118140960795 + 6256318 * 2 ^ 59
def prefixEnd_6256318 : Nat := 4983230072969 + 3 ^ 40 * 6256318 * 2
def baseEnd_6256318 : Nat := 39660472362663683466083

theorem tailTrace_6256318 : CollatzResearch.WordTrace tailWord_6256318 prefixEnd_6256318 39660472362663683466083 := by
  unfold tailWord_6256318
  simp only [CollatzResearch.WordTrace]
  refine ⟨28523332968554481861544201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152124442498957236594902405 28523332968554481861544201)
  ·
    refine ⟨21392499726415861396158151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28523332968554481861544201 21392499726415861396158151)
    ·
      refine ⟨32088749589623792094237227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21392499726415861396158151 32088749589623792094237227)
      ·
        refine ⟨48133124384435688141355841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32088749589623792094237227 48133124384435688141355841)
        ·
          refine ⟨36099843288326766106016881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48133124384435688141355841 36099843288326766106016881)
          ·
            refine ⟨27074882466245074579512661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36099843288326766106016881 27074882466245074579512661)
            ·
              refine ⟨39660472362663683466083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27074882466245074579512661 39660472362663683466083)
              ·
                rfl

theorem cell23_6256318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 11].length) (baseStart_6256318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256318 prefixEnd_6256318 := by exact prefixLift 6256318
  have htrace : WordTrace (prefixWord ++ tailWord_6256318) baseStart_6256318 baseEnd_6256318 := by
    simpa [prefixWord, tailWord_6256318, baseEnd_6256318] using wordTrace_append hprefix tailTrace_6256318
  have hstable : (prefixWord ++ tailWord_6256318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256318).length < 2 ^ (prefixWord ++ tailWord_6256318).sum := by decide
  have hdescent : baseEnd_6256318 < baseStart_6256318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256349 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_6256349 : Nat := 118140960795 + 6256349 * 2 ^ 59
def prefixEnd_6256349 : Nat := 4983230072969 + 3 ^ 40 * 6256349 * 2
def baseEnd_6256349 : Nat := 3212514179276047739465081

theorem tailTrace_6256349 : CollatzResearch.WordTrace tailWord_6256349 prefixEnd_6256349 3212514179276047739465081 := by
  unfold tailWord_6256349
  simp only [CollatzResearch.WordTrace]
  refine ⟨228187794411323547186732101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152125196274215698124488067 228187794411323547186732101)
  ·
    refine ⟨42785211452123165097512269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228187794411323547186732101 42785211452123165097512269)
    ·
      refine ⟨16044454294546186911567101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42785211452123165097512269 16044454294546186911567101)
      ·
        refine ⟨6016670360454820091837663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16044454294546186911567101 6016670360454820091837663)
        ·
          refine ⟨9025005540682230137756495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6016670360454820091837663 9025005540682230137756495)
          ·
            refine ⟨13537508311023345206634743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9025005540682230137756495 13537508311023345206634743)
            ·
              refine ⟨20306262466535017809952115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13537508311023345206634743 20306262466535017809952115)
              ·
                refine ⟨30459393699802526714928173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20306262466535017809952115 30459393699802526714928173)
                ·
                  refine ⟨11422272637425947518098065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30459393699802526714928173 11422272637425947518098065)
                  ·
                    refine ⟨8566704478069460638573549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11422272637425947518098065 8566704478069460638573549)
                    ·
                      refine ⟨3212514179276047739465081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8566704478069460638573549 3212514179276047739465081)
                      ·
                        rfl

theorem cell23_6256349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_6256349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256349 prefixEnd_6256349 := by exact prefixLift 6256349
  have htrace : WordTrace (prefixWord ++ tailWord_6256349) baseStart_6256349 baseEnd_6256349 := by
    simpa [prefixWord, tailWord_6256349, baseEnd_6256349] using wordTrace_append hprefix tailTrace_6256349
  have hstable : (prefixWord ++ tailWord_6256349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256349).length < 2 ^ (prefixWord ++ tailWord_6256349).sum := by decide
  have hdescent : baseEnd_6256349 < baseStart_6256349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256378 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 2, 6]
def baseStart_6256378 : Nat := 118140960795 + 6256378 * 2 ^ 59
def prefixEnd_6256378 : Nat := 4983230072969 + 3 ^ 40 * 6256378 * 2
def baseEnd_6256378 : Nat := 1070843023405009375334149

theorem tailTrace_6256378 : CollatzResearch.WordTrace tailWord_6256378 prefixEnd_6256378 1070843023405009375334149 := by
  unfold tailWord_6256378
  simp only [CollatzResearch.WordTrace]
  refine ⟨57047213032054621284884447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152125901418812323426358525 57047213032054621284884447)
  ·
    refine ⟨85570819548081931927326671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57047213032054621284884447 85570819548081931927326671)
    ·
      refine ⟨128356229322122897890990007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85570819548081931927326671 128356229322122897890990007)
      ·
        refine ⟨192534343983184346836485011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128356229322122897890990007 192534343983184346836485011)
        ·
          refine ⟨288801515974776520254727517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192534343983184346836485011 288801515974776520254727517)
          ·
            refine ⟨108300568490541195095522819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288801515974776520254727517 108300568490541195095522819)
            ·
              refine ⟨162450852735811792643284229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108300568490541195095522819 162450852735811792643284229)
              ·
                refine ⟨30459534887964711120615793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162450852735811792643284229 30459534887964711120615793)
                ·
                  refine ⟨22844651165973533340461845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30459534887964711120615793 22844651165973533340461845)
                  ·
                    refine ⟨1070843023405009375334149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22844651165973533340461845 1070843023405009375334149)
                    ·
                      rfl

theorem cell23_6256378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_6256378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256378 prefixEnd_6256378 := by exact prefixLift 6256378
  have htrace : WordTrace (prefixWord ++ tailWord_6256378) baseStart_6256378 baseEnd_6256378 := by
    simpa [prefixWord, tailWord_6256378, baseEnd_6256378] using wordTrace_append hprefix tailTrace_6256378
  have hstable : (prefixWord ++ tailWord_6256378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256378).length < 2 ^ (prefixWord ++ tailWord_6256378).sum := by decide
  have hdescent : baseEnd_6256378 < baseStart_6256378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256408 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 9]
def baseStart_6256408 : Nat := 118140960795 + 6256408 * 2 ^ 59
def prefixEnd_6256408 : Nat := 4983230072969 + 3 ^ 40 * 6256408 * 2
def baseEnd_6256408 : Nat := 356949386070518112069701

theorem tailTrace_6256408 : CollatzResearch.WordTrace tailWord_6256408 prefixEnd_6256408 356949386070518112069701 := by
  unfold tailWord_6256408
  simp only [CollatzResearch.WordTrace]
  refine ⟨114094973159054900131564939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152126630878739866842086585 114094973159054900131564939)
  ·
    refine ⟨171142459738582350197347409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114094973159054900131564939 171142459738582350197347409)
    ·
      refine ⟨128356844803936762648010557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171142459738582350197347409 128356844803936762648010557)
      ·
        refine ⟨48133816801476285993003959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128356844803936762648010557 48133816801476285993003959)
        ·
          refine ⟨72200725202214428989505939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48133816801476285993003959 72200725202214428989505939)
          ·
            refine ⟨108301087803321643484258909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72200725202214428989505939 108301087803321643484258909)
            ·
              refine ⟨40612907926245616306597091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108301087803321643484258909 40612907926245616306597091)
              ·
                refine ⟨60919361889368424459895637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40612907926245616306597091 60919361889368424459895637)
                ·
                  refine ⟨356949386070518112069701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60919361889368424459895637 356949386070518112069701)
                  ·
                    rfl

theorem cell23_6256408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 9].length) (baseStart_6256408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256408 prefixEnd_6256408 := by exact prefixLift 6256408
  have htrace : WordTrace (prefixWord ++ tailWord_6256408) baseStart_6256408 baseEnd_6256408 := by
    simpa [prefixWord, tailWord_6256408, baseEnd_6256408] using wordTrace_append hprefix tailTrace_6256408
  have hstable : (prefixWord ++ tailWord_6256408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256408).length < 2 ^ (prefixWord ++ tailWord_6256408).sum := by decide
  have hdescent : baseEnd_6256408 < baseStart_6256408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256436 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_6256436 : Nat := 118140960795 + 6256436 * 2 ^ 59
def prefixEnd_6256436 : Nat := 4983230072969 + 3 ^ 40 * 6256436 * 2
def baseEnd_6256436 : Nat := 3212558852092988899077181

theorem tailTrace_6256436 : CollatzResearch.WordTrace tailWord_6256436 prefixEnd_6256436 3212558852092988899077181 := by
  unfold tailWord_6256436
  simp only [CollatzResearch.WordTrace]
  refine ⟨114095483781004180522574581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152127311708005574030099441 114095483781004180522574581)
  ·
    refine ⟨10696451604469141923991367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114095483781004180522574581 10696451604469141923991367)
    ·
      refine ⟨16044677406703712885987051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10696451604469141923991367 16044677406703712885987051)
      ·
        refine ⟨24067016110055569328980577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16044677406703712885987051 24067016110055569328980577)
        ·
          refine ⟨18050262082541676996735433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24067016110055569328980577 18050262082541676996735433)
          ·
            refine ⟨13537696561906257747551575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18050262082541676996735433 13537696561906257747551575)
            ·
              refine ⟨20306544842859386621327363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13537696561906257747551575 20306544842859386621327363)
              ·
                refine ⟨30459817264289079931991045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20306544842859386621327363 30459817264289079931991045)
                ·
                  refine ⟨5711215737054202487248321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30459817264289079931991045 5711215737054202487248321)
                  ·
                    refine ⟨4283411802790651865436241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5711215737054202487248321 4283411802790651865436241)
                    ·
                      refine ⟨3212558852092988899077181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4283411802790651865436241 3212558852092988899077181)
                      ·
                        rfl

theorem cell23_6256436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_6256436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256436 prefixEnd_6256436 := by exact prefixLift 6256436
  have htrace : WordTrace (prefixWord ++ tailWord_6256436) baseStart_6256436 baseEnd_6256436 := by
    simpa [prefixWord, tailWord_6256436, baseEnd_6256436] using wordTrace_append hprefix tailTrace_6256436
  have hstable : (prefixWord ++ tailWord_6256436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256436).length < 2 ^ (prefixWord ++ tailWord_6256436).sum := by decide
  have hdescent : baseEnd_6256436 < baseStart_6256436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256442 : List Nat := [3, 1, 1, 1, 5, 1, 2, 4, 5]
def baseStart_6256442 : Nat := 118140960795 + 6256442 * 2 ^ 59
def prefixEnd_6256442 : Nat := 4983230072969 + 3 ^ 40 * 6256442 * 2
def baseEnd_6256442 : Nat := 356951325886323986178017

theorem tailTrace_6256442 : CollatzResearch.WordTrace tailWord_6256442 prefixEnd_6256442 356951325886323986178017 := by
  unfold tailWord_6256442
  simp only [CollatzResearch.WordTrace]
  refine ⟨57047796599996656017466895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152127457599991082713245053 57047796599996656017466895)
  ·
    refine ⟨85571694899994984026200343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57047796599996656017466895 85571694899994984026200343)
    ·
      refine ⟨128357542349992476039300515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85571694899994984026200343 128357542349992476039300515)
      ·
        refine ⟨192536313524988714058950773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128357542349992476039300515 192536313524988714058950773)
        ·
          refine ⟨18050279392967691943026635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192536313524988714058950773 18050279392967691943026635)
          ·
            refine ⟨27075419089451537914539953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18050279392967691943026635 27075419089451537914539953)
            ·
              refine ⟨20306564317088653435904965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27075419089451537914539953 20306564317088653435904965)
              ·
                refine ⟨3807480809454122519232181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20306564317088653435904965 3807480809454122519232181)
                ·
                  refine ⟨356951325886323986178017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3807480809454122519232181 356951325886323986178017)
                  ·
                    rfl

theorem cell23_6256442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 5].length) (baseStart_6256442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256442 prefixEnd_6256442 := by exact prefixLift 6256442
  have htrace : WordTrace (prefixWord ++ tailWord_6256442) baseStart_6256442 baseEnd_6256442 := by
    simpa [prefixWord, tailWord_6256442, baseEnd_6256442] using wordTrace_append hprefix tailTrace_6256442
  have hstable : (prefixWord ++ tailWord_6256442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256442).length < 2 ^ (prefixWord ++ tailWord_6256442).sum := by decide
  have hdescent : baseEnd_6256442 < baseStart_6256442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256476 : List Nat := [2, 2, 4, 2, 2, 2, 1, 3, 5]
def baseStart_6256476 : Nat := 118140960795 + 6256476 * 2 ^ 59
def prefixEnd_6256476 : Nat := 4983230072969 + 3 ^ 40 * 6256476 * 2
def baseEnd_6256476 : Nat := 356953265702129860286333

theorem tailTrace_6256476 : CollatzResearch.WordTrace tailWord_6256476 prefixEnd_6256476 356953265702129860286333 := by
  unfold tailWord_6256476
  simp only [CollatzResearch.WordTrace]
  refine ⟨114096213240931723938302641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152128284321242298584403521 114096213240931723938302641)
  ·
    refine ⟨85572159930698792953726981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114096213240931723938302641 85572159930698792953726981)
    ·
      refine ⟨16044779987006023678823809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85572159930698792953726981 16044779987006023678823809)
      ·
        refine ⟨12033584990254517759117857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16044779987006023678823809 12033584990254517759117857)
        ·
          refine ⟨9025188742690888319338393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12033584990254517759117857 9025188742690888319338393)
          ·
            refine ⟨6768891557018166239503795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9025188742690888319338393 6768891557018166239503795)
            ·
              refine ⟨10153337335527249359255693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6768891557018166239503795 10153337335527249359255693)
              ·
                refine ⟨3807501500822718509720885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10153337335527249359255693 3807501500822718509720885)
                ·
                  refine ⟨356953265702129860286333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3807501500822718509720885 356953265702129860286333)
                  ·
                    rfl

theorem cell23_6256476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 5].length) (baseStart_6256476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256476 prefixEnd_6256476 := by exact prefixLift 6256476
  have htrace : WordTrace (prefixWord ++ tailWord_6256476) baseStart_6256476 baseEnd_6256476 := by
    simpa [prefixWord, tailWord_6256476, baseEnd_6256476] using wordTrace_append hprefix tailTrace_6256476
  have hstable : (prefixWord ++ tailWord_6256476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256476).length < 2 ^ (prefixWord ++ tailWord_6256476).sum := by decide
  have hdescent : baseEnd_6256476 < baseStart_6256476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256492 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 4]
def baseStart_6256492 : Nat := 118140960795 + 6256492 * 2 ^ 59
def prefixEnd_6256492 : Nat := 4983230072969 + 3 ^ 40 * 6256492 * 2
def baseEnd_6256492 : Nat := 3212587607009640679976923

theorem tailTrace_6256492 : CollatzResearch.WordTrace tailWord_6256492 prefixEnd_6256492 3212587607009640679976923 := by
  unfold tailWord_6256492
  simp only [CollatzResearch.WordTrace]
  refine ⟨114096505024902741304593865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152128673366536988406125153 114096505024902741304593865)
  ·
    refine ⟨85572378768677055978445399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114096505024902741304593865 85572378768677055978445399)
    ·
      refine ⟨128358568153015583967668099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85572378768677055978445399 128358568153015583967668099)
      ·
        refine ⟨192537852229523375951502149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128358568153015583967668099 192537852229523375951502149)
        ·
          refine ⟨36100847293035632990906653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192537852229523375951502149 36100847293035632990906653)
          ·
            refine ⟨13537817734888362371589995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36100847293035632990906653 13537817734888362371589995)
            ·
              refine ⟨20306726602332543557384993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13537817734888362371589995 20306726602332543557384993)
              ·
                refine ⟨15230044951749407668038745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20306726602332543557384993 15230044951749407668038745)
                ·
                  refine ⟨11422533713812055751029059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15230044951749407668038745 11422533713812055751029059)
                  ·
                    refine ⟨17133800570718083626543589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11422533713812055751029059 17133800570718083626543589)
                    ·
                      refine ⟨3212587607009640679976923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17133800570718083626543589 3212587607009640679976923)
                      ·
                        rfl

theorem cell23_6256492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_6256492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256492 prefixEnd_6256492 := by exact prefixLift 6256492
  have htrace : WordTrace (prefixWord ++ tailWord_6256492) baseStart_6256492 baseEnd_6256492 := by
    simpa [prefixWord, tailWord_6256492, baseEnd_6256492] using wordTrace_append hprefix tailTrace_6256492
  have hstable : (prefixWord ++ tailWord_6256492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256492).length < 2 ^ (prefixWord ++ tailWord_6256492).sum := by decide
  have hdescent : baseEnd_6256492 < baseStart_6256492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256526 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6256526 : Nat := 118140960795 + 6256526 * 2 ^ 59
def prefixEnd_6256526 : Nat := 4983230072969 + 3 ^ 40 * 6256526 * 2
def baseEnd_6256526 : Nat := 3212605065351893546951767

theorem tailTrace_6256526 : CollatzResearch.WordTrace tailWord_6256526 prefixEnd_6256526 3212605065351893546951767 := by
  unfold tailWord_6256526
  simp only [CollatzResearch.WordTrace]
  refine ⟨28524281266460288301990679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152129500087788204277283621 28524281266460288301990679)
  ·
    refine ⟨42786421899690432452986019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28524281266460288301990679 42786421899690432452986019)
    ·
      refine ⟨64179632849535648679479029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42786421899690432452986019 64179632849535648679479029)
      ·
        refine ⟨6016840579643967063701159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64179632849535648679479029 6016840579643967063701159)
        ·
          refine ⟨9025260869465950595551739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6016840579643967063701159 9025260869465950595551739)
          ·
            refine ⟨13537891304198925893327609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9025260869465950595551739 13537891304198925893327609)
            ·
              refine ⟨10153418478149194419995707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13537891304198925893327609 10153418478149194419995707)
              ·
                refine ⟨15230127717223791629993561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10153418478149194419995707 15230127717223791629993561)
                ·
                  refine ⟨11422595787917843722495171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15230127717223791629993561 11422595787917843722495171)
                  ·
                    refine ⟨17133893681876765583742757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11422595787917843722495171 17133893681876765583742757)
                    ·
                      refine ⟨3212605065351893546951767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17133893681876765583742757 3212605065351893546951767)
                      ·
                        rfl

theorem cell23_6256526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6256526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256526 prefixEnd_6256526 := by exact prefixLift 6256526
  have htrace : WordTrace (prefixWord ++ tailWord_6256526) baseStart_6256526 baseEnd_6256526 := by
    simpa [prefixWord, tailWord_6256526, baseEnd_6256526] using wordTrace_append hprefix tailTrace_6256526
  have hstable : (prefixWord ++ tailWord_6256526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256526).length < 2 ^ (prefixWord ++ tailWord_6256526).sum := by decide
  have hdescent : baseEnd_6256526 < baseStart_6256526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256585 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 3, 1, 5]
def baseStart_6256585 : Nat := 118140960795 + 6256585 * 2 ^ 59
def prefixEnd_6256585 : Nat := 4983230072969 + 3 ^ 40 * 6256585 * 2
def baseEnd_6256585 : Nat := 3212635360710508816113995

theorem tailTrace_6256585 : CollatzResearch.WordTrace tailWord_6256585 prefixEnd_6256585 3212635360710508816113995 := by
  unfold tailWord_6256585
  simp only [CollatzResearch.WordTrace]
  refine ⟨228196402038468559492323209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152130934692312372994882139 228196402038468559492323209)
  ·
    refine ⟨171147301528851419619242407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228196402038468559492323209 171147301528851419619242407)
    ·
      refine ⟨256720952293277129428863611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171147301528851419619242407 256720952293277129428863611)
      ·
        refine ⟨385081428439915694143295417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256720952293277129428863611 385081428439915694143295417)
        ·
          refine ⟨288811071329936770607471563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385081428439915694143295417 288811071329936770607471563)
          ·
            refine ⟨433216606994905155911207345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288811071329936770607471563 433216606994905155911207345)
            ·
              refine ⟨324912455246178866933405509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433216606994905155911207345 324912455246178866933405509)
              ·
                refine ⟨60921085358658537550013533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324912455246178866933405509 60921085358658537550013533)
                ·
                  refine ⟨22845407009496951581255075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60921085358658537550013533 22845407009496951581255075)
                  ·
                    refine ⟨34268110514245427371882613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22845407009496951581255075 34268110514245427371882613)
                    ·
                      refine ⟨3212635360710508816113995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34268110514245427371882613 3212635360710508816113995)
                      ·
                        rfl

theorem cell23_6256585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_6256585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256585 prefixEnd_6256585 := by exact prefixLift 6256585
  have htrace : WordTrace (prefixWord ++ tailWord_6256585) baseStart_6256585 baseEnd_6256585 := by
    simpa [prefixWord, tailWord_6256585, baseEnd_6256585] using wordTrace_append hprefix tailTrace_6256585
  have hstable : (prefixWord ++ tailWord_6256585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256585).length < 2 ^ (prefixWord ++ tailWord_6256585).sum := by decide
  have hdescent : baseEnd_6256585 < baseStart_6256585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256599 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 5, 2, 2]
def baseStart_6256599 : Nat := 118140960795 + 6256599 * 2 ^ 59
def prefixEnd_6256599 : Nat := 4983230072969 + 3 ^ 40 * 6256599 * 2
def baseEnd_6256599 : Nat := 3212642549439671761338931

theorem tailTrace_6256599 : CollatzResearch.WordTrace tailWord_6256599 prefixEnd_6256599 3212642549439671761338931 := by
  unfold tailWord_6256599
  simp only [CollatzResearch.WordTrace]
  refine ⟨228196912660417839883332851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152131275106945226588888567 228196912660417839883332851)
  ·
    refine ⟨342295368990626759824999277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228196912660417839883332851 342295368990626759824999277)
    ·
      refine ⟨128360763371485034934374729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342295368990626759824999277 128360763371485034934374729)
      ·
        refine ⟨96270572528613776200781047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128360763371485034934374729 96270572528613776200781047)
        ·
          refine ⟨144405858792920664301171571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96270572528613776200781047 144405858792920664301171571)
          ·
            refine ⟨216608788189380996451757357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144405858792920664301171571 216608788189380996451757357)
            ·
              refine ⟨81228295571017873669409009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216608788189380996451757357 81228295571017873669409009)
              ·
                refine ⟨60921221678263405252056757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81228295571017873669409009 60921221678263405252056757)
                ·
                  refine ⟨5711364532337194242380321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60921221678263405252056757 5711364532337194242380321)
                  ·
                    refine ⟨4283523399252895681785241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5711364532337194242380321 4283523399252895681785241)
                    ·
                      refine ⟨3212642549439671761338931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4283523399252895681785241 3212642549439671761338931)
                      ·
                        rfl

theorem cell23_6256599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_6256599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256599 prefixEnd_6256599 := by exact prefixLift 6256599
  have htrace : WordTrace (prefixWord ++ tailWord_6256599) baseStart_6256599 baseEnd_6256599 := by
    simpa [prefixWord, tailWord_6256599, baseEnd_6256599] using wordTrace_append hprefix tailTrace_6256599
  have hstable : (prefixWord ++ tailWord_6256599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256599).length < 2 ^ (prefixWord ++ tailWord_6256599).sum := by decide
  have hdescent : baseEnd_6256599 < baseStart_6256599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256609 : List Nat := [1, 2, 3, 1, 2, 1, 5, 2, 2, 4]
def baseStart_6256609 : Nat := 118140960795 + 6256609 * 2 ^ 59
def prefixEnd_6256609 : Nat := 4983230072969 + 3 ^ 40 * 6256609 * 2
def baseEnd_6256609 : Nat := 1070882561415405574071295

theorem tailTrace_6256609 : CollatzResearch.WordTrace tailWord_6256609 prefixEnd_6256609 1070882561415405574071295 := by
  unfold tailWord_6256609
  simp only [CollatzResearch.WordTrace]
  refine ⟨228197277390381611591196881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152131518260254407727464587 228197277390381611591196881)
  ·
    refine ⟨171147958042786208693397661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228197277390381611591196881 171147958042786208693397661)
    ·
      refine ⟨64180484266044828260024123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171147958042786208693397661 64180484266044828260024123)
      ·
        refine ⟨96270726399067242390036185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64180484266044828260024123 96270726399067242390036185)
        ·
          refine ⟨72203044799300431792527139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96270726399067242390036185 72203044799300431792527139)
          ·
            refine ⟨108304567198950647688790709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72203044799300431792527139 108304567198950647688790709)
            ·
              refine ⟨10153553174901623220824129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108304567198950647688790709 10153553174901623220824129)
              ·
                refine ⟨7615164881176217415618097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10153553174901623220824129 7615164881176217415618097)
                ·
                  refine ⟨5711373660882163061713573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7615164881176217415618097 5711373660882163061713573)
                  ·
                    refine ⟨1070882561415405574071295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5711373660882163061713573 1070882561415405574071295)
                    ·
                      rfl

theorem cell23_6256609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_6256609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256609 prefixEnd_6256609 := by exact prefixLift 6256609
  have htrace : WordTrace (prefixWord ++ tailWord_6256609) baseStart_6256609 baseEnd_6256609 := by
    simpa [prefixWord, tailWord_6256609, baseEnd_6256609] using wordTrace_append hprefix tailTrace_6256609
  have hstable : (prefixWord ++ tailWord_6256609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256609).length < 2 ^ (prefixWord ++ tailWord_6256609).sum := by decide
  have hdescent : baseEnd_6256609 < baseStart_6256609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256635 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 2, 7]
def baseStart_6256635 : Nat := 118140960795 + 6256635 * 2 ^ 59
def prefixEnd_6256635 : Nat := 4983230072969 + 3 ^ 40 * 6256635 * 2
def baseEnd_6256635 : Nat := 1070887011581077873496255

theorem tailTrace_6256635 : CollatzResearch.WordTrace tailWord_6256635 prefixEnd_6256635 1070887011581077873496255 := by
  unfold tailWord_6256635
  simp only [CollatzResearch.WordTrace]
  refine ⟨228198225688287418031643359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152132150458858278687762239 228198225688287418031643359)
  ·
    refine ⟨342297338532431127047465039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228198225688287418031643359 342297338532431127047465039)
    ·
      refine ⟨513446007798646690571197559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342297338532431127047465039 513446007798646690571197559)
      ·
        refine ⟨770169011697970035856796339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513446007798646690571197559 770169011697970035856796339)
        ·
          refine ⟨1155253517546955053785194509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770169011697970035856796339 1155253517546955053785194509)
          ·
            refine ⟨433220069080108145169447941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1155253517546955053785194509 433220069080108145169447941)
            ·
              refine ⟨81228762952520277219271489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 433220069080108145169447941 81228762952520277219271489)
              ·
                refine ⟨60921572214390207914453617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81228762952520277219271489 60921572214390207914453617)
                ·
                  refine ⟨45691179160792655935840213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60921572214390207914453617 45691179160792655935840213)
                  ·
                    refine ⟨1070887011581077873496255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45691179160792655935840213 1070887011581077873496255)
                    ·
                      rfl

theorem cell23_6256635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 7].length) (baseStart_6256635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256635 prefixEnd_6256635 := by exact prefixLift 6256635
  have htrace : WordTrace (prefixWord ++ tailWord_6256635) baseStart_6256635 baseEnd_6256635 := by
    simpa [prefixWord, tailWord_6256635, baseEnd_6256635] using wordTrace_append hprefix tailTrace_6256635
  have hstable : (prefixWord ++ tailWord_6256635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256635).length < 2 ^ (prefixWord ++ tailWord_6256635).sum := by decide
  have hdescent : baseEnd_6256635 < baseStart_6256635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256729 : List Nat := [1, 2, 1, 2, 2, 1, 5, 4, 5]
def baseStart_6256729 : Nat := 118140960795 + 6256729 * 2 ^ 59
def prefixEnd_6256729 : Nat := 4983230072969 + 3 ^ 40 * 6256729 * 2
def baseEnd_6256729 : Nat := 356967700213861805857037

theorem tailTrace_6256729 : CollatzResearch.WordTrace tailWord_6256729 prefixEnd_6256729 356967700213861805857037 := by
  unfold tailWord_6256729
  simp only [CollatzResearch.WordTrace]
  refine ⟨228201654149946872085565241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152134436099964581390376827 228201654149946872085565241)
  ·
    refine ⟨171151240612460154064173931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228201654149946872085565241 171151240612460154064173931)
    ·
      refine ⟨256726860918690231096260897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171151240612460154064173931 256726860918690231096260897)
      ·
        refine ⟨192545145689017673322195673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256726860918690231096260897 192545145689017673322195673)
        ·
          refine ⟨144408859266763254991646755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192545145689017673322195673 144408859266763254991646755)
          ·
            refine ⟨216613288900144882487470133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144408859266763254991646755 216613288900144882487470133)
            ·
              refine ⟨20307495834388582733200325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216613288900144882487470133 20307495834388582733200325)
              ·
                refine ⟨3807655468947859262475061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20307495834388582733200325 3807655468947859262475061)
                ·
                  refine ⟨356967700213861805857037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3807655468947859262475061 356967700213861805857037)
                  ·
                    rfl

theorem cell23_6256729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 5].length) (baseStart_6256729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256729 prefixEnd_6256729 := by exact prefixLift 6256729
  have htrace : WordTrace (prefixWord ++ tailWord_6256729) baseStart_6256729 baseEnd_6256729 := by
    simpa [prefixWord, tailWord_6256729, baseEnd_6256729] using wordTrace_append hprefix tailTrace_6256729
  have hstable : (prefixWord ++ tailWord_6256729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256729).length < 2 ^ (prefixWord ++ tailWord_6256729).sum := by decide
  have hdescent : baseEnd_6256729 < baseStart_6256729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256759 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 2, 5]
def baseStart_6256759 : Nat := 118140960795 + 6256759 * 2 ^ 59
def prefixEnd_6256759 : Nat := 4983230072969 + 3 ^ 40 * 6256759 * 2
def baseEnd_6256759 : Nat := 1070908235448130378446065

theorem tailTrace_6256759 : CollatzResearch.WordTrace tailWord_6256759 prefixEnd_6256759 1070908235448130378446065 := by
  unfold tailWord_6256759
  simp only [CollatzResearch.WordTrace]
  refine ⟨228202748339838187209157331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152135165559892124806104887 228202748339838187209157331)
  ·
    refine ⟨342304122509757280813735997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228202748339838187209157331 342304122509757280813735997)
    ·
      refine ⟨128364045941158980305150999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342304122509757280813735997 128364045941158980305150999)
      ·
        refine ⟨192546068911738470457726499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128364045941158980305150999 192546068911738470457726499)
        ·
          refine ⟨288819103367607705686589749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192546068911738470457726499 288819103367607705686589749)
          ·
            refine ⟨27076790940713222408117789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 288819103367607705686589749 27076790940713222408117789)
            ·
              refine ⟨10153796602767458403044171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27076790940713222408117789 10153796602767458403044171)
              ·
                refine ⟨15230694904151187604566257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10153796602767458403044171 15230694904151187604566257)
                ·
                  refine ⟨11423021178113390703424693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15230694904151187604566257 11423021178113390703424693)
                  ·
                    refine ⟨1070908235448130378446065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11423021178113390703424693 1070908235448130378446065)
                    ·
                      rfl

theorem cell23_6256759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_6256759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256759 prefixEnd_6256759 := by exact prefixLift 6256759
  have htrace : WordTrace (prefixWord ++ tailWord_6256759) baseStart_6256759 baseEnd_6256759 := by
    simpa [prefixWord, tailWord_6256759, baseEnd_6256759] using wordTrace_append hprefix tailTrace_6256759
  have hstable : (prefixWord ++ tailWord_6256759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256759).length < 2 ^ (prefixWord ++ tailWord_6256759).sum := by decide
  have hdescent : baseEnd_6256759 < baseStart_6256759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256796 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_6256796 : Nat := 118140960795 + 6256796 * 2 ^ 59
def prefixEnd_6256796 : Nat := 4983230072969 + 3 ^ 40 * 6256796 * 2
def baseEnd_6256796 : Nat := 3212743705128607490575525

theorem tailTrace_6256796 : CollatzResearch.WordTrace tailWord_6256796 prefixEnd_6256796 3212743705128607490575525 := by
  unfold tailWord_6256796
  simp only [CollatzResearch.WordTrace]
  refine ⟨114102048920352071264127121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152136065227136095018836161 114102048920352071264127121)
  ·
    refine ⟨85576536690264053448095341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114102048920352071264127121 85576536690264053448095341)
    ·
      refine ⟨32091201258849020043035753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85576536690264053448095341 32091201258849020043035753)
      ·
        refine ⟨24068400944136765032276815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32091201258849020043035753 24068400944136765032276815)
        ·
          refine ⟨36102601416205147548415223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24068400944136765032276815 36102601416205147548415223)
          ·
            refine ⟨54153902124307721322622835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36102601416205147548415223 54153902124307721322622835)
            ·
              refine ⟨81230853186461581983934253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54153902124307721322622835 81230853186461581983934253)
              ·
                refine ⟨30461569944923093243975345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81230853186461581983934253 30461569944923093243975345)
                ·
                  refine ⟨22846177458692319932981509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30461569944923093243975345 22846177458692319932981509)
                  ·
                    refine ⟨4283658273504809987434033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22846177458692319932981509 4283658273504809987434033)
                    ·
                      refine ⟨3212743705128607490575525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4283658273504809987434033 3212743705128607490575525)
                      ·
                        rfl

theorem cell23_6256796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_6256796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256796 prefixEnd_6256796 := by exact prefixLift 6256796
  have htrace : WordTrace (prefixWord ++ tailWord_6256796) baseStart_6256796 baseEnd_6256796 := by
    simpa [prefixWord, tailWord_6256796, baseEnd_6256796] using wordTrace_append hprefix tailTrace_6256796
  have hstable : (prefixWord ++ tailWord_6256796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256796).length < 2 ^ (prefixWord ++ tailWord_6256796).sum := by decide
  have hdescent : baseEnd_6256796 < baseStart_6256796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256823 : List Nat := [1, 1, 3, 1, 4, 2, 3, 3, 1, 4]
def baseStart_6256823 : Nat := 118140960795 + 6256823 * 2 ^ 59
def prefixEnd_6256823 : Nat := 4983230072969 + 3 ^ 40 * 6256823 * 2
def baseEnd_6256823 : Nat := 1070919189702092961645967

theorem tailTrace_6256823 : CollatzResearch.WordTrace tailWord_6256823 prefixEnd_6256823 1070919189702092961645967 := by
  unfold tailWord_6256823
  simp only [CollatzResearch.WordTrace]
  refine ⟨228205082611606326139487123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152136721741070884092991415 228205082611606326139487123)
  ·
    refine ⟨342307623917409489209230685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228205082611606326139487123 342307623917409489209230685)
    ·
      refine ⟨128365358969028558453461507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342307623917409489209230685 128365358969028558453461507)
      ·
        refine ⟨192548038453542837680192261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128365358969028558453461507 192548038453542837680192261)
        ·
          refine ⟨36102757210039282065036049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192548038453542837680192261 36102757210039282065036049)
          ·
            refine ⟨27077067907529461548777037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36102757210039282065036049 27077067907529461548777037)
            ·
              refine ⟨10153900465323548080791389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27077067907529461548777037 10153900465323548080791389)
              ·
                refine ⟨3807712674496330530296771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10153900465323548080791389 3807712674496330530296771)
                ·
                  refine ⟨5711569011744495795445157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3807712674496330530296771 5711569011744495795445157)
                  ·
                    refine ⟨1070919189702092961645967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5711569011744495795445157 1070919189702092961645967)
                    ·
                      rfl

theorem cell23_6256823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_6256823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256823 prefixEnd_6256823 := by exact prefixLift 6256823
  have htrace : WordTrace (prefixWord ++ tailWord_6256823) baseStart_6256823 baseEnd_6256823 := by
    simpa [prefixWord, tailWord_6256823, baseEnd_6256823] using wordTrace_append hprefix tailTrace_6256823
  have hstable : (prefixWord ++ tailWord_6256823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256823).length < 2 ^ (prefixWord ++ tailWord_6256823).sum := by decide
  have hdescent : baseEnd_6256823 < baseStart_6256823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256879 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 3, 6]
def baseStart_6256879 : Nat := 118140960795 + 6256879 * 2 ^ 59
def prefixEnd_6256879 : Nat := 4983230072969 + 3 ^ 40 * 6256879 * 2
def baseEnd_6256879 : Nat := 1070928774674310221945881

theorem tailTrace_6256879 : CollatzResearch.WordTrace tailWord_6256879 prefixEnd_6256879 1070928774674310221945881 := by
  unfold tailWord_6256879
  simp only [CollatzResearch.WordTrace]
  refine ⟨228207125099403447703525691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152138083399602298469017127 228207125099403447703525691)
  ·
    refine ⟨342310687649105171555288537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228207125099403447703525691 342310687649105171555288537)
    ·
      refine ⟨256733015736828878666466403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342310687649105171555288537 256733015736828878666466403)
      ·
        refine ⟨385099523605243317999699605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256733015736828878666466403 385099523605243317999699605)
        ·
          refine ⟨18051540168995780531235919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 385099523605243317999699605 18051540168995780531235919)
          ·
            refine ⟨27077310253493670796853879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18051540168995780531235919 27077310253493670796853879)
            ·
              refine ⟨40615965380240506195280819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27077310253493670796853879 40615965380240506195280819)
              ·
                refine ⟨60923948070360759292921229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40615965380240506195280819 60923948070360759292921229)
                ·
                  refine ⟨22846480526385284734845461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60923948070360759292921229 22846480526385284734845461)
                  ·
                    refine ⟨1070928774674310221945881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22846480526385284734845461 1070928774674310221945881)
                    ·
                      rfl

theorem cell23_6256879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 6].length) (baseStart_6256879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256879 prefixEnd_6256879 := by exact prefixLift 6256879
  have htrace : WordTrace (prefixWord ++ tailWord_6256879) baseStart_6256879 baseEnd_6256879 := by
    simpa [prefixWord, tailWord_6256879, baseEnd_6256879] using wordTrace_append hprefix tailTrace_6256879
  have hstable : (prefixWord ++ tailWord_6256879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256879).length < 2 ^ (prefixWord ++ tailWord_6256879).sum := by decide
  have hdescent : baseEnd_6256879 < baseStart_6256879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256889 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 1, 1, 5]
def baseStart_6256889 : Nat := 118140960795 + 6256889 * 2 ^ 59
def prefixEnd_6256889 : Nat := 4983230072969 + 3 ^ 40 * 6256889 * 2
def baseEnd_6256889 : Nat := 3212791458829475626712597

theorem tailTrace_6256889 : CollatzResearch.WordTrace tailWord_6256889 prefixEnd_6256889 3212791458829475626712597 := by
  unfold tailWord_6256889
  simp only [CollatzResearch.WordTrace]
  refine ⟨228207489829367219411389721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152138326552911479607593147 228207489829367219411389721)
  ·
    refine ⟨171155617372025414558542291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228207489829367219411389721 171155617372025414558542291)
    ·
      refine ⟨256733426058038121837813437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171155617372025414558542291 256733426058038121837813437)
      ·
        refine ⟨96275034771764295689180039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256733426058038121837813437 96275034771764295689180039)
        ·
          refine ⟨144412552157646443533770059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96275034771764295689180039 144412552157646443533770059)
          ·
            refine ⟨216618828236469665300655089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144412552157646443533770059 216618828236469665300655089)
            ·
              refine ⟨162464121177352248975491317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216618828236469665300655089 162464121177352248975491317)
              ·
                refine ⟨15231011360376773341452311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162464121177352248975491317 15231011360376773341452311)
                ·
                  refine ⟨22846517040565160012178467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15231011360376773341452311 22846517040565160012178467)
                  ·
                    refine ⟨34269775560847740018267701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22846517040565160012178467 34269775560847740018267701)
                    ·
                      refine ⟨3212791458829475626712597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34269775560847740018267701 3212791458829475626712597)
                      ·
                        rfl

theorem cell23_6256889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_6256889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256889 prefixEnd_6256889 := by exact prefixLift 6256889
  have htrace : WordTrace (prefixWord ++ tailWord_6256889) baseStart_6256889 baseEnd_6256889 := by
    simpa [prefixWord, tailWord_6256889, baseEnd_6256889] using wordTrace_append hprefix tailTrace_6256889
  have hstable : (prefixWord ++ tailWord_6256889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256889).length < 2 ^ (prefixWord ++ tailWord_6256889).sum := by decide
  have hdescent : baseEnd_6256889 < baseStart_6256889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256896 : List Nat := [2, 1, 1, 2, 1, 1, 5, 4, 2, 4]
def baseStart_6256896 : Nat := 118140960795 + 6256896 * 2 ^ 59
def prefixEnd_6256896 : Nat := 4983230072969 + 3 ^ 40 * 6256896 * 2
def baseEnd_6256896 : Nat := 1070931684398019033108355

theorem tailTrace_6256896 : CollatzResearch.WordTrace tailWord_6256896 prefixEnd_6256896 1070931684398019033108355 := by
  unfold tailWord_6256896
  simp only [CollatzResearch.WordTrace]
  refine ⟨114103872570170929803447271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152138496760227906404596361 114103872570170929803447271)
  ·
    refine ⟨171155808855256394705170907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114103872570170929803447271 171155808855256394705170907)
    ·
      refine ⟨256733713282884592057756361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171155808855256394705170907 256733713282884592057756361)
      ·
        refine ⟨192550284962163444043317271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256733713282884592057756361 192550284962163444043317271)
        ·
          refine ⟨288825427443245166064975907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192550284962163444043317271 288825427443245166064975907)
          ·
            refine ⟨433238141164867749097463861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288825427443245166064975907 433238141164867749097463861)
            ·
              refine ⟨40616075734206351477887237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 433238141164867749097463861 40616075734206351477887237)
              ·
                refine ⟨7615514200163690902103857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40616075734206351477887237 7615514200163690902103857)
                ·
                  refine ⟨5711635650122768176577893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7615514200163690902103857 5711635650122768176577893)
                  ·
                    refine ⟨1070931684398019033108355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5711635650122768176577893 1070931684398019033108355)
                    ·
                      rfl

theorem cell23_6256896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 2, 4].length) (baseStart_6256896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256896 prefixEnd_6256896 := by exact prefixLift 6256896
  have htrace : WordTrace (prefixWord ++ tailWord_6256896) baseStart_6256896 baseEnd_6256896 := by
    simpa [prefixWord, tailWord_6256896, baseEnd_6256896] using wordTrace_append hprefix tailTrace_6256896
  have hstable : (prefixWord ++ tailWord_6256896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256896).length < 2 ^ (prefixWord ++ tailWord_6256896).sum := by decide
  have hdescent : baseEnd_6256896 < baseStart_6256896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256899 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 4]
def baseStart_6256899 : Nat := 118140960795 + 6256899 * 2 ^ 59
def prefixEnd_6256899 : Nat := 4983230072969 + 3 ^ 40 * 6256899 * 2
def baseEnd_6256899 : Nat := 3212796593636020587587551

theorem tailTrace_6256899 : CollatzResearch.WordTrace tailWord_6256899 prefixEnd_6256899 3212796593636020587587551 := by
  unfold tailWord_6256899
  simp only [CollatzResearch.WordTrace]
  refine ⟨228207854559330991119253751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152138569706220660746169167 228207854559330991119253751)
  ·
    refine ⟨342311781838996486678880627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228207854559330991119253751 342311781838996486678880627)
    ·
      refine ⟨513467672758494730018320941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342311781838996486678880627 513467672758494730018320941)
      ·
        refine ⟨192550377284435523756870353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 513467672758494730018320941 192550377284435523756870353)
        ·
          refine ⟨144412782963326642817652765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192550377284435523756870353 144412782963326642817652765)
          ·
            refine ⟨54154793611247491056619787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144412782963326642817652765 54154793611247491056619787)
            ·
              refine ⟨81232190416871236584929681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54154793611247491056619787 81232190416871236584929681)
              ·
                refine ⟨60924142812653427438697261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81232190416871236584929681 60924142812653427438697261)
                ·
                  refine ⟨22846553554745035289511473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60924142812653427438697261 22846553554745035289511473)
                  ·
                    refine ⟨17134915166058776467133605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22846553554745035289511473 17134915166058776467133605)
                    ·
                      refine ⟨3212796593636020587587551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17134915166058776467133605 3212796593636020587587551)
                      ·
                        rfl

theorem cell23_6256899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_6256899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256899 prefixEnd_6256899 := by exact prefixLift 6256899
  have htrace : WordTrace (prefixWord ++ tailWord_6256899) baseStart_6256899 baseEnd_6256899 := by
    simpa [prefixWord, tailWord_6256899, baseEnd_6256899] using wordTrace_append hprefix tailTrace_6256899
  have hstable : (prefixWord ++ tailWord_6256899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256899).length < 2 ^ (prefixWord ++ tailWord_6256899).sum := by decide
  have hdescent : baseEnd_6256899 < baseStart_6256899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256906 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_6256906 : Nat := 118140960795 + 6256906 * 2 ^ 59
def prefixEnd_6256906 : Nat := 4983230072969 + 3 ^ 40 * 6256906 * 2
def baseEnd_6256906 : Nat := 3212800188000602060200019

theorem tailTrace_6256906 : CollatzResearch.WordTrace tailWord_6256906 prefixEnd_6256906 3212800188000602060200019 := by
  unfold tailWord_6256906
  simp only [CollatzResearch.WordTrace]
  refine ⟨57052027467576407828689643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152138739913537087543172381 57052027467576407828689643)
  ·
    refine ⟨85578041201364611743034465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57052027467576407828689643 85578041201364611743034465)
    ·
      refine ⟨64183530901023458807275849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85578041201364611743034465 64183530901023458807275849)
      ·
        refine ⟨48137648175767594105456887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64183530901023458807275849 48137648175767594105456887)
        ·
          refine ⟨72206472263651391158185331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48137648175767594105456887 72206472263651391158185331)
          ·
            refine ⟨108309708395477086737277997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72206472263651391158185331 108309708395477086737277997)
            ·
              refine ⟨40616140648303907526479249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108309708395477086737277997 40616140648303907526479249)
              ·
                refine ⟨30462105486227930644859437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40616140648303907526479249 30462105486227930644859437)
                ·
                  refine ⟨11423289557335473991822289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30462105486227930644859437 11423289557335473991822289)
                  ·
                    refine ⟨8567467168001605493866717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11423289557335473991822289 8567467168001605493866717)
                    ·
                      refine ⟨3212800188000602060200019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8567467168001605493866717 3212800188000602060200019)
                      ·
                        rfl

theorem cell23_6256906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_6256906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256906 prefixEnd_6256906 := by exact prefixLift 6256906
  have htrace : WordTrace (prefixWord ++ tailWord_6256906) baseStart_6256906 baseEnd_6256906 := by
    simpa [prefixWord, tailWord_6256906, baseEnd_6256906] using wordTrace_append hprefix tailTrace_6256906
  have hstable : (prefixWord ++ tailWord_6256906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256906).length < 2 ^ (prefixWord ++ tailWord_6256906).sum := by decide
  have hdescent : baseEnd_6256906 < baseStart_6256906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256980 : List Nat := [2, 4, 1, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_6256980 : Nat := 118140960795 + 6256980 * 2 ^ 59
def prefixEnd_6256980 : Nat := 4983230072969 + 3 ^ 40 * 6256980 * 2
def baseEnd_6256980 : Nat := 3212838185569034770674679

theorem tailTrace_6256980 : CollatzResearch.WordTrace tailWord_6256980 prefixEnd_6256980 3212838185569034770674679 := by
  unfold tailWord_6256980
  simp only [CollatzResearch.WordTrace]
  refine ⟨114105404436018770976476197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152140539248025027968634929 114105404436018770976476197)
  ·
    refine ⟨21394763331753519558089287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114105404436018770976476197 21394763331753519558089287)
    ·
      refine ⟨32092144997630279337133931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21394763331753519558089287 32092144997630279337133931)
      ·
        refine ⟨48138217496445419005700897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32092144997630279337133931 48138217496445419005700897)
        ·
          refine ⟨36103663122334064254275673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48138217496445419005700897 36103663122334064254275673)
          ·
            refine ⟨27077747341750548190706755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36103663122334064254275673 27077747341750548190706755)
            ·
              refine ⟨40616621012625822286060133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27077747341750548190706755 40616621012625822286060133)
              ·
                refine ⟨7615616439867341678636275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40616621012625822286060133 7615616439867341678636275)
                ·
                  refine ⟨11423424659801012517954413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7615616439867341678636275 11423424659801012517954413)
                  ·
                    refine ⟨4283784247425379694232905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11423424659801012517954413 4283784247425379694232905)
                    ·
                      refine ⟨3212838185569034770674679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4283784247425379694232905 3212838185569034770674679)
                      ·
                        rfl

theorem cell23_6256980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_6256980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256980 prefixEnd_6256980 := by exact prefixLift 6256980
  have htrace : WordTrace (prefixWord ++ tailWord_6256980) baseStart_6256980 baseEnd_6256980 := by
    simpa [prefixWord, tailWord_6256980, baseEnd_6256980] using wordTrace_append hprefix tailTrace_6256980
  have hstable : (prefixWord ++ tailWord_6256980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256980).length < 2 ^ (prefixWord ++ tailWord_6256980).sum := by decide
  have hdescent : baseEnd_6256980 < baseStart_6256980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256988 : List Nat := [2, 2, 4, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_6256988 : Nat := 118140960795 + 6256988 * 2 ^ 59
def prefixEnd_6256988 : Nat := 4983230072969 + 3 ^ 40 * 6256988 * 2
def baseEnd_6256988 : Nat := 3212842293414270739374643

theorem tailTrace_6256988 : CollatzResearch.WordTrace tailWord_6256988 prefixEnd_6256988 3212842293414270739374643 := by
  unfold tailWord_6256988
  simp only [CollatzResearch.WordTrace]
  refine ⟨114105550328004279659621809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152140733770672372879495745 114105550328004279659621809)
  ·
    refine ⟨85579162746003209744716357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114105550328004279659621809 85579162746003209744716357)
    ·
      refine ⟨16046093014875601827134317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85579162746003209744716357 16046093014875601827134317)
      ·
        refine ⟨6017284880578350685175369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16046093014875601827134317 6017284880578350685175369)
        ·
          refine ⟨4512963660433763013881527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6017284880578350685175369 4512963660433763013881527)
          ·
            refine ⟨6769445490650644520822291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4512963660433763013881527 6769445490650644520822291)
            ·
              refine ⟨10154168235975966781233437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6769445490650644520822291 10154168235975966781233437)
              ·
                refine ⟨3807813088490987542962539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10154168235975966781233437 3807813088490987542962539)
                ·
                  refine ⟨5711719632736481314443809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3807813088490987542962539 5711719632736481314443809)
                  ·
                    refine ⟨4283789724552360985832857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5711719632736481314443809 4283789724552360985832857)
                    ·
                      refine ⟨3212842293414270739374643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4283789724552360985832857 3212842293414270739374643)
                      ·
                        rfl

theorem cell23_6256988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_6256988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256988 prefixEnd_6256988 := by exact prefixLift 6256988
  have htrace : WordTrace (prefixWord ++ tailWord_6256988) baseStart_6256988 baseEnd_6256988 := by
    simpa [prefixWord, tailWord_6256988, baseEnd_6256988] using wordTrace_append hprefix tailTrace_6256988
  have hstable : (prefixWord ++ tailWord_6256988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256988).length < 2 ^ (prefixWord ++ tailWord_6256988).sum := by decide
  have hdescent : baseEnd_6256988 < baseStart_6256988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6256996 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_6256996 : Nat := 118140960795 + 6256996 * 2 ^ 59
def prefixEnd_6256996 : Nat := 4983230072969 + 3 ^ 40 * 6256996 * 2
def baseEnd_6256996 : Nat := 3212846401259506708074605

theorem tailTrace_6256996 : CollatzResearch.WordTrace tailWord_6256996 prefixEnd_6256996 3212846401259506708074605 := by
  unfold tailWord_6256996
  simp only [CollatzResearch.WordTrace]
  refine ⟨114105696219989788342767421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152140928293319717790356561 114105696219989788342767421)
  ·
    refine ⟨42789636082496170628537783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114105696219989788342767421 42789636082496170628537783)
    ·
      refine ⟨64184454123744255942806675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42789636082496170628537783 64184454123744255942806675)
      ·
        refine ⟨96276681185616383914210013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64184454123744255942806675 96276681185616383914210013)
        ·
          refine ⟨36103755444606143967828755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96276681185616383914210013 36103755444606143967828755)
          ·
            refine ⟨54155633166909215951743133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36103755444606143967828755 54155633166909215951743133)
            ·
              refine ⟨20308362437590955981903675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54155633166909215951743133 20308362437590955981903675)
              ·
                refine ⟨30462543656386433972855513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20308362437590955981903675 30462543656386433972855513)
                ·
                  refine ⟨22846907742289825479641635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30462543656386433972855513 22846907742289825479641635)
                  ·
                    refine ⟨34270361613434738219462453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22846907742289825479641635 34270361613434738219462453)
                    ·
                      refine ⟨3212846401259506708074605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34270361613434738219462453 3212846401259506708074605)
                      ·
                        rfl

theorem cell23_6256996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_6256996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6256996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6256996 prefixEnd_6256996 := by exact prefixLift 6256996
  have htrace : WordTrace (prefixWord ++ tailWord_6256996) baseStart_6256996 baseEnd_6256996 := by
    simpa [prefixWord, tailWord_6256996, baseEnd_6256996] using wordTrace_append hprefix tailTrace_6256996
  have hstable : (prefixWord ++ tailWord_6256996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6256996).length < 2 ^ (prefixWord ++ tailWord_6256996).sum := by decide
  have hdescent : baseEnd_6256996 < baseStart_6256996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6256996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257009 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_6257009 : Nat := 118140960795 + 6257009 * 2 ^ 59
def prefixEnd_6257009 : Nat := 4983230072969 + 3 ^ 40 * 6257009 * 2
def baseEnd_6257009 : Nat := 3212853076508015157212045

theorem tailTrace_6257009 : CollatzResearch.WordTrace tailWord_6257009 prefixEnd_6257009 3212853076508015157212045 := by
  unfold tailWord_6257009
  simp only [CollatzResearch.WordTrace]
  refine ⟨228211866588932479905758081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152141244392621653270505387 228211866588932479905758081)
  ·
    refine ⟨171158899941699359929318561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228211866588932479905758081 171158899941699359929318561)
    ·
      refine ⟨128369174956274519946988921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171158899941699359929318561 128369174956274519946988921)
      ·
        refine ⟨96276881217205889960241691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128369174956274519946988921 96276881217205889960241691)
        ·
          refine ⟨144415321825808834940362537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96276881217205889960241691 144415321825808834940362537)
          ·
            refine ⟨108311491369356626205271903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144415321825808834940362537 108311491369356626205271903)
            ·
              refine ⟨162467237054034939307907855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108311491369356626205271903 162467237054034939307907855)
              ·
                refine ⟨243700855581052408961861783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162467237054034939307907855 243700855581052408961861783)
                ·
                  refine ⟨365551283371578613442792675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243700855581052408961861783 365551283371578613442792675)
                  ·
                    refine ⟨548326925057367920164189013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 365551283371578613442792675 548326925057367920164189013)
                    ·
                      refine ⟨3212853076508015157212045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 548326925057367920164189013 3212853076508015157212045)
                      ·
                        rfl

theorem cell23_6257009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_6257009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257009 prefixEnd_6257009 := by exact prefixLift 6257009
  have htrace : WordTrace (prefixWord ++ tailWord_6257009) baseStart_6257009 baseEnd_6257009 := by
    simpa [prefixWord, tailWord_6257009, baseEnd_6257009] using wordTrace_append hprefix tailTrace_6257009
  have hstable : (prefixWord ++ tailWord_6257009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257009).length < 2 ^ (prefixWord ++ tailWord_6257009).sum := by decide
  have hdescent : baseEnd_6257009 < baseStart_6257009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257010 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 4, 2, 2]
def baseStart_6257010 : Nat := 118140960795 + 6257010 * 2 ^ 59
def prefixEnd_6257010 : Nat := 4983230072969 + 3 ^ 40 * 6257010 * 2
def baseEnd_6257010 : Nat := 3212853589988669653299541

theorem tailTrace_6257010 : CollatzResearch.WordTrace tailWord_6257010 prefixEnd_6257010 3212853589988669653299541 := by
  unfold tailWord_6257010
  simp only [CollatzResearch.WordTrace]
  refine ⟨57052975765482214269136121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152141268707952571384362989 57052975765482214269136121)
  ·
    refine ⟨42789731824111660701852091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57052975765482214269136121 42789731824111660701852091)
    ·
      refine ⟨64184597736167491052778137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42789731824111660701852091 64184597736167491052778137)
      ·
        refine ⟨48138448302125618289583603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64184597736167491052778137 48138448302125618289583603)
        ·
          refine ⟨72207672453188427434375405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48138448302125618289583603 72207672453188427434375405)
          ·
            refine ⟨27077877169945660287890777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72207672453188427434375405 27077877169945660287890777)
            ·
              refine ⟨20308407877459245215918083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27077877169945660287890777 20308407877459245215918083)
              ·
                refine ⟨30462611816188867823877125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20308407877459245215918083 30462611816188867823877125)
                ·
                  refine ⟨5711739715535412716976961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30462611816188867823877125 5711739715535412716976961)
                  ·
                    refine ⟨4283804786651559537732721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5711739715535412716976961 4283804786651559537732721)
                    ·
                      refine ⟨3212853589988669653299541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4283804786651559537732721 3212853589988669653299541)
                      ·
                        rfl

theorem cell23_6257010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_6257010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257010 prefixEnd_6257010 := by exact prefixLift 6257010
  have htrace : WordTrace (prefixWord ++ tailWord_6257010) baseStart_6257010 baseEnd_6257010 := by
    simpa [prefixWord, tailWord_6257010, baseEnd_6257010] using wordTrace_append hprefix tailTrace_6257010
  have hstable : (prefixWord ++ tailWord_6257010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257010).length < 2 ^ (prefixWord ++ tailWord_6257010).sum := by decide
  have hdescent : baseEnd_6257010 < baseStart_6257010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257027 : List Nat := [1, 1, 1, 3, 6, 1, 1, 3, 2, 2, 2]
def baseStart_6257027 : Nat := 118140960795 + 6257027 * 2 ^ 59
def prefixEnd_6257027 : Nat := 4983230072969 + 3 ^ 40 * 6257027 * 2
def baseEnd_6257027 : Nat := 3212862319159796086786963

theorem tailTrace_6257027 : CollatzResearch.WordTrace tailWord_6257027 prefixEnd_6257027 3212862319159796086786963 := by
  unfold tailWord_6257027
  simp only [CollatzResearch.WordTrace]
  refine ⟨228212523102867268979913335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152141682068578179319942223 228212523102867268979913335)
  ·
    refine ⟨342318784654300903469870003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228212523102867268979913335 342318784654300903469870003)
    ·
      refine ⟨513478176981451355204805005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342318784654300903469870003 513478176981451355204805005)
      ·
        refine ⟨192554316368044258201801877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 513478176981451355204805005 192554316368044258201801877)
        ·
          refine ⟨9025983579752074603209463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 192554316368044258201801877 9025983579752074603209463)
          ·
            refine ⟨13538975369628111904814195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9025983579752074603209463 13538975369628111904814195)
            ·
              refine ⟨20308463054442167857221293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13538975369628111904814195 20308463054442167857221293)
              ·
                refine ⟨7615673645415812946457985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20308463054442167857221293 7615673645415812946457985)
                ·
                  refine ⟨5711755234061859709843489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7615673645415812946457985 5711755234061859709843489)
                  ·
                    refine ⟨4283816425546394782382617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5711755234061859709843489 4283816425546394782382617)
                    ·
                      refine ⟨3212862319159796086786963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4283816425546394782382617 3212862319159796086786963)
                      ·
                        rfl

theorem cell23_6257027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 2, 2].length) (baseStart_6257027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257027 prefixEnd_6257027 := by exact prefixLift 6257027
  have htrace : WordTrace (prefixWord ++ tailWord_6257027) baseStart_6257027 baseEnd_6257027 := by
    simpa [prefixWord, tailWord_6257027, baseEnd_6257027] using wordTrace_append hprefix tailTrace_6257027
  have hstable : (prefixWord ++ tailWord_6257027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257027).length < 2 ^ (prefixWord ++ tailWord_6257027).sum := by decide
  have hdescent : baseEnd_6257027 < baseStart_6257027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257056 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 5]
def baseStart_6257056 : Nat := 118140960795 + 6257056 * 2 ^ 59
def prefixEnd_6257056 : Nat := 4983230072969 + 3 ^ 40 * 6257056 * 2
def baseEnd_6257056 : Nat := 3212877210098776473324329

theorem tailTrace_6257056 : CollatzResearch.WordTrace tailWord_6257056 prefixEnd_6257056 3212877210098776473324329 := by
  unfold tailWord_6257056
  simp only [CollatzResearch.WordTrace]
  refine ⟨114106790409881103466359511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152142387213174804621812681 114106790409881103466359511)
  ·
    refine ⟨171160185614821655199539267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114106790409881103466359511 171160185614821655199539267)
    ·
      refine ⟨256740278422232482799308901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171160185614821655199539267 256740278422232482799308901)
      ·
        refine ⟨48138802204168590524870419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256740278422232482799308901 48138802204168590524870419)
        ·
          refine ⟨72208203306252885787305629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48138802204168590524870419 72208203306252885787305629)
          ·
            refine ⟨27078076239844832170239611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72208203306252885787305629 27078076239844832170239611)
            ·
              refine ⟨40617114359767248255359417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27078076239844832170239611 40617114359767248255359417)
              ·
                refine ⟨30462835769825436191519563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40617114359767248255359417 30462835769825436191519563)
                ·
                  refine ⟨45694253654738154287279345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30462835769825436191519563 45694253654738154287279345)
                  ·
                    refine ⟨34270690241053615715459509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45694253654738154287279345 34270690241053615715459509)
                    ·
                      refine ⟨3212877210098776473324329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34270690241053615715459509 3212877210098776473324329)
                      ·
                        rfl

theorem cell23_6257056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_6257056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257056 prefixEnd_6257056 := by exact prefixLift 6257056
  have htrace : WordTrace (prefixWord ++ tailWord_6257056) baseStart_6257056 baseEnd_6257056 := by
    simpa [prefixWord, tailWord_6257056, baseEnd_6257056] using wordTrace_append hprefix tailTrace_6257056
  have hstable : (prefixWord ++ tailWord_6257056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257056).length < 2 ^ (prefixWord ++ tailWord_6257056).sum := by decide
  have hdescent : baseEnd_6257056 < baseStart_6257056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257063 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 2, 5]
def baseStart_6257063 : Nat := 118140960795 + 6257063 * 2 ^ 59
def prefixEnd_6257063 : Nat := 4983230072969 + 3 ^ 40 * 6257063 * 2
def baseEnd_6257063 : Nat := 1070960268154452648645599

theorem tailTrace_6257063 : CollatzResearch.WordTrace tailWord_6257063 prefixEnd_6257063 1070960268154452648645599 := by
  unfold tailWord_6257063
  simp only [CollatzResearch.WordTrace]
  refine ⟨228213836130736847128223843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152142557420491231418815895 228213836130736847128223843)
  ·
    refine ⟨342320754196105270692335765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228213836130736847128223843 342320754196105270692335765)
    ·
      refine ⟨16046285352942434563703239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 342320754196105270692335765 16046285352942434563703239)
      ·
        refine ⟨24069428029413651845554859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16046285352942434563703239 24069428029413651845554859)
        ·
          refine ⟨36104142044120477768332289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24069428029413651845554859 36104142044120477768332289)
          ·
            refine ⟨27078106533090358326249217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36104142044120477768332289 27078106533090358326249217)
            ·
              refine ⟨20308579899817768744686913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27078106533090358326249217 20308579899817768744686913)
              ·
                refine ⟨15231434924863326558515185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20308579899817768744686913 15231434924863326558515185)
                ·
                  refine ⟨11423576193647494918886389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15231434924863326558515185 11423576193647494918886389)
                  ·
                    refine ⟨1070960268154452648645599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11423576193647494918886389 1070960268154452648645599)
                    ·
                      rfl

theorem cell23_6257063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_6257063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257063 prefixEnd_6257063 := by exact prefixLift 6257063
  have htrace : WordTrace (prefixWord ++ tailWord_6257063) baseStart_6257063 baseEnd_6257063 := by
    simpa [prefixWord, tailWord_6257063, baseEnd_6257063] using wordTrace_append hprefix tailTrace_6257063
  have hstable : (prefixWord ++ tailWord_6257063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257063).length < 2 ^ (prefixWord ++ tailWord_6257063).sum := by decide
  have hdescent : baseEnd_6257063 < baseStart_6257063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257110 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_6257110 : Nat := 118140960795 + 6257110 * 2 ^ 59
def prefixEnd_6257110 : Nat := 4983230072969 + 3 ^ 40 * 6257110 * 2
def baseEnd_6257110 : Nat := 1070968312684706420683027

theorem tailTrace_6257110 : CollatzResearch.WordTrace tailWord_6257110 prefixEnd_6257110 1070968312684706420683027 := by
  unfold tailWord_6257110
  simp only [CollatzResearch.WordTrace]
  refine ⟨14263471897597910884699049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152143700241044382770123189 14263471897597910884699049)
  ·
    refine ⟨10697603923198433163524287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14263471897597910884699049 10697603923198433163524287)
    ·
      refine ⟨16046405884797649745286431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10697603923198433163524287 16046405884797649745286431)
      ·
        refine ⟨24069608827196474617929647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16046405884797649745286431 24069608827196474617929647)
        ·
          refine ⟨36104413240794711926894471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24069608827196474617929647 36104413240794711926894471)
          ·
            refine ⟨54156619861192067890341707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36104413240794711926894471 54156619861192067890341707)
            ·
              refine ⟨81234929791788101835512561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54156619861192067890341707 81234929791788101835512561)
              ·
                refine ⟨60926197343841076376634421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81234929791788101835512561 60926197343841076376634421)
                ·
                  refine ⟨5711831000985100910309477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60926197343841076376634421 5711831000985100910309477)
                  ·
                    refine ⟨1070968312684706420683027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5711831000985100910309477 1070968312684706420683027)
                    ·
                      rfl

theorem cell23_6257110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_6257110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257110 prefixEnd_6257110 := by exact prefixLift 6257110
  have htrace : WordTrace (prefixWord ++ tailWord_6257110) baseStart_6257110 baseEnd_6257110 := by
    simpa [prefixWord, tailWord_6257110, baseEnd_6257110] using wordTrace_append hprefix tailTrace_6257110
  have hstable : (prefixWord ++ tailWord_6257110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257110).length < 2 ^ (prefixWord ++ tailWord_6257110).sum := by decide
  have hdescent : baseEnd_6257110 < baseStart_6257110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257123 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 8]
def baseStart_6257123 : Nat := 118140960795 + 6257123 * 2 ^ 59
def prefixEnd_6257123 : Nat := 4983230072969 + 3 ^ 40 * 6257123 * 2
def baseEnd_6257123 : Nat := 356990179255847523465169

theorem tailTrace_6257123 : CollatzResearch.WordTrace tailWord_6257123 prefixEnd_6257123 356990179255847523465169 := by
  unfold tailWord_6257123
  simp only [CollatzResearch.WordTrace]
  refine ⟨228216024510519477375408023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152144016340346318250272015 228216024510519477375408023)
  ·
    refine ⟨342324036765779216063112035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228216024510519477375408023 342324036765779216063112035)
    ·
      refine ⟨513486055148668824094668053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342324036765779216063112035 513486055148668824094668053)
      ·
        refine ⟨24069658835093851129437565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 513486055148668824094668053 24069658835093851129437565)
        ·
          refine ⟨9026122063160194173539087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24069658835093851129437565 9026122063160194173539087)
          ·
            refine ⟨13539183094740291260308631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9026122063160194173539087 13539183094740291260308631)
            ·
              refine ⟨20308774642110436890462947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13539183094740291260308631 20308774642110436890462947)
              ·
                refine ⟨30463161963165655335694421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20308774642110436890462947 30463161963165655335694421)
                ·
                  refine ⟨356990179255847523465169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30463161963165655335694421 356990179255847523465169)
                  ·
                    rfl

theorem cell23_6257123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 8].length) (baseStart_6257123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257123 prefixEnd_6257123 := by exact prefixLift 6257123
  have htrace : WordTrace (prefixWord ++ tailWord_6257123) baseStart_6257123 baseEnd_6257123 := by
    simpa [prefixWord, tailWord_6257123, baseEnd_6257123] using wordTrace_append hprefix tailTrace_6257123
  have hstable : (prefixWord ++ tailWord_6257123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257123).length < 2 ^ (prefixWord ++ tailWord_6257123).sum := by decide
  have hdescent : baseEnd_6257123 < baseStart_6257123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257160 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 2, 3, 2]
def baseStart_6257160 : Nat := 118140960795 + 6257160 * 2 ^ 59
def prefixEnd_6257160 : Nat := 4983230072969 + 3 ^ 40 * 6257160 * 2
def baseEnd_6257160 : Nat := 3212930612086844066423851

theorem tailTrace_6257160 : CollatzResearch.WordTrace tailWord_6257160 prefixEnd_6257160 3212930612086844066423851 := by
  unfold tailWord_6257160
  simp only [CollatzResearch.WordTrace]
  refine ⟨114108687005692716347252467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152144916007590288463003289 114108687005692716347252467)
  ·
    refine ⟨171163030508539074520878701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114108687005692716347252467 171163030508539074520878701)
    ·
      refine ⟨64186136440702152945329513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171163030508539074520878701 64186136440702152945329513)
      ·
        refine ⟨48139602330526614708997135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64186136440702152945329513 48139602330526614708997135)
        ·
          refine ⟨72209403495789922063495703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48139602330526614708997135 72209403495789922063495703)
          ·
            refine ⟨108314105243684883095243555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72209403495789922063495703 108314105243684883095243555)
            ·
              refine ⟨162471157865527324642865333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108314105243684883095243555 162471157865527324642865333)
              ·
                refine ⟨15231671049893186685268625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162471157865527324642865333 15231671049893186685268625)
                ·
                  refine ⟨11423753287419890013951469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15231671049893186685268625 11423753287419890013951469)
                  ·
                    refine ⟨4283907482782458755231801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11423753287419890013951469 4283907482782458755231801)
                    ·
                      refine ⟨3212930612086844066423851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4283907482782458755231801 3212930612086844066423851)
                      ·
                        rfl

theorem cell23_6257160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_6257160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257160 prefixEnd_6257160 := by exact prefixLift 6257160
  have htrace : WordTrace (prefixWord ++ tailWord_6257160) baseStart_6257160 baseEnd_6257160 := by
    simpa [prefixWord, tailWord_6257160, baseEnd_6257160] using wordTrace_append hprefix tailTrace_6257160
  have hstable : (prefixWord ++ tailWord_6257160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257160).length < 2 ^ (prefixWord ++ tailWord_6257160).sum := by decide
  have hdescent : baseEnd_6257160 < baseStart_6257160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257184 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 3, 1, 3]
def baseStart_6257184 : Nat := 118140960795 + 6257184 * 2 ^ 59
def prefixEnd_6257184 : Nat := 4983230072969 + 3 ^ 40 * 6257184 * 2
def baseEnd_6257184 : Nat := 3212942935622551972523741

theorem tailTrace_6257184 : CollatzResearch.WordTrace tailWord_6257184 prefixEnd_6257184 3212942935622551972523741 := by
  unfold tailWord_6257184
  simp only [CollatzResearch.WordTrace]
  refine ⟨114109124681649242396689303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152145499575532323195585737 114109124681649242396689303)
  ·
    refine ⟨171163687022473863595033955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114109124681649242396689303 171163687022473863595033955)
    ·
      refine ⟨256745530533710795392550933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171163687022473863595033955 256745530533710795392550933)
      ·
        refine ⟨12034946743767693534025825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 256745530533710795392550933 12034946743767693534025825)
        ·
          refine ⟨9026210057825770150519369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12034946743767693534025825 9026210057825770150519369)
          ·
            refine ⟨6769657543369327612889527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9026210057825770150519369 6769657543369327612889527)
            ·
              refine ⟨10154486315053991419334291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6769657543369327612889527 10154486315053991419334291)
              ·
                refine ⟨15231729472580987129001437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10154486315053991419334291 15231729472580987129001437)
                ·
                  refine ⟨5711898552217870173375539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15231729472580987129001437 5711898552217870173375539)
                  ·
                    refine ⟨8567847828326805260063309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5711898552217870173375539 8567847828326805260063309)
                    ·
                      refine ⟨3212942935622551972523741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8567847828326805260063309 3212942935622551972523741)
                      ·
                        rfl

theorem cell23_6257184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_6257184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257184 prefixEnd_6257184 := by exact prefixLift 6257184
  have htrace : WordTrace (prefixWord ++ tailWord_6257184) baseStart_6257184 baseEnd_6257184 := by
    simpa [prefixWord, tailWord_6257184, baseEnd_6257184] using wordTrace_append hprefix tailTrace_6257184
  have hstable : (prefixWord ++ tailWord_6257184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257184).length < 2 ^ (prefixWord ++ tailWord_6257184).sum := by decide
  have hdescent : baseEnd_6257184 < baseStart_6257184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257191 : List Nat := [1, 1, 7, 2, 2, 1, 2, 1, 6]
def baseStart_6257191 : Nat := 118140960795 + 6257191 * 2 ^ 59
def prefixEnd_6257191 : Nat := 4983230072969 + 3 ^ 40 * 6257191 * 2
def baseEnd_6257191 : Nat := 356994058887459271681801

theorem tailTrace_6257191 : CollatzResearch.WordTrace tailWord_6257191 prefixEnd_6257191 356994058887459271681801 := by
  unfold tailWord_6257191
  simp only [CollatzResearch.WordTrace]
  refine ⟨228218504674273124988883427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152145669782848749992588951 228218504674273124988883427)
  ·
    refine ⟨342327757011409687483325141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228218504674273124988883427 342327757011409687483325141)
    ·
      refine ⟨8023306804954914550390433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 342327757011409687483325141 8023306804954914550390433)
      ·
        refine ⟨6017480103716185912792825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8023306804954914550390433 6017480103716185912792825)
        ·
          refine ⟨4513110077787139434594619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6017480103716185912792825 4513110077787139434594619)
          ·
            refine ⟨6769665116680709151891929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4513110077787139434594619 6769665116680709151891929)
            ·
              refine ⟨5077248837510531863918947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6769665116680709151891929 5077248837510531863918947)
              ·
                refine ⟨7615873256265797795878421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5077248837510531863918947 7615873256265797795878421)
                ·
                  refine ⟨356994058887459271681801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7615873256265797795878421 356994058887459271681801)
                  ·
                    rfl

theorem cell23_6257191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 6].length) (baseStart_6257191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257191 prefixEnd_6257191 := by exact prefixLift 6257191
  have htrace : WordTrace (prefixWord ++ tailWord_6257191) baseStart_6257191 baseEnd_6257191 := by
    simpa [prefixWord, tailWord_6257191, baseEnd_6257191] using wordTrace_append hprefix tailTrace_6257191
  have hstable : (prefixWord ++ tailWord_6257191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257191).length < 2 ^ (prefixWord ++ tailWord_6257191).sum := by decide
  have hdescent : baseEnd_6257191 < baseStart_6257191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257203 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 4]
def baseStart_6257203 : Nat := 118140960795 + 6257203 * 2 ^ 59
def prefixEnd_6257203 : Nat := 4983230072969 + 3 ^ 40 * 6257203 * 2
def baseEnd_6257203 : Nat := 3212952691754987398186153

theorem tailTrace_6257203 : CollatzResearch.WordTrace tailWord_6257203 prefixEnd_6257203 3212952691754987398186153 := by
  unfold tailWord_6257203
  simp only [CollatzResearch.WordTrace]
  refine ⟨228218942350229651038320263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152145961566819767358880175 228218942350229651038320263)
  ·
    refine ⟨342328413525344476557480395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228218942350229651038320263 342328413525344476557480395)
    ·
      refine ⟨513492620288016714836220593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342328413525344476557480395 513492620288016714836220593)
      ·
        refine ⟨385119465216012536127165445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513492620288016714836220593 385119465216012536127165445)
        ·
          refine ⟨72209899728002350523843521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 385119465216012536127165445 72209899728002350523843521)
          ·
            refine ⟨54157424796001762892882641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72209899728002350523843521 54157424796001762892882641)
            ·
              refine ⟨40618068597001322169661981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54157424796001762892882641 40618068597001322169661981)
              ·
                refine ⟨15231775723875495813623243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40618068597001322169661981 15231775723875495813623243)
                ·
                  refine ⟨22847663585813243720434865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15231775723875495813623243 22847663585813243720434865)
                  ·
                    refine ⟨17135747689359932790326149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22847663585813243720434865 17135747689359932790326149)
                    ·
                      refine ⟨3212952691754987398186153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17135747689359932790326149 3212952691754987398186153)
                      ·
                        rfl

theorem cell23_6257203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_6257203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257203 prefixEnd_6257203 := by exact prefixLift 6257203
  have htrace : WordTrace (prefixWord ++ tailWord_6257203) baseStart_6257203 baseEnd_6257203 := by
    simpa [prefixWord, tailWord_6257203, baseEnd_6257203] using wordTrace_append hprefix tailTrace_6257203
  have hstable : (prefixWord ++ tailWord_6257203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257203).length < 2 ^ (prefixWord ++ tailWord_6257203).sum := by decide
  have hdescent : baseEnd_6257203 < baseStart_6257203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257210 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3]
def baseStart_6257210 : Nat := 118140960795 + 6257210 * 2 ^ 59
def prefixEnd_6257210 : Nat := 4983230072969 + 3 ^ 40 * 6257210 * 2
def baseEnd_6257210 : Nat := 3212956286119568870798621

theorem tailTrace_6257210 : CollatzResearch.WordTrace tailWord_6257210 prefixEnd_6257210 3212956286119568870798621 := by
  unfold tailWord_6257210
  simp only [CollatzResearch.WordTrace]
  refine ⟨57054799415301072808456271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152146131774136194155883389 57054799415301072808456271)
  ·
    refine ⟨85582199122951609212684407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57054799415301072808456271 85582199122951609212684407)
    ·
      refine ⟨128373298684427413819026611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85582199122951609212684407 128373298684427413819026611)
      ·
        refine ⟨192559948026641120728539917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128373298684427413819026611 192559948026641120728539917)
        ·
          refine ⟨72209980509990420273202469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192559948026641120728539917 72209980509990420273202469)
          ·
            refine ⟨13539371345623203801225463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72209980509990420273202469 13539371345623203801225463)
            ·
              refine ⟨20309057018434805701838195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13539371345623203801225463 20309057018434805701838195)
              ·
                refine ⟨30463585527652208552757293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20309057018434805701838195 30463585527652208552757293)
                ·
                  refine ⟨11423844572869578207283985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30463585527652208552757293 11423844572869578207283985)
                  ·
                    refine ⟨8567883429652183655462989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11423844572869578207283985 8567883429652183655462989)
                    ·
                      refine ⟨3212956286119568870798621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8567883429652183655462989 3212956286119568870798621)
                      ·
                        rfl

theorem cell23_6257210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_6257210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257210 prefixEnd_6257210 := by exact prefixLift 6257210
  have htrace : WordTrace (prefixWord ++ tailWord_6257210) baseStart_6257210 baseEnd_6257210 := by
    simpa [prefixWord, tailWord_6257210, baseEnd_6257210] using wordTrace_append hprefix tailTrace_6257210
  have hstable : (prefixWord ++ tailWord_6257210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257210).length < 2 ^ (prefixWord ++ tailWord_6257210).sum := by decide
  have hdescent : baseEnd_6257210 < baseStart_6257210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257213 : List Nat := [1, 4, 1, 3, 2, 1, 2, 9]
def baseStart_6257213 : Nat := 118140960795 + 6257213 * 2 ^ 59
def prefixEnd_6257213 : Nat := 4983230072969 + 3 ^ 40 * 6257213 * 2
def baseEnd_6257213 : Nat := 118998438020797494780041

theorem tailTrace_6257213 : CollatzResearch.WordTrace tailWord_6257213 prefixEnd_6257213 118998438020797494780041 := by
  unfold tailWord_6257213
  simp only [CollatzResearch.WordTrace]
  refine ⟨228219307080193422746184293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152146204720128948497456195 228219307080193422746184293)
  ·
    refine ⟨42791120077536266764909555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228219307080193422746184293 42791120077536266764909555)
    ·
      refine ⟨64186680116304400147364333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42791120077536266764909555 64186680116304400147364333)
      ·
        refine ⟨24070005043614150055261625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64186680116304400147364333 24070005043614150055261625)
        ·
          refine ⟨18052503782710612541446219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24070005043614150055261625 18052503782710612541446219)
          ·
            refine ⟨27078755674065918812169329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18052503782710612541446219 27078755674065918812169329)
            ·
              refine ⟨20309066755549439109126997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27078755674065918812169329 20309066755549439109126997)
              ·
                refine ⟨118998438020797494780041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20309066755549439109126997 118998438020797494780041)
                ·
                  rfl

theorem cell23_6257213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 9].length) (baseStart_6257213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257213 prefixEnd_6257213 := by exact prefixLift 6257213
  have htrace : WordTrace (prefixWord ++ tailWord_6257213) baseStart_6257213 baseEnd_6257213 := by
    simpa [prefixWord, tailWord_6257213, baseEnd_6257213] using wordTrace_append hprefix tailTrace_6257213
  have hstable : (prefixWord ++ tailWord_6257213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257213).length < 2 ^ (prefixWord ++ tailWord_6257213).sum := by decide
  have hdescent : baseEnd_6257213 < baseStart_6257213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257240 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 4, 1, 3]
def baseStart_6257240 : Nat := 118140960795 + 6257240 * 2 ^ 59
def prefixEnd_6257240 : Nat := 4983230072969 + 3 ^ 40 * 6257240 * 2
def baseEnd_6257240 : Nat := 3212971690539203753423483

theorem tailTrace_6257240 : CollatzResearch.WordTrace tailWord_6257240 prefixEnd_6257240 3212971690539203753423483 := by
  unfold tailWord_6257240
  simp only [CollatzResearch.WordTrace]
  refine ⟨114110145925547803178708587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152146861234063737571611449 114110145925547803178708587)
  ·
    refine ⟨171165218888321704768062881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114110145925547803178708587 171165218888321704768062881)
    ·
      refine ⟨128373914166241278576047161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171165218888321704768062881 128373914166241278576047161)
      ·
        refine ⟨96280435624680958932035371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128373914166241278576047161 96280435624680958932035371)
        ·
          refine ⟨144420653437021438398053057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96280435624680958932035371 144420653437021438398053057)
          ·
            refine ⟨108315490077766078798539793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144420653437021438398053057 108315490077766078798539793)
            ·
              refine ⟨81236617558324559098904845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108315490077766078798539793 81236617558324559098904845)
              ·
                refine ⟨30463731584371709662089317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81236617558324559098904845 30463731584371709662089317)
                ·
                  refine ⟨5711949672069695561641747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30463731584371709662089317 5711949672069695561641747)
                  ·
                    refine ⟨8567924508104543342462621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5711949672069695561641747 8567924508104543342462621)
                    ·
                      refine ⟨3212971690539203753423483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8567924508104543342462621 3212971690539203753423483)
                      ·
                        rfl

theorem cell23_6257240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_6257240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257240 prefixEnd_6257240 := by exact prefixLift 6257240
  have htrace : WordTrace (prefixWord ++ tailWord_6257240) baseStart_6257240 baseEnd_6257240 := by
    simpa [prefixWord, tailWord_6257240, baseEnd_6257240] using wordTrace_append hprefix tailTrace_6257240
  have hstable : (prefixWord ++ tailWord_6257240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257240).length < 2 ^ (prefixWord ++ tailWord_6257240).sum := by decide
  have hdescent : baseEnd_6257240 < baseStart_6257240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257283 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 5]
def baseStart_6257283 : Nat := 118140960795 + 6257283 * 2 ^ 59
def prefixEnd_6257283 : Nat := 4983230072969 + 3 ^ 40 * 6257283 * 2
def baseEnd_6257283 : Nat := 3212993770207347085185785

theorem tailTrace_6257283 : CollatzResearch.WordTrace tailWord_6257283 prefixEnd_6257283 3212993770207347085185785 := by
  unfold tailWord_6257283
  simp only [CollatzResearch.WordTrace]
  refine ⟨228221860189939824701232503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152147906793293216467488335 228221860189939824701232503)
  ·
    refine ⟨342332790284909737051848755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228221860189939824701232503 342332790284909737051848755)
    ·
      refine ⟨513499185427364605577773133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342332790284909737051848755 513499185427364605577773133)
      ·
        refine ⟨192562194535261727091664925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 513499185427364605577773133 192562194535261727091664925)
        ·
          refine ⟨72210822950723147659374347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192562194535261727091664925 72210822950723147659374347)
          ·
            refine ⟨108316234426084721489061521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72210822950723147659374347 108316234426084721489061521)
            ·
              refine ⟨81237175819563541116796141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108316234426084721489061521 81237175819563541116796141)
              ·
                refine ⟨30463940932336327918798553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81237175819563541116796141 30463940932336327918798553)
                ·
                  refine ⟨22847955699252245939098915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30463940932336327918798553 22847955699252245939098915)
                  ·
                    refine ⟨34271933548878368908648373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22847955699252245939098915 34271933548878368908648373)
                    ·
                      refine ⟨3212993770207347085185785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34271933548878368908648373 3212993770207347085185785)
                      ·
                        rfl

theorem cell23_6257283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_6257283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257283 prefixEnd_6257283 := by exact prefixLift 6257283
  have htrace : WordTrace (prefixWord ++ tailWord_6257283) baseStart_6257283 baseEnd_6257283 := by
    simpa [prefixWord, tailWord_6257283, baseEnd_6257283] using wordTrace_append hprefix tailTrace_6257283
  have hstable : (prefixWord ++ tailWord_6257283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257283).length < 2 ^ (prefixWord ++ tailWord_6257283).sum := by decide
  have hdescent : baseEnd_6257283 < baseStart_6257283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257284 : List Nat := [2, 3, 2, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_6257284 : Nat := 118140960795 + 6257284 * 2 ^ 59
def prefixEnd_6257284 : Nat := 4983230072969 + 3 ^ 40 * 6257284 * 2
def baseEnd_6257284 : Nat := 3212994283688001581273281

theorem tailTrace_6257284 : CollatzResearch.WordTrace tailWord_6257284 prefixEnd_6257284 3212994283688001581273281 := by
  unfold tailWord_6257284
  simp only [CollatzResearch.WordTrace]
  refine ⟨114110948331468100936009453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152147931108624134581345937 114110948331468100936009453)
  ·
    refine ⟨42791605624300537851003545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114110948331468100936009453 42791605624300537851003545)
    ·
      refine ⟨32093704218225403388252659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42791605624300537851003545 32093704218225403388252659)
      ·
        refine ⟨48140556327338105082378989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32093704218225403388252659 48140556327338105082378989)
        ·
          refine ⟨18052708622751789405892121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48140556327338105082378989 18052708622751789405892121)
          ·
            refine ⟨13539531467063842054419091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18052708622751789405892121 13539531467063842054419091)
            ·
              refine ⟨20309297200595763081628637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13539531467063842054419091 20309297200595763081628637)
              ·
                refine ⟨7615986450223411155610739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20309297200595763081628637 7615986450223411155610739)
                ·
                  refine ⟨11423979675335116733416109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7615986450223411155610739 11423979675335116733416109)
                  ·
                    refine ⟨4283992378250668775031041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11423979675335116733416109 4283992378250668775031041)
                    ·
                      refine ⟨3212994283688001581273281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4283992378250668775031041 3212994283688001581273281)
                      ·
                        rfl

theorem cell23_6257284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_6257284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257284 prefixEnd_6257284 := by exact prefixLift 6257284
  have htrace : WordTrace (prefixWord ++ tailWord_6257284) baseStart_6257284 baseEnd_6257284 := by
    simpa [prefixWord, tailWord_6257284, baseEnd_6257284] using wordTrace_append hprefix tailTrace_6257284
  have hstable : (prefixWord ++ tailWord_6257284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257284).length < 2 ^ (prefixWord ++ tailWord_6257284).sum := by decide
  have hdescent : baseEnd_6257284 < baseStart_6257284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257334 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_6257334 : Nat := 118140960795 + 6257334 * 2 ^ 59
def prefixEnd_6257334 : Nat := 4983230072969 + 3 ^ 40 * 6257334 * 2
def baseEnd_6257334 : Nat := 3213019957720726385648051

theorem tailTrace_6257334 : CollatzResearch.WordTrace tailWord_6257334 prefixEnd_6257334 3213019957720726385648051 := by
  unfold tailWord_6257334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14263982519547191275708691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152149146875170040274226037 14263982519547191275708691)
  ·
    refine ⟨21395973779320786913563037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14263982519547191275708691 21395973779320786913563037)
    ·
      refine ⟨8023490167245295092586139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21395973779320786913563037 8023490167245295092586139)
      ·
        refine ⟨12035235250867942638879209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8023490167245295092586139 12035235250867942638879209)
        ·
          refine ⟨9026426438150956979159407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12035235250867942638879209 9026426438150956979159407)
          ·
            refine ⟨13539639657226435468739111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9026426438150956979159407 13539639657226435468739111)
            ·
              refine ⟨20309459485839653203108667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13539639657226435468739111 20309459485839653203108667)
              ·
                refine ⟨30464189228759479804663001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20309459485839653203108667 30464189228759479804663001)
                ·
                  refine ⟨22848141921569609853497251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30464189228759479804663001 22848141921569609853497251)
                  ·
                    refine ⟨34272212882354414780245877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22848141921569609853497251 34272212882354414780245877)
                    ·
                      refine ⟨3213019957720726385648051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34272212882354414780245877 3213019957720726385648051)
                      ·
                        rfl

theorem cell23_6257334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_6257334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257334 prefixEnd_6257334 := by exact prefixLift 6257334
  have htrace : WordTrace (prefixWord ++ tailWord_6257334) baseStart_6257334 baseEnd_6257334 := by
    simpa [prefixWord, tailWord_6257334, baseEnd_6257334] using wordTrace_append hprefix tailTrace_6257334
  have hstable : (prefixWord ++ tailWord_6257334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257334).length < 2 ^ (prefixWord ++ tailWord_6257334).sum := by decide
  have hdescent : baseEnd_6257334 < baseStart_6257334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257353 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 2, 7, 4]
def baseStart_6257353 : Nat := 118140960795 + 6257353 * 2 ^ 59
def prefixEnd_6257353 : Nat := 4983230072969 + 3 ^ 40 * 6257353 * 2
def baseEnd_6257353 : Nat := 3213029713853161811310463

theorem tailTrace_6257353 : CollatzResearch.WordTrace tailWord_6257353 prefixEnd_6257353 3213029713853161811310463 := by
  unfold tailWord_6257353
  simp only [CollatzResearch.WordTrace]
  refine ⟨228224413299686226656280713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152149608866457484437520475 228224413299686226656280713)
  ·
    refine ⟨171168309974764669992210535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228224413299686226656280713 171168309974764669992210535)
    ·
      refine ⟨256752464962147004988315803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171168309974764669992210535 256752464962147004988315803)
      ·
        refine ⟨385128697443220507482473705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256752464962147004988315803 385128697443220507482473705)
        ·
          refine ⟨288846523082415380611855279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385128697443220507482473705 288846523082415380611855279)
          ·
            refine ⟨433269784623623070917782919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288846523082415380611855279 433269784623623070917782919)
            ·
              refine ⟨649904676935434606376674379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433269784623623070917782919 649904676935434606376674379)
              ·
                refine ⟨974857015403151909565011569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649904676935434606376674379 974857015403151909565011569)
                ·
                  refine ⟨731142761552363932173758677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 974857015403151909565011569 731142761552363932173758677)
                  ·
                    refine ⟨17136158473883529660322469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 731142761552363932173758677 17136158473883529660322469)
                    ·
                      refine ⟨3213029713853161811310463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17136158473883529660322469 3213029713853161811310463)
                      ·
                        rfl

theorem cell23_6257353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_6257353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257353 prefixEnd_6257353 := by exact prefixLift 6257353
  have htrace : WordTrace (prefixWord ++ tailWord_6257353) baseStart_6257353 baseEnd_6257353 := by
    simpa [prefixWord, tailWord_6257353, baseEnd_6257353] using wordTrace_append hprefix tailTrace_6257353
  have hstable : (prefixWord ++ tailWord_6257353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257353).length < 2 ^ (prefixWord ++ tailWord_6257353).sum := by decide
  have hdescent : baseEnd_6257353 < baseStart_6257353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257354 : List Nat := [3, 1, 2, 1, 4, 2, 3, 2, 5]
def baseStart_6257354 : Nat := 118140960795 + 6257354 * 2 ^ 59
def prefixEnd_6257354 : Nat := 4983230072969 + 3 ^ 40 * 6257354 * 2
def baseEnd_6257354 : Nat := 357003358592646256377551

theorem tailTrace_6257354 : CollatzResearch.WordTrace tailWord_6257354 prefixEnd_6257354 357003358592646256377551 := by
  unfold tailWord_6257354
  simp only [CollatzResearch.WordTrace]
  refine ⟨57056112443170650956766779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152149633181788402551378077 57056112443170650956766779)
  ·
    refine ⟨85584168664755976435150169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57056112443170650956766779 85584168664755976435150169)
    ·
      refine ⟨64188126498566982326362627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85584168664755976435150169 64188126498566982326362627)
      ·
        refine ⟨96282189747850473489543941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64188126498566982326362627 96282189747850473489543941)
        ·
          refine ⟨18052910577721963779289489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96282189747850473489543941 18052910577721963779289489)
          ·
            refine ⟨13539682933291472834467117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18052910577721963779289489 13539682933291472834467117)
            ·
              refine ⟨5077381099984302312925169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13539682933291472834467117 5077381099984302312925169)
              ·
                refine ⟨3808035824988226734693877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5077381099984302312925169 3808035824988226734693877)
                ·
                  refine ⟨357003358592646256377551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3808035824988226734693877 357003358592646256377551)
                  ·
                    rfl

theorem cell23_6257354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 5].length) (baseStart_6257354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257354 prefixEnd_6257354 := by exact prefixLift 6257354
  have htrace : WordTrace (prefixWord ++ tailWord_6257354) baseStart_6257354 baseEnd_6257354 := by
    simpa [prefixWord, tailWord_6257354, baseEnd_6257354] using wordTrace_append hprefix tailTrace_6257354
  have hstable : (prefixWord ++ tailWord_6257354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257354).length < 2 ^ (prefixWord ++ tailWord_6257354).sum := by decide
  have hdescent : baseEnd_6257354 < baseStart_6257354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257365 : List Nat := [1, 3, 2, 5, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6257365 : Nat := 118140960795 + 6257365 * 2 ^ 59
def prefixEnd_6257365 : Nat := 4983230072969 + 3 ^ 40 * 6257365 * 2
def baseEnd_6257365 : Nat := 3213035875621015764360409

theorem tailTrace_6257365 : CollatzResearch.WordTrace tailWord_6257365 prefixEnd_6257365 3213035875621015764360409 := by
  unfold tailWord_6257365
  simp only [CollatzResearch.WordTrace]
  refine ⟨228224850975642752705717549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152149900650428501803811699 228224850975642752705717549)
  ·
    refine ⟨85584319115866032264644081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228224850975642752705717549 85584319115866032264644081)
    ·
      refine ⟨64188239336899524198483061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85584319115866032264644081 64188239336899524198483061)
      ·
        refine ⟨6017647437834330393607787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64188239336899524198483061 6017647437834330393607787)
        ·
          refine ⟨9026471156751495590411681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6017647437834330393607787 9026471156751495590411681)
          ·
            refine ⟨6769853367563621692808761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9026471156751495590411681 6769853367563621692808761)
            ·
              refine ⟨5077390025672716269606571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6769853367563621692808761 5077390025672716269606571)
              ·
                refine ⟨7616085038509074404409857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5077390025672716269606571 7616085038509074404409857)
                ·
                  refine ⟨5712063778881805803307393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7616085038509074404409857 5712063778881805803307393)
                  ·
                    refine ⟨4284047834161354352480545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5712063778881805803307393 4284047834161354352480545)
                    ·
                      refine ⟨3213035875621015764360409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4284047834161354352480545 3213035875621015764360409)
                      ·
                        rfl

theorem cell23_6257365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6257365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257365 prefixEnd_6257365 := by exact prefixLift 6257365
  have htrace : WordTrace (prefixWord ++ tailWord_6257365) baseStart_6257365 baseEnd_6257365 := by
    simpa [prefixWord, tailWord_6257365, baseEnd_6257365] using wordTrace_append hprefix tailTrace_6257365
  have hstable : (prefixWord ++ tailWord_6257365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257365).length < 2 ^ (prefixWord ++ tailWord_6257365).sum := by decide
  have hdescent : baseEnd_6257365 < baseStart_6257365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257370 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4]
def baseStart_6257370 : Nat := 118140960795 + 6257370 * 2 ^ 59
def prefixEnd_6257370 : Nat := 4983230072969 + 3 ^ 40 * 6257370 * 2
def baseEnd_6257370 : Nat := 3213038443024288244797885

theorem tailTrace_6257370 : CollatzResearch.WordTrace tailWord_6257370 prefixEnd_6257370 3213038443024288244797885 := by
  unfold tailWord_6257370
  simp only [CollatzResearch.WordTrace]
  refine ⟨57056258335156159639912391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152150022227083092373099709 57056258335156159639912391)
  ·
    refine ⟨85584387502734239459868587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57056258335156159639912391 85584387502734239459868587)
    ·
      refine ⟨128376581254101359189802881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85584387502734239459868587 128376581254101359189802881)
      ·
        refine ⟨96282435940576019392352161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128376581254101359189802881 96282435940576019392352161)
        ·
          refine ⟨72211826955432014544264121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96282435940576019392352161 72211826955432014544264121)
          ·
            refine ⟨54158870216574010908198091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72211826955432014544264121 54158870216574010908198091)
            ·
              refine ⟨81238305324861016362297137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54158870216574010908198091 81238305324861016362297137)
              ·
                refine ⟨60928728993645762271722853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81238305324861016362297137 60928728993645762271722853)
                ·
                  refine ⟨11424136686308580425948035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60928728993645762271722853 11424136686308580425948035)
                  ·
                    refine ⟨17136205029462870638922053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11424136686308580425948035 17136205029462870638922053)
                    ·
                      refine ⟨3213038443024288244797885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17136205029462870638922053 3213038443024288244797885)
                      ·
                        rfl

theorem cell23_6257370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_6257370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257370 prefixEnd_6257370 := by exact prefixLift 6257370
  have htrace : WordTrace (prefixWord ++ tailWord_6257370) baseStart_6257370 baseEnd_6257370 := by
    simpa [prefixWord, tailWord_6257370, baseEnd_6257370] using wordTrace_append hprefix tailTrace_6257370
  have hstable : (prefixWord ++ tailWord_6257370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257370).length < 2 ^ (prefixWord ++ tailWord_6257370).sum := by decide
  have hdescent : baseEnd_6257370 < baseStart_6257370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257420 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 2, 5, 3]
def baseStart_6257420 : Nat := 118140960795 + 6257420 * 2 ^ 59
def prefixEnd_6257420 : Nat := 4983230072969 + 3 ^ 40 * 6257420 * 2
def baseEnd_6257420 : Nat := 3213064117057013049172655

theorem tailTrace_6257420 : CollatzResearch.WordTrace tailWord_6257420 prefixEnd_6257420 3213064117057013049172655 := by
  unfold tailWord_6257420
  simp only [CollatzResearch.WordTrace]
  refine ⟨114113428495221748549484857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152151237993628998065979809 114113428495221748549484857)
  ·
    refine ⟨85585071371416311412113643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114113428495221748549484857 85585071371416311412113643)
    ·
      refine ⟨128377607057124467118170465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85585071371416311412113643 128377607057124467118170465)
      ·
        refine ⟨96283205292843350338627849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128377607057124467118170465 96283205292843350338627849)
        ·
          refine ⟨72212403969632512753970887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96283205292843350338627849 72212403969632512753970887)
          ·
            refine ⟨108318605954448769130956331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72212403969632512753970887 108318605954448769130956331)
            ·
              refine ⟨162477908931673153696434497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108318605954448769130956331 162477908931673153696434497)
              ·
                refine ⟨121858431698754865272325873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162477908931673153696434497 121858431698754865272325873)
                ·
                  refine ⟨91393823774066148954244405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121858431698754865272325873 91393823774066148954244405)
                  ·
                    refine ⟨8568170978818701464460413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91393823774066148954244405 8568170978818701464460413)
                    ·
                      refine ⟨3213064117057013049172655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8568170978818701464460413 3213064117057013049172655)
                      ·
                        rfl

theorem cell23_6257420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_6257420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257420 prefixEnd_6257420 := by exact prefixLift 6257420
  have htrace : WordTrace (prefixWord ++ tailWord_6257420) baseStart_6257420 baseEnd_6257420 := by
    simpa [prefixWord, tailWord_6257420, baseEnd_6257420] using wordTrace_append hprefix tailTrace_6257420
  have hstable : (prefixWord ++ tailWord_6257420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257420).length < 2 ^ (prefixWord ++ tailWord_6257420).sum := by decide
  have hdescent : baseEnd_6257420 < baseStart_6257420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257457 : List Nat := [1, 2, 2, 3, 2, 1, 3, 3, 1, 5]
def baseStart_6257457 : Nat := 118140960795 + 6257457 * 2 ^ 59
def prefixEnd_6257457 : Nat := 4983230072969 + 3 ^ 40 * 6257457 * 2
def baseEnd_6257457 : Nat := 1071027705280409801469995

theorem tailTrace_6257457 : CollatzResearch.WordTrace tailWord_6257457 prefixEnd_6257457 1071027705280409801469995 := by
  unfold tailWord_6257457
  simp only [CollatzResearch.WordTrace]
  refine ⟨228228206491309452418066625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152152137660872968278711083 228228206491309452418066625)
  ·
    refine ⟨171171154868482089313549969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228228206491309452418066625 171171154868482089313549969)
    ·
      refine ⟨128378366151361566985162477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171171154868482089313549969 128378366151361566985162477)
      ·
        refine ⟨48141887306760587619435929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128378366151361566985162477 48141887306760587619435929)
        ·
          refine ⟨36106415480070440714576947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48141887306760587619435929 36106415480070440714576947)
          ·
            refine ⟨54159623220105661071865421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36106415480070440714576947 54159623220105661071865421)
            ·
              refine ⟨20309858707539622901949533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54159623220105661071865421 20309858707539622901949533)
              ·
                refine ⟨7616197015327358588231075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20309858707539622901949533 7616197015327358588231075)
                ·
                  refine ⟨11424295522991037882346613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7616197015327358588231075 11424295522991037882346613)
                  ·
                    refine ⟨1071027705280409801469995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11424295522991037882346613 1071027705280409801469995)
                    ·
                      rfl

theorem cell23_6257457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_6257457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257457 prefixEnd_6257457 := by exact prefixLift 6257457
  have htrace : WordTrace (prefixWord ++ tailWord_6257457) baseStart_6257457 baseEnd_6257457 := by
    simpa [prefixWord, tailWord_6257457, baseEnd_6257457] using wordTrace_append hprefix tailTrace_6257457
  have hstable : (prefixWord ++ tailWord_6257457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257457).length < 2 ^ (prefixWord ++ tailWord_6257457).sum := by decide
  have hdescent : baseEnd_6257457 < baseStart_6257457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257471 : List Nat := [1, 1, 2, 2, 5, 1, 2, 4, 1, 1, 3]
def baseStart_6257471 : Nat := 118140960795 + 6257471 * 2 ^ 59
def prefixEnd_6257471 : Nat := 4983230072969 + 3 ^ 40 * 6257471 * 2
def baseEnd_6257471 : Nat := 3213090304570392349634921

theorem tailTrace_6257471 : CollatzResearch.WordTrace tailWord_6257471 prefixEnd_6257471 3213090304570392349634921 := by
  unfold tailWord_6257471
  simp only [CollatzResearch.WordTrace]
  refine ⟨228228717113258732809076267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152152478075505821872717511 228228717113258732809076267)
  ·
    refine ⟨342343075669888099213614401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228228717113258732809076267 342343075669888099213614401)
    ·
      refine ⟨256757306752416074410210801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342343075669888099213614401 256757306752416074410210801)
      ·
        refine ⟨192567980064312055807658101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256757306752416074410210801 192567980064312055807658101)
        ·
          refine ⟨18053248131029255231967947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192567980064312055807658101 18053248131029255231967947)
          ·
            refine ⟨27079872196543882847951921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18053248131029255231967947 27079872196543882847951921)
            ·
              refine ⟨20309904147407912135963941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27079872196543882847951921 20309904147407912135963941)
              ·
                refine ⟨3808107027638983525493239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20309904147407912135963941 3808107027638983525493239)
                ·
                  refine ⟨5712160541458475288239859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3808107027638983525493239 5712160541458475288239859)
                  ·
                    refine ⟨8568240812187712932359789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5712160541458475288239859 8568240812187712932359789)
                    ·
                      refine ⟨3213090304570392349634921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8568240812187712932359789 3213090304570392349634921)
                      ·
                        rfl

theorem cell23_6257471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 1, 1, 3].length) (baseStart_6257471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257471 prefixEnd_6257471 := by exact prefixLift 6257471
  have htrace : WordTrace (prefixWord ++ tailWord_6257471) baseStart_6257471 baseEnd_6257471 := by
    simpa [prefixWord, tailWord_6257471, baseEnd_6257471] using wordTrace_append hprefix tailTrace_6257471
  have hstable : (prefixWord ++ tailWord_6257471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257471).length < 2 ^ (prefixWord ++ tailWord_6257471).sum := by decide
  have hdescent : baseEnd_6257471 < baseStart_6257471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257478 : List Nat := [6, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_6257478 : Nat := 118140960795 + 6257478 * 2 ^ 59
def prefixEnd_6257478 : Nat := 4983230072969 + 3 ^ 40 * 6257478 * 2
def baseEnd_6257478 : Nat := 357010433214997091360821

theorem tailTrace_6257478 : CollatzResearch.WordTrace tailWord_6257478 prefixEnd_6257478 357010433214997091360821 := by
  unfold tailWord_6257478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7132155388257292906393159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152152648282822248669720725 7132155388257292906393159)
  ·
    refine ⟨10698233082385939359589739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7132155388257292906393159 10698233082385939359589739)
    ·
      refine ⟨16047349623578909039384609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10698233082385939359589739 16047349623578909039384609)
      ·
        refine ⟨12035512217684181779538457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16047349623578909039384609 12035512217684181779538457)
        ·
          refine ⟨9026634163263136334653843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12035512217684181779538457 9026634163263136334653843)
          ·
            refine ⟨13539951244894704501980765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9026634163263136334653843 13539951244894704501980765)
            ·
              refine ⟨5077481716835514188242787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13539951244894704501980765 5077481716835514188242787)
              ·
                refine ⟨7616222575253271282364181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5077481716835514188242787 7616222575253271282364181)
                ·
                  refine ⟨357010433214997091360821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7616222575253271282364181 357010433214997091360821)
                  ·
                    rfl

theorem cell23_6257478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_6257478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257478 prefixEnd_6257478 := by exact prefixLift 6257478
  have htrace : WordTrace (prefixWord ++ tailWord_6257478) baseStart_6257478 baseEnd_6257478 := by
    simpa [prefixWord, tailWord_6257478, baseEnd_6257478] using wordTrace_append hprefix tailTrace_6257478
  have hstable : (prefixWord ++ tailWord_6257478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257478).length < 2 ^ (prefixWord ++ tailWord_6257478).sum := by decide
  have hdescent : baseEnd_6257478 < baseStart_6257478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257530 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 2, 7]
def baseStart_6257530 : Nat := 118140960795 + 6257530 * 2 ^ 59
def prefixEnd_6257530 : Nat := 4983230072969 + 3 ^ 40 * 6257530 * 2
def baseEnd_6257530 : Nat := 1071040199976335872932383

theorem tailTrace_6257530 : CollatzResearch.WordTrace tailWord_6257530 prefixEnd_6257530 1071040199976335872932383 := by
  unfold tailWord_6257530
  simp only [CollatzResearch.WordTrace]
  refine ⟨57057717255011246471368511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152153912680029990590316029 57057717255011246471368511)
  ·
    refine ⟨85586575882516869707052767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57057717255011246471368511 85586575882516869707052767)
    ·
      refine ⟨128379863823775304560579151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85586575882516869707052767 128379863823775304560579151)
      ·
        refine ⟨192569795735662956840868727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128379863823775304560579151 192569795735662956840868727)
        ·
          refine ⟨288854693603494435261303091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192569795735662956840868727 288854693603494435261303091)
          ·
            refine ⟨433282040405241652891954637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288854693603494435261303091 433282040405241652891954637)
            ·
              refine ⟨162480765151965619834482989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433282040405241652891954637 162480765151965619834482989)
              ·
                refine ⟨60930286931987107437931121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162480765151965619834482989 60930286931987107437931121)
                ·
                  refine ⟨45697715198990330578448341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60930286931987107437931121 45697715198990330578448341)
                  ·
                    refine ⟨1071040199976335872932383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45697715198990330578448341 1071040199976335872932383)
                    ·
                      rfl

theorem cell23_6257530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_6257530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257530 prefixEnd_6257530 := by exact prefixLift 6257530
  have htrace : WordTrace (prefixWord ++ tailWord_6257530) baseStart_6257530 baseEnd_6257530 := by
    simpa [prefixWord, tailWord_6257530, baseEnd_6257530] using wordTrace_append hprefix tailTrace_6257530
  have hstable : (prefixWord ++ tailWord_6257530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257530).length < 2 ^ (prefixWord ++ tailWord_6257530).sum := by decide
  have hdescent : baseEnd_6257530 < baseStart_6257530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257558 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_6257558 : Nat := 118140960795 + 6257558 * 2 ^ 59
def prefixEnd_6257558 : Nat := 4983230072969 + 3 ^ 40 * 6257558 * 2
def baseEnd_6257558 : Nat := 3213134977387333509247021

theorem tailTrace_6257558 : CollatzResearch.WordTrace tailWord_6257558 prefixEnd_6257558 3213134977387333509247021 := by
  unfold tailWord_6257558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14264493141496471666718333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152154593509295697778328885 14264493141496471666718333)
  ·
    refine ⟨5349184928061176875019375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14264493141496471666718333 5349184928061176875019375)
    ·
      refine ⟨8023777392091765312529063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5349184928061176875019375 8023777392091765312529063)
      ·
        refine ⟨12035666088137647968793595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8023777392091765312529063 12035666088137647968793595)
        ·
          refine ⟨18053499132206471953190393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12035666088137647968793595 18053499132206471953190393)
          ·
            refine ⟨13540124349154853964892795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18053499132206471953190393 13540124349154853964892795)
            ·
              refine ⟨20310186523732280947339193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13540124349154853964892795 20310186523732280947339193)
              ·
                refine ⟨15232639892799210710504395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20310186523732280947339193 15232639892799210710504395)
                ·
                  refine ⟨22848959839198816065756593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15232639892799210710504395 22848959839198816065756593)
                  ·
                    refine ⟨17136719879399112049317445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22848959839198816065756593 17136719879399112049317445)
                    ·
                      refine ⟨3213134977387333509247021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17136719879399112049317445 3213134977387333509247021)
                      ·
                        rfl

theorem cell23_6257558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_6257558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257558 prefixEnd_6257558 := by exact prefixLift 6257558
  have htrace : WordTrace (prefixWord ++ tailWord_6257558) baseStart_6257558 baseEnd_6257558 := by
    simpa [prefixWord, tailWord_6257558, baseEnd_6257558] using wordTrace_append hprefix tailTrace_6257558
  have hstable : (prefixWord ++ tailWord_6257558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257558).length < 2 ^ (prefixWord ++ tailWord_6257558).sum := by decide
  have hdescent : baseEnd_6257558 < baseStart_6257558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257588 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_6257588 : Nat := 118140960795 + 6257588 * 2 ^ 59
def prefixEnd_6257588 : Nat := 4983230072969 + 3 ^ 40 * 6257588 * 2
def baseEnd_6257588 : Nat := 3213150381806968391871883

theorem tailTrace_6257588 : CollatzResearch.WordTrace tailWord_6257588 prefixEnd_6257588 3213150381806968391871883 := by
  unfold tailWord_6257588
  simp only [CollatzResearch.WordTrace]
  refine ⟨114116492226917430895542709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152155322969223241194056945 114116492226917430895542709)
  ·
    refine ⟨10698421146273509146457129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114116492226917430895542709 10698421146273509146457129)
    ·
      refine ⟨8023815859705131859842847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10698421146273509146457129 8023815859705131859842847)
      ·
        refine ⟨12035723789557697789764271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8023815859705131859842847 12035723789557697789764271)
        ·
          refine ⟨18053585684336546684646407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12035723789557697789764271 18053585684336546684646407)
          ·
            refine ⟨27080378526504820026969611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18053585684336546684646407 27080378526504820026969611)
            ·
              refine ⟨40620567789757230040454417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27080378526504820026969611 40620567789757230040454417)
              ·
                refine ⟨30465425842317922530340813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40620567789757230040454417 30465425842317922530340813)
                ·
                  refine ⟨11424534690869220948877805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30465425842317922530340813 11424534690869220948877805)
                  ·
                    refine ⟨4284200509075957855829177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11424534690869220948877805 4284200509075957855829177)
                    ·
                      refine ⟨3213150381806968391871883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4284200509075957855829177 3213150381806968391871883)
                      ·
                        rfl

theorem cell23_6257588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_6257588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257588 prefixEnd_6257588 := by exact prefixLift 6257588
  have htrace : WordTrace (prefixWord ++ tailWord_6257588) baseStart_6257588 baseEnd_6257588 := by
    simpa [prefixWord, tailWord_6257588, baseEnd_6257588] using wordTrace_append hprefix tailTrace_6257588
  have hstable : (prefixWord ++ tailWord_6257588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257588).length < 2 ^ (prefixWord ++ tailWord_6257588).sum := by decide
  have hdescent : baseEnd_6257588 < baseStart_6257588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257617 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 1, 5, 3]
def baseStart_6257617 : Nat := 118140960795 + 6257617 * 2 ^ 59
def prefixEnd_6257617 : Nat := 4983230072969 + 3 ^ 40 * 6257617 * 2
def baseEnd_6257617 : Nat := 3213165272745948778409249

theorem tailTrace_6257617 : CollatzResearch.WordTrace tailWord_6257617 prefixEnd_6257617 3213165272745948778409249 := by
  unfold tailWord_6257617
  simp only [CollatzResearch.WordTrace]
  refine ⟨228234042170729799743891105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152156028113819866495927403 228234042170729799743891105)
  ·
    refine ⟨171175531628047349807918329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228234042170729799743891105 171175531628047349807918329)
    ·
      refine ⟨128381648721035512355938747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171175531628047349807918329 128381648721035512355938747)
      ·
        refine ⟨192572473081553268533908121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128381648721035512355938747 192572473081553268533908121)
        ·
          refine ⟨144429354811164951400431091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192572473081553268533908121 144429354811164951400431091)
          ·
            refine ⟨216644032216747427100646637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144429354811164951400431091 216644032216747427100646637)
            ·
              refine ⟨81241512081280285162742489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216644032216747427100646637 81241512081280285162742489)
              ·
                refine ⟨60931134060960213872056867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81241512081280285162742489 60931134060960213872056867)
                ·
                  refine ⟨91396701091440320808085301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60931134060960213872056867 91396701091440320808085301)
                  ·
                    refine ⟨8568440727322530075757997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91396701091440320808085301 8568440727322530075757997)
                    ·
                      refine ⟨3213165272745948778409249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8568440727322530075757997 3213165272745948778409249)
                      ·
                        rfl

theorem cell23_6257617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_6257617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257617 prefixEnd_6257617 := by exact prefixLift 6257617
  have htrace : WordTrace (prefixWord ++ tailWord_6257617) baseStart_6257617 baseEnd_6257617 := by
    simpa [prefixWord, tailWord_6257617, baseEnd_6257617] using wordTrace_append hprefix tailTrace_6257617
  have hstable : (prefixWord ++ tailWord_6257617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257617).length < 2 ^ (prefixWord ++ tailWord_6257617).sum := by decide
  have hdescent : baseEnd_6257617 < baseStart_6257617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257622 : List Nat := [5, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_6257622 : Nat := 118140960795 + 6257622 * 2 ^ 59
def prefixEnd_6257622 : Nat := 4983230072969 + 3 ^ 40 * 6257622 * 2
def baseEnd_6257622 : Nat := 3213167840149221258846727

theorem tailTrace_6257622 : CollatzResearch.WordTrace tailWord_6257622 prefixEnd_6257622 3213167840149221258846727 := by
  unfold tailWord_6257622
  simp only [CollatzResearch.WordTrace]
  refine ⟨14264639033481980349863945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152156149690474457065215413 14264639033481980349863945)
  ·
    refine ⟨10698479275111485262397959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14264639033481980349863945 10698479275111485262397959)
    ·
      refine ⟨16047718912667227893596939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10698479275111485262397959 16047718912667227893596939)
      ·
        refine ⟨24071578369000841840395409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16047718912667227893596939 24071578369000841840395409)
        ·
          refine ⟨18053683776750631380296557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24071578369000841840395409 18053683776750631380296557)
          ·
            refine ⟨6770131416281486767611209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18053683776750631380296557 6770131416281486767611209)
            ·
              refine ⟨5077598562211115075708407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6770131416281486767611209 5077598562211115075708407)
              ·
                refine ⟨7616397843316672613562611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5077598562211115075708407 7616397843316672613562611)
                ·
                  refine ⟨11424596764975008920343917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7616397843316672613562611 11424596764975008920343917)
                  ·
                    refine ⟨4284223786865628345128969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11424596764975008920343917 4284223786865628345128969)
                    ·
                      refine ⟨3213167840149221258846727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4284223786865628345128969 3213167840149221258846727)
                      ·
                        rfl

theorem cell23_6257622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_6257622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257622 prefixEnd_6257622 := by exact prefixLift 6257622
  have htrace : WordTrace (prefixWord ++ tailWord_6257622) baseStart_6257622 baseEnd_6257622 := by
    simpa [prefixWord, tailWord_6257622, baseEnd_6257622] using wordTrace_append hprefix tailTrace_6257622
  have hstable : (prefixWord ++ tailWord_6257622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257622).length < 2 ^ (prefixWord ++ tailWord_6257622).sum := by decide
  have hdescent : baseEnd_6257622 < baseStart_6257622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257624 : List Nat := [2, 1, 2, 2, 2, 3, 1, 5, 5]
def baseStart_6257624 : Nat := 118140960795 + 6257624 * 2 ^ 59
def prefixEnd_6257624 : Nat := 4983230072969 + 3 ^ 40 * 6257624 * 2
def baseEnd_6257624 : Nat := 357018763012281139002413

theorem tailTrace_6257624 : CollatzResearch.WordTrace tailWord_6257624 prefixEnd_6257624 357018763012281139002413 := by
  unfold tailWord_6257624
  simp only [CollatzResearch.WordTrace]
  refine ⟨114117148740852219969697963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152156198321136293292930617 114117148740852219969697963)
  ·
    refine ⟨171175723111278329954546945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114117148740852219969697963 171175723111278329954546945)
    ·
      refine ⟨128381792333458747465910209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171175723111278329954546945 128381792333458747465910209)
      ·
        refine ⟨96286344250094060599432657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128381792333458747465910209 96286344250094060599432657)
        ·
          refine ⟨72214758187570545449574493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96286344250094060599432657 72214758187570545449574493)
          ·
            refine ⟨27080534320338954543590435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72214758187570545449574493 27080534320338954543590435)
            ·
              refine ⟨40620801480508431815385653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27080534320338954543590435 40620801480508431815385653)
              ·
                refine ⟨3808200138797665482692405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40620801480508431815385653 3808200138797665482692405)
                ·
                  refine ⟨357018763012281139002413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3808200138797665482692405 357018763012281139002413)
                  ·
                    rfl

theorem cell23_6257624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 5].length) (baseStart_6257624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257624 prefixEnd_6257624 := by exact prefixLift 6257624
  have htrace : WordTrace (prefixWord ++ tailWord_6257624) baseStart_6257624 baseEnd_6257624 := by
    simpa [prefixWord, tailWord_6257624, baseEnd_6257624] using wordTrace_append hprefix tailTrace_6257624
  have hstable : (prefixWord ++ tailWord_6257624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257624).length < 2 ^ (prefixWord ++ tailWord_6257624).sum := by decide
  have hdescent : baseEnd_6257624 < baseStart_6257624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257654 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_6257654 : Nat := 118140960795 + 6257654 * 2 ^ 59
def prefixEnd_6257654 : Nat := 4983230072969 + 3 ^ 40 * 6257654 * 2
def baseEnd_6257654 : Nat := 1071061423843388377882193

theorem tailTrace_6257654 : CollatzResearch.WordTrace tailWord_6257654 prefixEnd_6257654 1071061423843388377882193 := by
  unfold tailWord_6257654
  simp only [CollatzResearch.WordTrace]
  refine ⟨14264711979474734691436751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152156927781063836708658677 14264711979474734691436751)
  ·
    refine ⟨21397067969212102037155127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14264711979474734691436751 21397067969212102037155127)
    ·
      refine ⟨32095601953818153055732691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21397067969212102037155127 32095601953818153055732691)
      ·
        refine ⟨48143402930727229583599037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32095601953818153055732691 48143402930727229583599037)
        ·
          refine ⟨18053776099022711093849639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48143402930727229583599037 18053776099022711093849639)
          ·
            refine ⟨27080664148534066640774459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18053776099022711093849639 27080664148534066640774459)
            ·
              refine ⟨40620996222801099961161689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27080664148534066640774459 40620996222801099961161689)
              ·
                refine ⟨30465747167100824970871267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40620996222801099961161689 30465747167100824970871267)
                ·
                  refine ⟨45698620750651237456306901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30465747167100824970871267 45698620750651237456306901)
                  ·
                    refine ⟨1071061423843388377882193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45698620750651237456306901 1071061423843388377882193)
                    ·
                      rfl

theorem cell23_6257654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_6257654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257654 prefixEnd_6257654 := by exact prefixLift 6257654
  have htrace : WordTrace (prefixWord ++ tailWord_6257654) baseStart_6257654 baseEnd_6257654 := by
    simpa [prefixWord, tailWord_6257654, baseEnd_6257654] using wordTrace_append hprefix tailTrace_6257654
  have hstable : (prefixWord ++ tailWord_6257654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257654).length < 2 ^ (prefixWord ++ tailWord_6257654).sum := by decide
  have hdescent : baseEnd_6257654 < baseStart_6257654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257657 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 3, 3, 4]
def baseStart_6257657 : Nat := 118140960795 + 6257657 * 2 ^ 59
def prefixEnd_6257657 : Nat := 4983230072969 + 3 ^ 40 * 6257657 * 2
def baseEnd_6257657 : Nat := 3213185811972128621909065

theorem tailTrace_6257657 : CollatzResearch.WordTrace tailWord_6257657 prefixEnd_6257657 3213185811972128621909065 := by
  unfold tailWord_6257657
  simp only [CollatzResearch.WordTrace]
  refine ⟨228235501090584886575347225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152157000727056591050231483 228235501090584886575347225)
  ·
    refine ⟨171176625817938664931510419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228235501090584886575347225 171176625817938664931510419)
    ·
      refine ⟨256764938726907997397265629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171176625817938664931510419 256764938726907997397265629)
      ·
        refine ⟨96286852022590499023974611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256764938726907997397265629 96286852022590499023974611)
        ·
          refine ⟨144430278033885748535961917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96286852022590499023974611 144430278033885748535961917)
          ·
            refine ⟨54161354262707155700985719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144430278033885748535961917 54161354262707155700985719)
            ·
              refine ⟨81242031394060733551478579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54161354262707155700985719 81242031394060733551478579)
              ·
                refine ⟨121863047091091100327217869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81242031394060733551478579 121863047091091100327217869)
                ·
                  refine ⟨45698642659159162622706701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121863047091091100327217869 45698642659159162622706701)
                  ·
                    refine ⟨17136990997184685983515013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45698642659159162622706701 17136990997184685983515013)
                    ·
                      refine ⟨3213185811972128621909065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17136990997184685983515013 3213185811972128621909065)
                      ·
                        rfl

theorem cell23_6257657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_6257657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257657 prefixEnd_6257657 := by exact prefixLift 6257657
  have htrace : WordTrace (prefixWord ++ tailWord_6257657) baseStart_6257657 baseEnd_6257657 := by
    simpa [prefixWord, tailWord_6257657, baseEnd_6257657] using wordTrace_append hprefix tailTrace_6257657
  have hstable : (prefixWord ++ tailWord_6257657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257657).length < 2 ^ (prefixWord ++ tailWord_6257657).sum := by decide
  have hdescent : baseEnd_6257657 < baseStart_6257657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257674 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_6257674 : Nat := 118140960795 + 6257674 * 2 ^ 59
def prefixEnd_6257674 : Nat := 4983230072969 + 3 ^ 40 * 6257674 * 2
def baseEnd_6257674 : Nat := 3213194541143255055396487

theorem tailTrace_6257674 : CollatzResearch.WordTrace tailWord_6257674 prefixEnd_6257674 3213194541143255055396487 := by
  unfold tailWord_6257674
  simp only [CollatzResearch.WordTrace]
  refine ⟨57059030282880824619679019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152157414087682198985810717 57059030282880824619679019)
  ·
    refine ⟨85588545424321236929518529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57059030282880824619679019 85588545424321236929518529)
    ·
      refine ⟨64191409068240927697138897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85588545424321236929518529 64191409068240927697138897)
      ·
        refine ⟨48143556801180695772854173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64191409068240927697138897 48143556801180695772854173)
        ·
          refine ⟨18053833800442760914820315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48143556801180695772854173 18053833800442760914820315)
          ·
            refine ⟨27080750700664141372230473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18053833800442760914820315 27080750700664141372230473)
            ·
              refine ⟨20310563025498106029172855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27080750700664141372230473 20310563025498106029172855)
              ·
                refine ⟨30465844538247159043759283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20310563025498106029172855 30465844538247159043759283)
                ·
                  refine ⟨45698766807370738565638925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30465844538247159043759283 45698766807370738565638925)
                  ·
                    refine ⟨17137037552764026962114597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45698766807370738565638925 17137037552764026962114597)
                    ·
                      refine ⟨3213194541143255055396487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17137037552764026962114597 3213194541143255055396487)
                      ·
                        rfl

theorem cell23_6257674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_6257674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257674 prefixEnd_6257674 := by exact prefixLift 6257674
  have htrace : WordTrace (prefixWord ++ tailWord_6257674) baseStart_6257674 baseEnd_6257674 := by
    simpa [prefixWord, tailWord_6257674, baseEnd_6257674] using wordTrace_append hprefix tailTrace_6257674
  have hstable : (prefixWord ++ tailWord_6257674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257674).length < 2 ^ (prefixWord ++ tailWord_6257674).sum := by decide
  have hdescent : baseEnd_6257674 < baseStart_6257674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257714 : List Nat := [3, 2, 1, 1, 2, 2, 3, 3, 6]
def baseStart_6257714 : Nat := 118140960795 + 6257714 * 2 ^ 59
def prefixEnd_6257714 : Nat := 4983230072969 + 3 ^ 40 * 6257714 * 2
def baseEnd_6257714 : Nat := 357023897818826099877367

theorem tailTrace_6257714 : CollatzResearch.WordTrace tailWord_6257714 prefixEnd_6257714 357023897818826099877367 := by
  unfold tailWord_6257714
  simp only [CollatzResearch.WordTrace]
  refine ⟨57059395012844596327543049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152158386700918923540114797 57059395012844596327543049)
  ·
    refine ⟨42794546259633447245657287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57059395012844596327543049 42794546259633447245657287)
    ·
      refine ⟨64191819389450170868485931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42794546259633447245657287 64191819389450170868485931)
      ·
        refine ⟨96287729084175256302728897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64191819389450170868485931 96287729084175256302728897)
        ·
          refine ⟨72215796813131442227046673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96287729084175256302728897 72215796813131442227046673)
          ·
            refine ⟨54161847609848581670285005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72215796813131442227046673 54161847609848581670285005)
            ·
              refine ⟨20310692853693218126356877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54161847609848581670285005 20310692853693218126356877)
              ·
                refine ⟨7616509820134956797383829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20310692853693218126356877 7616509820134956797383829)
                ·
                  refine ⟨357023897818826099877367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7616509820134956797383829 357023897818826099877367)
                  ·
                    rfl

theorem cell23_6257714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_6257714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257714 prefixEnd_6257714 := by exact prefixLift 6257714
  have htrace : WordTrace (prefixWord ++ tailWord_6257714) baseStart_6257714 baseEnd_6257714 := by
    simpa [prefixWord, tailWord_6257714, baseEnd_6257714] using wordTrace_append hprefix tailTrace_6257714
  have hstable : (prefixWord ++ tailWord_6257714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257714).length < 2 ^ (prefixWord ++ tailWord_6257714).sum := by decide
  have hdescent : baseEnd_6257714 < baseStart_6257714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257737 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 2, 4, 5]
def baseStart_6257737 : Nat := 118140960795 + 6257737 * 2 ^ 59
def prefixEnd_6257737 : Nat := 4983230072969 + 3 ^ 40 * 6257737 * 2
def baseEnd_6257737 : Nat := 3213226890424488308908697

theorem tailTrace_6257737 : CollatzResearch.WordTrace tailWord_6257737 prefixEnd_6257737 3213226890424488308908697 := by
  unfold tailWord_6257737
  simp only [CollatzResearch.WordTrace]
  refine ⟨228238418930295060238259465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152158945953530040158839643 228238418930295060238259465)
  ·
    refine ⟨171178814197721295178694599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228238418930295060238259465 171178814197721295178694599)
    ·
      refine ⟨256768221296581942768041899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171178814197721295178694599 256768221296581942768041899)
      ·
        refine ⟨385152331944872914152062849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256768221296581942768041899 385152331944872914152062849)
        ·
          refine ⟨288864248958654685614047137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385152331944872914152062849 288864248958654685614047137)
          ·
            refine ⟨216648186718991014210535353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288864248958654685614047137 216648186718991014210535353)
            ·
              refine ⟨162486140039243260657901515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216648186718991014210535353 162486140039243260657901515)
              ·
                refine ⟨243729210058864890986852273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162486140039243260657901515 243729210058864890986852273)
                ·
                  refine ⟨182796907544148668240139205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243729210058864890986852273 182796907544148668240139205)
                  ·
                    refine ⟨34274420164527875295026101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 182796907544148668240139205 34274420164527875295026101)
                    ·
                      refine ⟨3213226890424488308908697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34274420164527875295026101 3213226890424488308908697)
                      ·
                        rfl

theorem cell23_6257737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_6257737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257737 prefixEnd_6257737 := by exact prefixLift 6257737
  have htrace : WordTrace (prefixWord ++ tailWord_6257737) baseStart_6257737 baseEnd_6257737 := by
    simpa [prefixWord, tailWord_6257737, baseEnd_6257737] using wordTrace_append hprefix tailTrace_6257737
  have hstable : (prefixWord ++ tailWord_6257737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257737).length < 2 ^ (prefixWord ++ tailWord_6257737).sum := by decide
  have hdescent : baseEnd_6257737 < baseStart_6257737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257744 : List Nat := [2, 1, 1, 1, 1, 3, 1, 7, 1, 5]
def baseStart_6257744 : Nat := 118140960795 + 6257744 * 2 ^ 59
def prefixEnd_6257744 : Nat := 4983230072969 + 3 ^ 40 * 6257744 * 2
def baseEnd_6257744 : Nat := 1071076828263023260507055

theorem tailTrace_6257744 : CollatzResearch.WordTrace tailWord_6257744 prefixEnd_6257744 1071076828263023260507055 := by
  unfold tailWord_6257744
  simp only [CollatzResearch.WordTrace]
  refine ⟨114119337120634850216882143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152159116160846466955842857 114119337120634850216882143)
  ·
    refine ⟨171179005680952275325323215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114119337120634850216882143 171179005680952275325323215)
    ·
      refine ⟨256768508521428412987984823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171179005680952275325323215 256768508521428412987984823)
      ·
        refine ⟨385152762782142619481977235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256768508521428412987984823 385152762782142619481977235)
        ·
          refine ⟨577729144173213929222965853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385152762782142619481977235 577729144173213929222965853)
          ·
            refine ⟨216648429064955223458612195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 577729144173213929222965853 216648429064955223458612195)
            ·
              refine ⟨324972643597432835187918293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216648429064955223458612195 324972643597432835187918293)
              ·
                refine ⟨7616546334314832074716835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 324972643597432835187918293 7616546334314832074716835)
                ·
                  refine ⟨11424819501472248112075253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7616546334314832074716835 11424819501472248112075253)
                  ·
                    refine ⟨1071076828263023260507055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11424819501472248112075253 1071076828263023260507055)
                    ·
                      rfl

theorem cell23_6257744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 1, 5].length) (baseStart_6257744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257744 prefixEnd_6257744 := by exact prefixLift 6257744
  have htrace : WordTrace (prefixWord ++ tailWord_6257744) baseStart_6257744 baseEnd_6257744 := by
    simpa [prefixWord, tailWord_6257744, baseEnd_6257744] using wordTrace_append hprefix tailTrace_6257744
  have hstable : (prefixWord ++ tailWord_6257744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257744).length < 2 ^ (prefixWord ++ tailWord_6257744).sum := by decide
  have hdescent : baseEnd_6257744 < baseStart_6257744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257785 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 2, 3, 2]
def baseStart_6257785 : Nat := 118140960795 + 6257785 * 2 ^ 59
def prefixEnd_6257785 : Nat := 4983230072969 + 3 ^ 40 * 6257785 * 2
def baseEnd_6257785 : Nat := 3213251537495904121108477

theorem tailTrace_6257785 : CollatzResearch.WordTrace tailWord_6257785 prefixEnd_6257785 3213251537495904121108477 := by
  unfold tailWord_6257785
  simp only [CollatzResearch.WordTrace]
  refine ⟨228240169634121164436006809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152160113089414109624004539 228240169634121164436006809)
  ·
    refine ⟨171180127225590873327005107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228240169634121164436006809 171180127225590873327005107)
    ·
      refine ⟨256770190838386309990507661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171180127225590873327005107 256770190838386309990507661)
      ·
        refine ⟨96288821564394866246440373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256770190838386309990507661 96288821564394866246440373)
        ·
          refine ⟨9027077021662018710603785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96288821564394866246440373 9027077021662018710603785)
          ·
            refine ⟨6770307766246514032952839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9027077021662018710603785 6770307766246514032952839)
            ·
              refine ⟨10155461649369771049429259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6770307766246514032952839 10155461649369771049429259)
              ·
                refine ⟨15233192474054656574143889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10155461649369771049429259 15233192474054656574143889)
                ·
                  refine ⟨11424894355540992430607917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15233192474054656574143889 11424894355540992430607917)
                  ·
                    refine ⟨4284335383327872161477969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11424894355540992430607917 4284335383327872161477969)
                    ·
                      refine ⟨3213251537495904121108477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4284335383327872161477969 3213251537495904121108477)
                      ·
                        rfl

theorem cell23_6257785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_6257785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257785 prefixEnd_6257785 := by exact prefixLift 6257785
  have htrace : WordTrace (prefixWord ++ tailWord_6257785) baseStart_6257785 baseEnd_6257785 := by
    simpa [prefixWord, tailWord_6257785, baseEnd_6257785] using wordTrace_append hprefix tailTrace_6257785
  have hstable : (prefixWord ++ tailWord_6257785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257785).length < 2 ^ (prefixWord ++ tailWord_6257785).sum := by decide
  have hdescent : baseEnd_6257785 < baseStart_6257785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257787 : List Nat := [1, 1, 1, 1, 1, 4, 1, 13]
def baseStart_6257787 : Nat := 118140960795 + 6257787 * 2 ^ 59
def prefixEnd_6257787 : Nat := 4983230072969 + 3 ^ 40 * 6257787 * 2
def baseEnd_6257787 : Nat := 119009354239156041232721

theorem tailTrace_6257787 : CollatzResearch.WordTrace tailWord_6257787 prefixEnd_6257787 119009354239156041232721 := by
  unfold tailWord_6257787
  simp only [CollatzResearch.WordTrace]
  refine ⟨228240242580113918777579615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152160161720075945851719743 228240242580113918777579615)
  ·
    refine ⟨342360363870170878166369423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228240242580113918777579615 342360363870170878166369423)
    ·
      refine ⟨513540545805256317249554135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342360363870170878166369423 513540545805256317249554135)
      ·
        refine ⟨770310818707884475874331203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513540545805256317249554135 770310818707884475874331203)
        ·
          refine ⟨1155466228061826713811496805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770310818707884475874331203 1155466228061826713811496805)
          ·
            refine ⟨216649917761592508839655651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1155466228061826713811496805 216649917761592508839655651)
            ·
              refine ⟨324974876642388763259483477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216649917761592508839655651 324974876642388763259483477)
              ·
                refine ⟨119009354239156041232721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 324974876642388763259483477 119009354239156041232721)
                ·
                  rfl

theorem cell23_6257787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 13].length) (baseStart_6257787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257787 prefixEnd_6257787 := by exact prefixLift 6257787
  have htrace : WordTrace (prefixWord ++ tailWord_6257787) baseStart_6257787 baseEnd_6257787 := by
    simpa [prefixWord, tailWord_6257787, baseEnd_6257787] using wordTrace_append hprefix tailTrace_6257787
  have hstable : (prefixWord ++ tailWord_6257787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257787).length < 2 ^ (prefixWord ++ tailWord_6257787).sum := by decide
  have hdescent : baseEnd_6257787 < baseStart_6257787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257815 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 3, 2, 2]
def baseStart_6257815 : Nat := 118140960795 + 6257815 * 2 ^ 59
def prefixEnd_6257815 : Nat := 4983230072969 + 3 ^ 40 * 6257815 * 2
def baseEnd_6257815 : Nat := 3213266941915539003733339

theorem tailTrace_6257815 : CollatzResearch.WordTrace tailWord_6257815 prefixEnd_6257815 3213266941915539003733339 := by
  unfold tailWord_6257815
  simp only [CollatzResearch.WordTrace]
  refine ⟨228241263824012479559598899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152160842549341653039732599 228241263824012479559598899)
  ·
    refine ⟨342361895736018719339398349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228241263824012479559598899 342361895736018719339398349)
    ·
      refine ⟨128385710901007019752274381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342361895736018719339398349 128385710901007019752274381)
      ·
        refine ⟨48144641587877632407102893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128385710901007019752274381 48144641587877632407102893)
        ·
          refine ⟨18054240595454112152663585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48144641587877632407102893 18054240595454112152663585)
          ·
            refine ⟨13540680446590584114497689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18054240595454112152663585 13540680446590584114497689)
            ·
              refine ⟨10155510334942938085873267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13540680446590584114497689 10155510334942938085873267)
              ·
                refine ⟨15233265502414407128809901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10155510334942938085873267 15233265502414407128809901)
                ·
                  refine ⟨5712474563405402673303713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15233265502414407128809901 5712474563405402673303713)
                  ·
                    refine ⟨4284355922554052004977785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5712474563405402673303713 4284355922554052004977785)
                    ·
                      refine ⟨3213266941915539003733339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4284355922554052004977785 3213266941915539003733339)
                      ·
                        rfl

theorem cell23_6257815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_6257815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257815 prefixEnd_6257815 := by exact prefixLift 6257815
  have htrace : WordTrace (prefixWord ++ tailWord_6257815) baseStart_6257815 baseEnd_6257815 := by
    simpa [prefixWord, tailWord_6257815, baseEnd_6257815] using wordTrace_append hprefix tailTrace_6257815
  have hstable : (prefixWord ++ tailWord_6257815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257815).length < 2 ^ (prefixWord ++ tailWord_6257815).sum := by decide
  have hdescent : baseEnd_6257815 < baseStart_6257815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257828 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 1, 2, 4]
def baseStart_6257828 : Nat := 118140960795 + 6257828 * 2 ^ 59
def prefixEnd_6257828 : Nat := 4983230072969 + 3 ^ 40 * 6257828 * 2
def baseEnd_6257828 : Nat := 3213273617164047452870779

theorem tailTrace_6257828 : CollatzResearch.WordTrace tailWord_6257828 prefixEnd_6257828 3213273617164047452870779 := by
  unfold tailWord_6257828
  simp only [CollatzResearch.WordTrace]
  refine ⟨114120868986482691389911069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152161158648643588519881425 114120868986482691389911069)
  ·
    refine ⟨42795325869931009271216651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114120868986482691389911069 42795325869931009271216651)
    ·
      refine ⟨64192988804896513906824977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42795325869931009271216651 64192988804896513906824977)
      ·
        refine ⟨48144741603672385430118733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64192988804896513906824977 48144741603672385430118733)
        ·
          refine ⟨18054278101377144536294525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48144741603672385430118733 18054278101377144536294525)
          ·
            refine ⟨6770354288016429201110447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18054278101377144536294525 6770354288016429201110447)
            ·
              refine ⟨10155531432024643801665671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6770354288016429201110447 10155531432024643801665671)
              ·
                refine ⟨15233297148036965702498507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10155531432024643801665671 15233297148036965702498507)
                ·
                  refine ⟨22849945722055448553747761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15233297148036965702498507 22849945722055448553747761)
                  ·
                    refine ⟨17137459291541586415310821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22849945722055448553747761 17137459291541586415310821)
                    ·
                      refine ⟨3213273617164047452870779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17137459291541586415310821 3213273617164047452870779)
                      ·
                        rfl

theorem cell23_6257828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_6257828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257828 prefixEnd_6257828 := by exact prefixLift 6257828
  have htrace : WordTrace (prefixWord ++ tailWord_6257828) baseStart_6257828 baseEnd_6257828 := by
    simpa [prefixWord, tailWord_6257828, baseEnd_6257828] using wordTrace_append hprefix tailTrace_6257828
  have hstable : (prefixWord ++ tailWord_6257828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257828).length < 2 ^ (prefixWord ++ tailWord_6257828).sum := by decide
  have hdescent : baseEnd_6257828 < baseStart_6257828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257864 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 4, 6]
def baseStart_6257864 : Nat := 118140960795 + 6257864 * 2 ^ 59
def prefixEnd_6257864 : Nat := 4983230072969 + 3 ^ 40 * 6257864 * 2
def baseEnd_6257864 : Nat := 1071097367489203104006871

theorem tailTrace_6257864 : CollatzResearch.WordTrace tailWord_6257864 prefixEnd_6257864 1071097367489203104006871 := by
  unfold tailWord_6257864
  simp only [CollatzResearch.WordTrace]
  refine ⟨114121525500417480464066323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152162034000556640618755097 114121525500417480464066323)
  ·
    refine ⟨171182288250626220696099485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114121525500417480464066323 171182288250626220696099485)
    ·
      refine ⟨64193358093984832761037307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171182288250626220696099485 64193358093984832761037307)
      ·
        refine ⟨96290037140977249141555961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64193358093984832761037307 96290037140977249141555961)
        ·
          refine ⟨72217527855732936856166971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96290037140977249141555961 72217527855732936856166971)
          ·
            refine ⟨108326291783599405284250457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72217527855732936856166971 108326291783599405284250457)
            ·
              refine ⟨81244718837699553963187843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108326291783599405284250457 81244718837699553963187843)
              ·
                refine ⟨121867078256549330944781765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81244718837699553963187843 121867078256549330944781765)
                ·
                  refine ⟨22850077173102999552146581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121867078256549330944781765 22850077173102999552146581)
                  ·
                    refine ⟨1071097367489203104006871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22850077173102999552146581 1071097367489203104006871)
                    ·
                      rfl

theorem cell23_6257864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_6257864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257864 prefixEnd_6257864 := by exact prefixLift 6257864
  have htrace : WordTrace (prefixWord ++ tailWord_6257864) baseStart_6257864 baseEnd_6257864 := by
    simpa [prefixWord, tailWord_6257864, baseEnd_6257864] using wordTrace_append hprefix tailTrace_6257864
  have hstable : (prefixWord ++ tailWord_6257864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257864).length < 2 ^ (prefixWord ++ tailWord_6257864).sum := by decide
  have hdescent : baseEnd_6257864 < baseStart_6257864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257871 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 5, 4, 2]
def baseStart_6257871 : Nat := 118140960795 + 6257871 * 2 ^ 59
def prefixEnd_6257871 : Nat := 4983230072969 + 3 ^ 40 * 6257871 * 2
def baseEnd_6257871 : Nat := 3213295696832190784633081

theorem tailTrace_6257871 : CollatzResearch.WordTrace tailWord_6257871 prefixEnd_6257871 3213295696832190784633081 := by
  unfold tailWord_6257871
  simp only [CollatzResearch.WordTrace]
  refine ⟨228243306311809601123637467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152162204207873067415758311 228243306311809601123637467)
  ·
    refine ⟨342364959467714401685456201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228243306311809601123637467 342364959467714401685456201)
    ·
      refine ⟨256773719600785801264092151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342364959467714401685456201 256773719600785801264092151)
      ·
        refine ⟨385160579401178701896138227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256773719600785801264092151 385160579401178701896138227)
        ·
          refine ⟨577740869101768052844207341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385160579401178701896138227 577740869101768052844207341)
          ·
            refine ⟨216652825913163019816577753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 577740869101768052844207341 216652825913163019816577753)
            ·
              refine ⟨162489619434872264862433315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216652825913163019816577753 162489619434872264862433315)
              ·
                refine ⟨243734429152308397293649973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162489619434872264862433315 243734429152308397293649973)
                ·
                  refine ⟨22850102733028912246279685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 243734429152308397293649973 22850102733028912246279685)
                  ·
                    refine ⟨4284394262442921046177441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22850102733028912246279685 4284394262442921046177441)
                    ·
                      refine ⟨3213295696832190784633081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4284394262442921046177441 3213295696832190784633081)
                      ·
                        rfl

theorem cell23_6257871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 4, 2].length) (baseStart_6257871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257871 prefixEnd_6257871 := by exact prefixLift 6257871
  have htrace : WordTrace (prefixWord ++ tailWord_6257871) baseStart_6257871 baseEnd_6257871 := by
    simpa [prefixWord, tailWord_6257871, baseEnd_6257871] using wordTrace_append hprefix tailTrace_6257871
  have hstable : (prefixWord ++ tailWord_6257871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257871).length < 2 ^ (prefixWord ++ tailWord_6257871).sum := by decide
  have hdescent : baseEnd_6257871 < baseStart_6257871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6257978 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2]
def baseStart_6257978 : Nat := 118140960795 + 6257978 * 2 ^ 59
def prefixEnd_6257978 : Nat := 4983230072969 + 3 ^ 40 * 6257978 * 2
def baseEnd_6257978 : Nat := 3213350639262221865995089

theorem tailTrace_6257978 : CollatzResearch.WordTrace tailWord_6257978 prefixEnd_6257978 3213350639262221865995089 := by
  unfold tailWord_6257978
  simp only [CollatzResearch.WordTrace]
  refine ⟨57061802230605489599445647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152164805948281305598521725 57061802230605489599445647)
  ·
    refine ⟨85592703345908234399168471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57061802230605489599445647 85592703345908234399168471)
    ·
      refine ⟨128389055018862351598752707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85592703345908234399168471 128389055018862351598752707)
      ·
        refine ⟨192583582528293527398129061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128389055018862351598752707 192583582528293527398129061)
        ·
          refine ⟨36109421724055036387149199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192583582528293527398129061 36109421724055036387149199)
          ·
            refine ⟨54164132586082554580723799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36109421724055036387149199 54164132586082554580723799)
            ·
              refine ⟨81246198879123831871085699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54164132586082554580723799 81246198879123831871085699)
              ·
                refine ⟨121869298318685747806628549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81246198879123831871085699 121869298318685747806628549)
                ·
                  refine ⟨22850493434753577713742853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121869298318685747806628549 22850493434753577713742853)
                  ·
                    refine ⟨4284467519016295821326785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22850493434753577713742853 4284467519016295821326785)
                    ·
                      refine ⟨3213350639262221865995089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4284467519016295821326785 3213350639262221865995089)
                      ·
                        rfl

theorem cell23_6257978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2].length) (baseStart_6257978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6257978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6257978 prefixEnd_6257978 := by exact prefixLift 6257978
  have htrace : WordTrace (prefixWord ++ tailWord_6257978) baseStart_6257978 baseEnd_6257978 := by
    simpa [prefixWord, tailWord_6257978, baseEnd_6257978] using wordTrace_append hprefix tailTrace_6257978
  have hstable : (prefixWord ++ tailWord_6257978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6257978).length < 2 ^ (prefixWord ++ tailWord_6257978).sum := by decide
  have hdescent : baseEnd_6257978 < baseStart_6257978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6257978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258082 : List Nat := [3, 3, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_6258082 : Nat := 118140960795 + 6258082 * 2 ^ 59
def prefixEnd_6258082 : Nat := 4983230072969 + 3 ^ 40 * 6258082 * 2
def baseEnd_6258082 : Nat := 1071134680416763153031537

theorem tailTrace_6258082 : CollatzResearch.WordTrace tailWord_6258082 prefixEnd_6258082 1071134680416763153031537 := by
  unfold tailWord_6258082
  simp only [CollatzResearch.WordTrace]
  refine ⟨57062750528511296039892125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152167334742696789439712333 57062750528511296039892125)
  ·
    refine ⟨21398531448191736014959547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57062750528511296039892125 21398531448191736014959547)
    ·
      refine ⟨32097797172287604022439321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21398531448191736014959547 32097797172287604022439321)
      ·
        refine ⟨24073347879215703016829491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32097797172287604022439321 24073347879215703016829491)
        ·
          refine ⟨36110021818823554525244237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24073347879215703016829491 36110021818823554525244237)
          ·
            refine ⟨13541258182058832946966589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36110021818823554525244237 13541258182058832946966589)
            ·
              refine ⟨5077971818272062355112471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13541258182058832946966589 5077971818272062355112471)
              ·
                refine ⟨7616957727408093532668707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5077971818272062355112471 7616957727408093532668707)
                ·
                  refine ⟨11425436591112140299003061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7616957727408093532668707 11425436591112140299003061)
                  ·
                    refine ⟨1071134680416763153031537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11425436591112140299003061 1071134680416763153031537)
                    ·
                      rfl

theorem cell23_6258082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_6258082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258082 prefixEnd_6258082 := by exact prefixLift 6258082
  have htrace : WordTrace (prefixWord ++ tailWord_6258082) baseStart_6258082 baseEnd_6258082 := by
    simpa [prefixWord, tailWord_6258082, baseEnd_6258082] using wordTrace_append hprefix tailTrace_6258082
  have hstable : (prefixWord ++ tailWord_6258082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258082).length < 2 ^ (prefixWord ++ tailWord_6258082).sum := by decide
  have hdescent : baseEnd_6258082 < baseStart_6258082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258085 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 7, 2, 2]
def baseStart_6258085 : Nat := 118140960795 + 6258085 * 2 ^ 59
def prefixEnd_6258085 : Nat := 4983230072969 + 3 ^ 40 * 6258085 * 2
def baseEnd_6258085 : Nat := 3213405581692252947357097

theorem tailTrace_6258085 : CollatzResearch.WordTrace tailWord_6258085 prefixEnd_6258085 3213405581692252947357097 := by
  unfold tailWord_6258085
  simp only [CollatzResearch.WordTrace]
  refine ⟨228251111533034315671927709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152167407688689543781285139 228251111533034315671927709)
  ·
    refine ⟨85594166824887868376972891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228251111533034315671927709 85594166824887868376972891)
    ·
      refine ⟨128391250237331802565459337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85594166824887868376972891 128391250237331802565459337)
      ·
        refine ⟨96293437677998851924094503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128391250237331802565459337 96293437677998851924094503)
        ·
          refine ⟨144440156516998277886141755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96293437677998851924094503 144440156516998277886141755)
          ·
            refine ⟨216660234775497416829212633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144440156516998277886141755 216660234775497416829212633)
            ·
              refine ⟨162495176081623062621909475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216660234775497416829212633 162495176081623062621909475)
              ·
                refine ⟨243742764122434593932864213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162495176081623062621909475 243742764122434593932864213)
                ·
                  refine ⟨5712721034119560795301505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 243742764122434593932864213 5712721034119560795301505)
                  ·
                    refine ⟨4284540775589670596476129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5712721034119560795301505 4284540775589670596476129)
                    ·
                      refine ⟨3213405581692252947357097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4284540775589670596476129 3213405581692252947357097)
                      ·
                        rfl

theorem cell23_6258085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_6258085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258085 prefixEnd_6258085 := by exact prefixLift 6258085
  have htrace : WordTrace (prefixWord ++ tailWord_6258085) baseStart_6258085 baseEnd_6258085 := by
    simpa [prefixWord, tailWord_6258085, baseEnd_6258085] using wordTrace_append hprefix tailTrace_6258085
  have hstable : (prefixWord ++ tailWord_6258085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258085).length < 2 ^ (prefixWord ++ tailWord_6258085).sum := by decide
  have hdescent : baseEnd_6258085 < baseStart_6258085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258111 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 6]
def baseStart_6258111 : Nat := 118140960795 + 6258111 * 2 ^ 59
def prefixEnd_6258111 : Nat := 4983230072969 + 3 ^ 40 * 6258111 * 2
def baseEnd_6258111 : Nat := 3213418932189269845631977

theorem tailTrace_6258111 : CollatzResearch.WordTrace tailWord_6258111 prefixEnd_6258111 3213418932189269845631977 := by
  unfold tailWord_6258111
  simp only [CollatzResearch.WordTrace]
  refine ⟨228252059830940122112374187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152168039887293414741582791 228252059830940122112374187)
  ·
    refine ⟨342378089746410183168561281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228252059830940122112374187 342378089746410183168561281)
    ·
      refine ⟨256783567309807637376420961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342378089746410183168561281 256783567309807637376420961)
      ·
        refine ⟨192587675482355728032315721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256783567309807637376420961 192587675482355728032315721)
        ·
          refine ⟨144440756611766796024236791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192587675482355728032315721 144440756611766796024236791)
          ·
            refine ⟨216661134917650194036355187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144440756611766796024236791 216661134917650194036355187)
            ·
              refine ⟨324991702376475291054532781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216661134917650194036355187 324991702376475291054532781)
              ·
                refine ⟨121871888391178234145449793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324991702376475291054532781 121871888391178234145449793)
                ·
                  refine ⟨91403916293383675609087345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121871888391178234145449793 91403916293383675609087345)
                  ·
                    refine ⟨68552937220037756706815509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91403916293383675609087345 68552937220037756706815509)
                    ·
                      refine ⟨3213418932189269845631977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68552937220037756706815509 3213418932189269845631977)
                      ·
                        rfl

theorem cell23_6258111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_6258111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258111 prefixEnd_6258111 := by exact prefixLift 6258111
  have htrace : WordTrace (prefixWord ++ tailWord_6258111) baseStart_6258111 baseEnd_6258111 := by
    simpa [prefixWord, tailWord_6258111, baseEnd_6258111] using wordTrace_append hprefix tailTrace_6258111
  have hstable : (prefixWord ++ tailWord_6258111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258111).length < 2 ^ (prefixWord ++ tailWord_6258111).sum := by decide
  have hdescent : baseEnd_6258111 < baseStart_6258111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6258121 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 4, 7]
def baseStart_6258121 : Nat := 118140960795 + 6258121 * 2 ^ 59
def prefixEnd_6258121 : Nat := 4983230072969 + 3 ^ 40 * 6258121 * 2
def baseEnd_6258121 : Nat := 1071141355665271602168977

theorem tailTrace_6258121 : CollatzResearch.WordTrace tailWord_6258121 prefixEnd_6258121 1071141355665271602168977 := by
  unfold tailWord_6258121
  simp only [CollatzResearch.WordTrace]
  refine ⟨228252424560903893820238217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152168283040602595880158811 228252424560903893820238217)
  ·
    refine ⟨171189318420677920365178663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228252424560903893820238217 171189318420677920365178663)
    ·
      refine ⟨256783977631016880547767995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171189318420677920365178663 256783977631016880547767995)
      ·
        refine ⟨385175966446525320821651993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256783977631016880547767995 385175966446525320821651993)
        ·
          refine ⟨288881974834893990616238995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385175966446525320821651993 288881974834893990616238995)
          ·
            refine ⟨433322962252340985924358493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288881974834893990616238995 433322962252340985924358493)
            ·
              refine ⟨162496110844627869721634435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433322962252340985924358493 162496110844627869721634435)
              ·
                refine ⟨243744166266941804582451653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162496110844627869721634435 243744166266941804582451653)
                ·
                  refine ⟨45702031175051588359209685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243744166266941804582451653 45702031175051588359209685)
                  ·
                    refine ⟨1071141355665271602168977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45702031175051588359209685 1071141355665271602168977)
                    ·
                      rfl

theorem cell23_6258121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_6258121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6258121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6258121 prefixEnd_6258121 := by exact prefixLift 6258121
  have htrace : WordTrace (prefixWord ++ tailWord_6258121) baseStart_6258121 baseEnd_6258121 := by
    simpa [prefixWord, tailWord_6258121, baseEnd_6258121] using wordTrace_append hprefix tailTrace_6258121
  have hstable : (prefixWord ++ tailWord_6258121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6258121).length < 2 ^ (prefixWord ++ tailWord_6258121).sum := by decide
  have hdescent : baseEnd_6258121 < baseStart_6258121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6258121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
