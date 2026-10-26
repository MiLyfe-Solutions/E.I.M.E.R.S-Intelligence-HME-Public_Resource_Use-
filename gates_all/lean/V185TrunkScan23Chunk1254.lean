import V185TrunkScan23Chunk1253

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7428205 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_7428205 : Nat := 118140960795 + 7428205 * 2 ^ 59
def prefixEnd_7428205 : Nat := 4983230072969 + 3 ^ 40 * 7428205 * 2
def baseEnd_7428205 : Nat := 1271413188377071615825271

theorem tailTrace_7428205 : CollatzResearch.WordTrace tailWord_7428205 prefixEnd_7428205 1271413188377071615825271 := by
  unfold tailWord_7428205
  simp only [CollatzResearch.WordTrace]
  refine ⟨270928894053889396257806069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180619262702592930838537379 270928894053889396257806069)
  ·
    refine ⟨25399583817552130899169319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 270928894053889396257806069 25399583817552130899169319)
    ·
      refine ⟨38099375726328196348753979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25399583817552130899169319 38099375726328196348753979)
      ·
        refine ⟨57149063589492294523130969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38099375726328196348753979 57149063589492294523130969)
        ·
          refine ⟨42861797692119220892348227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57149063589492294523130969 42861797692119220892348227)
          ·
            refine ⟨64292696538178831338522341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42861797692119220892348227 64292696538178831338522341)
            ·
              refine ⟨12054880600908530875972939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64292696538178831338522341 12054880600908530875972939)
              ·
                refine ⟨18082320901362796313959409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12054880600908530875972939 18082320901362796313959409)
                ·
                  refine ⟨13561740676022097235469557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18082320901362796313959409 13561740676022097235469557)
                  ·
                    refine ⟨1271413188377071615825271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13561740676022097235469557 1271413188377071615825271)
                    ·
                      rfl

theorem cell23_7428205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_7428205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428205 prefixEnd_7428205 := by exact prefixLift 7428205
  have htrace : WordTrace (prefixWord ++ tailWord_7428205) baseStart_7428205 baseEnd_7428205 := by
    simpa [prefixWord, tailWord_7428205, baseEnd_7428205] using wordTrace_append hprefix tailTrace_7428205
  have hstable : (prefixWord ++ tailWord_7428205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428205).length < 2 ^ (prefixWord ++ tailWord_7428205).sum := by decide
  have hdescent : baseEnd_7428205 < baseStart_7428205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428211 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 11]
def baseStart_7428211 : Nat := 118140960795 + 7428211 * 2 ^ 59
def prefixEnd_7428211 : Nat := 4983230072969 + 3 ^ 40 * 7428211 * 2
def baseEnd_7428211 : Nat := 3814242646015141824000785

theorem tailTrace_7428211 : CollatzResearch.WordTrace tailWord_7428211 prefixEnd_7428211 3814242646015141824000785 := by
  unfold tailWord_7428211
  simp only [CollatzResearch.WordTrace]
  refine ⟨270929112891867659282524487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180619408594578439521682991 270929112891867659282524487)
  ·
    refine ⟨406393669337801488923786731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270929112891867659282524487 406393669337801488923786731)
    ·
      refine ⟨609590504006702233385680097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406393669337801488923786731 609590504006702233385680097)
      ·
        refine ⟨457192878005026675039260073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609590504006702233385680097 457192878005026675039260073)
        ·
          refine ⟨342894658503770006279445055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457192878005026675039260073 342894658503770006279445055)
          ·
            refine ⟨514341987755655009419167583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342894658503770006279445055 514341987755655009419167583)
            ·
              refine ⟨771512981633482514128751375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514341987755655009419167583 771512981633482514128751375)
              ·
                refine ⟨1157269472450223771193127063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771512981633482514128751375 1157269472450223771193127063)
                ·
                  refine ⟨1735904208675335656789690595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157269472450223771193127063 1735904208675335656789690595)
                  ·
                    refine ⟨2603856313013003485184535893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1735904208675335656789690595 2603856313013003485184535893)
                    ·
                      refine ⟨3814242646015141824000785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2603856313013003485184535893 3814242646015141824000785)
                      ·
                        rfl

theorem cell23_7428211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_7428211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428211 prefixEnd_7428211 := by exact prefixLift 7428211
  have htrace : WordTrace (prefixWord ++ tailWord_7428211) baseStart_7428211 baseEnd_7428211 := by
    simpa [prefixWord, tailWord_7428211, baseEnd_7428211] using wordTrace_append hprefix tailTrace_7428211
  have hstable : (prefixWord ++ tailWord_7428211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428211).length < 2 ^ (prefixWord ++ tailWord_7428211).sum := by decide
  have hdescent : baseEnd_7428211 < baseStart_7428211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428228 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_7428228 : Nat := 118140960795 + 7428228 * 2 ^ 59
def prefixEnd_7428228 : Nat := 4983230072969 + 3 ^ 40 * 7428228 * 2
def baseEnd_7428228 : Nat := 3814251375186268257488207

theorem tailTrace_7428228 : CollatzResearch.WordTrace tailWord_7428228 prefixEnd_7428228 3814251375186268257488207 := by
  unfold tailWord_7428228
  simp only [CollatzResearch.WordTrace]
  refine ⟨135464866466403035592946669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180619821955204047457262225 135464866466403035592946669)
  ·
    refine ⟨50799324924901138347355001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135464866466403035592946669 50799324924901138347355001)
    ·
      refine ⟨38099493693675853760516251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50799324924901138347355001 38099493693675853760516251)
      ·
        refine ⟨57149240540513780640774377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38099493693675853760516251 57149240540513780640774377)
        ·
          refine ⟨42861930405385335480580783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57149240540513780640774377 42861930405385335480580783)
          ·
            refine ⟨64292895608078003220871175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42861930405385335480580783 64292895608078003220871175)
            ·
              refine ⟨96439343412117004831306763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64292895608078003220871175 96439343412117004831306763)
              ·
                refine ⟨144659015118175507246960145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96439343412117004831306763 144659015118175507246960145)
                ·
                  refine ⟨108494261338631630435220109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144659015118175507246960145 108494261338631630435220109)
                  ·
                    refine ⟨40685348001986861413207541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108494261338631630435220109 40685348001986861413207541)
                    ·
                      refine ⟨3814251375186268257488207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40685348001986861413207541 3814251375186268257488207)
                      ·
                        rfl

theorem cell23_7428228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_7428228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428228 prefixEnd_7428228 := by exact prefixLift 7428228
  have htrace : WordTrace (prefixWord ++ tailWord_7428228) baseStart_7428228 baseEnd_7428228 := by
    simpa [prefixWord, tailWord_7428228, baseEnd_7428228] using wordTrace_append hprefix tailTrace_7428228
  have hstable : (prefixWord ++ tailWord_7428228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428228).length < 2 ^ (prefixWord ++ tailWord_7428228).sum := by decide
  have hdescent : baseEnd_7428228 < baseStart_7428228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428242 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_7428242 : Nat := 118140960795 + 7428242 * 2 ^ 59
def prefixEnd_7428242 : Nat := 4983230072969 + 3 ^ 40 * 7428242 * 2
def baseEnd_7428242 : Nat := 3814258563915431202713143

theorem tailTrace_7428242 : CollatzResearch.WordTrace tailWord_7428242 prefixEnd_7428242 3814258563915431202713143 := by
  unfold tailWord_7428242
  simp only [CollatzResearch.WordTrace]
  refine ⟨67732560888688837894225745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180620162369836901051268653 67732560888688837894225745)
  ·
    refine ⟨50799420666516628420669309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67732560888688837894225745 50799420666516628420669309)
    ·
      refine ⟨19049782749943735657750991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50799420666516628420669309 19049782749943735657750991)
      ·
        refine ⟨28574674124915603486626487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19049782749943735657750991 28574674124915603486626487)
        ·
          refine ⟨42862011187373405229939731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28574674124915603486626487 42862011187373405229939731)
          ·
            refine ⟨64293016781060107844909597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42862011187373405229939731 64293016781060107844909597)
            ·
              refine ⟨24109881292897540441841099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64293016781060107844909597 24109881292897540441841099)
              ·
                refine ⟨36164821939346310662761649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24109881292897540441841099 36164821939346310662761649)
                ·
                  refine ⟨27123616454509732997071237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36164821939346310662761649 27123616454509732997071237)
                  ·
                    refine ⟨5085678085220574936950857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27123616454509732997071237 5085678085220574936950857)
                    ·
                      refine ⟨3814258563915431202713143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5085678085220574936950857 3814258563915431202713143)
                      ·
                        rfl

theorem cell23_7428242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_7428242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428242 prefixEnd_7428242 := by exact prefixLift 7428242
  have htrace : WordTrace (prefixWord ++ tailWord_7428242) baseStart_7428242 baseEnd_7428242 := by
    simpa [prefixWord, tailWord_7428242, baseEnd_7428242] using wordTrace_append hprefix tailTrace_7428242
  have hstable : (prefixWord ++ tailWord_7428242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428242).length < 2 ^ (prefixWord ++ tailWord_7428242).sum := by decide
  have hdescent : baseEnd_7428242 < baseStart_7428242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428269 : List Nat := [1, 5, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_7428269 : Nat := 118140960795 + 7428269 * 2 ^ 59
def prefixEnd_7428269 : Nat := 4983230072969 + 3 ^ 40 * 7428269 * 2
def baseEnd_7428269 : Nat := 1271424142631034199025173

theorem tailTrace_7428269 : CollatzResearch.WordTrace tailWord_7428269 prefixEnd_7428269 1271424142631034199025173 := by
  unfold tailWord_7428269
  simp only [CollatzResearch.WordTrace]
  refine ⟨270931228325657535188135861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180620818883771690125423907 270931228325657535188135861)
  ·
    refine ⟨25399802655530393923887737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 270931228325657535188135861 25399802655530393923887737)
    ·
      refine ⟨19049851991647795442915803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25399802655530393923887737 19049851991647795442915803)
      ·
        refine ⟨28574777987471693164373705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19049851991647795442915803 28574777987471693164373705)
        ·
          refine ⟨21431083490603769873280279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28574777987471693164373705 21431083490603769873280279)
          ·
            refine ⟨32146625235905654809920419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21431083490603769873280279 32146625235905654809920419)
            ·
              refine ⟨48219937853858482214880629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32146625235905654809920419 48219937853858482214880629)
              ·
                refine ⟨4520619173799232707645059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48219937853858482214880629 4520619173799232707645059)
                ·
                  refine ⟨6780928760698849061467589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4520619173799232707645059 6780928760698849061467589)
                  ·
                    refine ⟨1271424142631034199025173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6780928760698849061467589 1271424142631034199025173)
                    ·
                      rfl

theorem cell23_7428269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_7428269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428269 prefixEnd_7428269 := by exact prefixLift 7428269
  have htrace : WordTrace (prefixWord ++ tailWord_7428269) baseStart_7428269 baseEnd_7428269 := by
    simpa [prefixWord, tailWord_7428269, baseEnd_7428269] using wordTrace_append hprefix tailTrace_7428269
  have hstable : (prefixWord ++ tailWord_7428269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428269).length < 2 ^ (prefixWord ++ tailWord_7428269).sum := by decide
  have hdescent : baseEnd_7428269 < baseStart_7428269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428275 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 7, 1, 3]
def baseStart_7428275 : Nat := 118140960795 + 7428275 * 2 ^ 59
def prefixEnd_7428275 : Nat := 4983230072969 + 3 ^ 40 * 7428275 * 2
def baseEnd_7428275 : Nat := 3814275508777029573600491

theorem tailTrace_7428275 : CollatzResearch.WordTrace tailWord_7428275 prefixEnd_7428275 3814275508777029573600491 := by
  unfold tailWord_7428275
  simp only [CollatzResearch.WordTrace]
  refine ⟨270931447163635798212854279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180620964775757198808569519 270931447163635798212854279)
  ·
    refine ⟨406397170745453697319281419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270931447163635798212854279 406397170745453697319281419)
    ·
      refine ⟨609595756118180545978922129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406397170745453697319281419 609595756118180545978922129)
      ·
        refine ⟨457196817088635409484191597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609595756118180545978922129 457196817088635409484191597)
        ·
          refine ⟨171448806408238278556571849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457196817088635409484191597 171448806408238278556571849)
          ·
            refine ⟨128586604806178708917428887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171448806408238278556571849 128586604806178708917428887)
            ·
              refine ⟨192879907209268063376143331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128586604806178708917428887 192879907209268063376143331)
              ·
                refine ⟨289319860813902095064214997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192879907209268063376143331 289319860813902095064214997)
                ·
                  refine ⟨6780934237825830353067539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 289319860813902095064214997 6780934237825830353067539)
                  ·
                    refine ⟨10171401356738745529601309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6780934237825830353067539 10171401356738745529601309)
                    ·
                      refine ⟨3814275508777029573600491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10171401356738745529601309 3814275508777029573600491)
                      ·
                        rfl

theorem cell23_7428275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 1, 3].length) (baseStart_7428275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428275 prefixEnd_7428275 := by exact prefixLift 7428275
  have htrace : WordTrace (prefixWord ++ tailWord_7428275) baseStart_7428275 baseEnd_7428275 := by
    simpa [prefixWord, tailWord_7428275, baseEnd_7428275] using wordTrace_append hprefix tailTrace_7428275
  have hstable : (prefixWord ++ tailWord_7428275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428275).length < 2 ^ (prefixWord ++ tailWord_7428275).sum := by decide
  have hdescent : baseEnd_7428275 < baseStart_7428275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428302 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2]
def baseStart_7428302 : Nat := 118140960795 + 7428302 * 2 ^ 59
def prefixEnd_7428302 : Nat := 4983230072969 + 3 ^ 40 * 7428302 * 2
def baseEnd_7428302 : Nat := 3814289372754700967962867

theorem tailTrace_7428302 : CollatzResearch.WordTrace tailWord_7428302 prefixEnd_7428302 3814289372754700967962867 := by
  unfold tailWord_7428302
  simp only [CollatzResearch.WordTrace]
  refine ⟨33866553991817247728010895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180621621289691987882724773 33866553991817247728010895)
  ·
    refine ⟨50799830987725871592016343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33866553991817247728010895 50799830987725871592016343)
    ·
      refine ⟨76199746481588807388024515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50799830987725871592016343 76199746481588807388024515)
      ·
        refine ⟨114299619722383211082036773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76199746481588807388024515 114299619722383211082036773)
        ·
          refine ⟨21431178697946852077881895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114299619722383211082036773 21431178697946852077881895)
          ·
            refine ⟨32146768046920278116822843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21431178697946852077881895 32146768046920278116822843)
            ·
              refine ⟨48220152070380417175234265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32146768046920278116822843 48220152070380417175234265)
              ·
                refine ⟨36165114052785312881425699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48220152070380417175234265 36165114052785312881425699)
                ·
                  refine ⟨54247671079177969322138549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36165114052785312881425699 54247671079177969322138549)
                  ·
                    refine ⟨5085719163672934623950489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54247671079177969322138549 5085719163672934623950489)
                    ·
                      refine ⟨3814289372754700967962867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5085719163672934623950489 3814289372754700967962867)
                      ·
                        rfl

theorem cell23_7428302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_7428302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428302 prefixEnd_7428302 := by exact prefixLift 7428302
  have htrace : WordTrace (prefixWord ++ tailWord_7428302) baseStart_7428302 baseEnd_7428302 := by
    simpa [prefixWord, tailWord_7428302, baseEnd_7428302] using wordTrace_append hprefix tailTrace_7428302
  have hstable : (prefixWord ++ tailWord_7428302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428302).length < 2 ^ (prefixWord ++ tailWord_7428302).sum := by decide
  have hdescent : baseEnd_7428302 < baseStart_7428302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428312 : List Nat := [2, 1, 2, 2, 4, 2, 2, 2, 1, 5]
def baseStart_7428312 : Nat := 118140960795 + 7428312 * 2 ^ 59
def prefixEnd_7428312 : Nat := 4983230072969 + 3 ^ 40 * 7428312 * 2
def baseEnd_7428312 : Nat := 1271431502520415309612607

theorem tailTrace_7428312 : CollatzResearch.WordTrace tailWord_7428312 prefixEnd_7428312 1271431502520415309612607 := by
  unfold tailWord_7428312
  simp only [CollatzResearch.WordTrace]
  refine ⟨135466398332250876765975595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180621864443001169021300793 135466398332250876765975595)
  ·
    refine ⟨203199597498376315148963393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135466398332250876765975595 203199597498376315148963393)
    ·
      refine ⟨152399698123782236361722545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203199597498376315148963393 152399698123782236361722545)
      ·
        refine ⟨114299773592836677271291909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152399698123782236361722545 114299773592836677271291909)
        ·
          refine ⟨21431207548656876988367233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114299773592836677271291909 21431207548656876988367233)
          ·
            refine ⟨16073405661492657741275425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21431207548656876988367233 16073405661492657741275425)
            ·
              refine ⟨12055054246119493305956569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16073405661492657741275425 12055054246119493305956569)
              ·
                refine ⟨9041290684589619979467427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12055054246119493305956569 9041290684589619979467427)
                ·
                  refine ⟨13561936026884429969201141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9041290684589619979467427 13561936026884429969201141)
                  ·
                    refine ⟨1271431502520415309612607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13561936026884429969201141 1271431502520415309612607)
                    ·
                      rfl

theorem cell23_7428312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_7428312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428312 prefixEnd_7428312 := by exact prefixLift 7428312
  have htrace : WordTrace (prefixWord ++ tailWord_7428312) baseStart_7428312 baseEnd_7428312 := by
    simpa [prefixWord, tailWord_7428312, baseEnd_7428312] using wordTrace_append hprefix tailTrace_7428312
  have hstable : (prefixWord ++ tailWord_7428312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428312).length < 2 ^ (prefixWord ++ tailWord_7428312).sum := by decide
  have hdescent : baseEnd_7428312 < baseStart_7428312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428315 : List Nat := [1, 1, 1, 1, 1, 1, 1, 10, 1, 1, 4]
def baseStart_7428315 : Nat := 118140960795 + 7428315 * 2 ^ 59
def prefixEnd_7428315 : Nat := 4983230072969 + 3 ^ 40 * 7428315 * 2
def baseEnd_7428315 : Nat := 3814296048003209417100307

theorem tailTrace_7428315 : CollatzResearch.WordTrace tailWord_7428315 prefixEnd_7428315 3814296048003209417100307 := by
  unfold tailWord_7428315
  simp only [CollatzResearch.WordTrace]
  refine ⟨270932906083490885044310399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180621937388993923362873599 270932906083490885044310399)
  ·
    refine ⟨406399359125236327566465599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270932906083490885044310399 406399359125236327566465599)
    ·
      refine ⟨609599038687854491349698399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406399359125236327566465599 609599038687854491349698399)
      ·
        refine ⟨914398558031781737024547599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609599038687854491349698399 914398558031781737024547599)
        ·
          refine ⟨1371597837047672605536821399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914398558031781737024547599 1371597837047672605536821399)
          ·
            refine ⟨2057396755571508908305232099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371597837047672605536821399 2057396755571508908305232099)
            ·
              refine ⟨3086095133357263362457848149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2057396755571508908305232099 3086095133357263362457848149)
              ·
                refine ⟨9041294336007607507200727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3086095133357263362457848149 9041294336007607507200727)
                ·
                  refine ⟨13561941504011411260801091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9041294336007607507200727 13561941504011411260801091)
                  ·
                    refine ⟨20342912256017116891201637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13561941504011411260801091 20342912256017116891201637)
                    ·
                      refine ⟨3814296048003209417100307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20342912256017116891201637 3814296048003209417100307)
                      ·
                        rfl

theorem cell23_7428315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 1, 4].length) (baseStart_7428315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428315 prefixEnd_7428315 := by exact prefixLift 7428315
  have htrace : WordTrace (prefixWord ++ tailWord_7428315) baseStart_7428315 baseEnd_7428315 := by
    simpa [prefixWord, tailWord_7428315, baseEnd_7428315] using wordTrace_append hprefix tailTrace_7428315
  have hstable : (prefixWord ++ tailWord_7428315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428315).length < 2 ^ (prefixWord ++ tailWord_7428315).sum := by decide
  have hdescent : baseEnd_7428315 < baseStart_7428315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428335 : List Nat := [1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 5]
def baseStart_7428335 : Nat := 118140960795 + 7428335 * 2 ^ 59
def prefixEnd_7428335 : Nat := 4983230072969 + 3 ^ 40 * 7428335 * 2
def baseEnd_7428335 : Nat := 3814306317616299338850215

theorem tailTrace_7428335 : CollatzResearch.WordTrace tailWord_7428335 prefixEnd_7428335 3814306317616299338850215 := by
  unfold tailWord_7428335
  simp only [CollatzResearch.WordTrace]
  refine ⟨270933635543418428460038459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180622423695612285640025639 270933635543418428460038459)
  ·
    refine ⟨406400453315127642690057689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270933635543418428460038459 406400453315127642690057689)
    ·
      refine ⟨304800339986345732017543267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406400453315127642690057689 304800339986345732017543267)
      ·
        refine ⟨457200509979518598026314901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304800339986345732017543267 457200509979518598026314901)
        ·
          refine ⟨21431273905289934282483511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 457200509979518598026314901 21431273905289934282483511)
          ·
            refine ⟨32146910857934901423725267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21431273905289934282483511 32146910857934901423725267)
            ·
              refine ⟨48220366286902352135587901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32146910857934901423725267 48220366286902352135587901)
              ·
                refine ⟨18082637357588382050845463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48220366286902352135587901 18082637357588382050845463)
                ·
                  refine ⟨27123956036382573076268195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18082637357588382050845463 27123956036382573076268195)
                  ·
                    refine ⟨40685934054573859614402293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27123956036382573076268195 40685934054573859614402293)
                    ·
                      refine ⟨3814306317616299338850215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40685934054573859614402293 3814306317616299338850215)
                      ·
                        rfl

theorem cell23_7428335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_7428335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428335 prefixEnd_7428335 := by exact prefixLift 7428335
  have htrace : WordTrace (prefixWord ++ tailWord_7428335) baseStart_7428335 baseEnd_7428335 := by
    simpa [prefixWord, tailWord_7428335, baseEnd_7428335] using wordTrace_append hprefix tailTrace_7428335
  have hstable : (prefixWord ++ tailWord_7428335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428335).length < 2 ^ (prefixWord ++ tailWord_7428335).sum := by decide
  have hdescent : baseEnd_7428335 < baseStart_7428335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428342 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_7428342 : Nat := 118140960795 + 7428342 * 2 ^ 59
def prefixEnd_7428342 : Nat := 4983230072969 + 3 ^ 40 * 7428342 * 2
def baseEnd_7428342 : Nat := 1271436637326960270487561

theorem tailTrace_7428342 : CollatzResearch.WordTrace tailWord_7428342 prefixEnd_7428342 1271436637326960270487561 := by
  unfold tailWord_7428342
  simp only [CollatzResearch.WordTrace]
  refine ⟨16933368178399566790971455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180622593902928712437028853 16933368178399566790971455)
  ·
    refine ⟨25400052267599350186457183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16933368178399566790971455 25400052267599350186457183)
    ·
      refine ⟨38100078401399025279685775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25400052267599350186457183 38100078401399025279685775)
      ·
        refine ⟨57150117602098537919528663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38100078401399025279685775 57150117602098537919528663)
        ·
          refine ⟨85725176403147806879292995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57150117602098537919528663 85725176403147806879292995)
          ·
            refine ⟨128587764604721710318939493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85725176403147806879292995 128587764604721710318939493)
            ·
              refine ⟨24110205863385320684801155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128587764604721710318939493 24110205863385320684801155)
              ·
                refine ⟨36165308795077981027201733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24110205863385320684801155 36165308795077981027201733)
                ·
                  refine ⟨6780995399077121442600325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36165308795077981027201733 6780995399077121442600325)
                  ·
                    refine ⟨1271436637326960270487561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6780995399077121442600325 1271436637326960270487561)
                    ·
                      rfl

theorem cell23_7428342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_7428342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428342 prefixEnd_7428342 := by exact prefixLift 7428342
  have htrace : WordTrace (prefixWord ++ tailWord_7428342) baseStart_7428342 baseEnd_7428342 := by
    simpa [prefixWord, tailWord_7428342, baseEnd_7428342] using wordTrace_append hprefix tailTrace_7428342
  have hstable : (prefixWord ++ tailWord_7428342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428342).length < 2 ^ (prefixWord ++ tailWord_7428342).sum := by decide
  have hdescent : baseEnd_7428342 < baseStart_7428342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428369 : List Nat := [1, 2, 2, 1, 1, 7, 1, 2, 1, 2, 3]
def baseStart_7428369 : Nat := 118140960795 + 7428369 * 2 ^ 59
def prefixEnd_7428369 : Nat := 4983230072969 + 3 ^ 40 * 7428369 * 2
def baseEnd_7428369 : Nat := 3814323775958552205825059

theorem tailTrace_7428369 : CollatzResearch.WordTrace tailWord_7428369 prefixEnd_7428369 3814323775958552205825059 := by
  unfold tailWord_7428369
  simp only [CollatzResearch.WordTrace]
  refine ⟨270934875625295252266776161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180623250416863501511184107 270934875625295252266776161)
  ·
    refine ⟨203201156718971439200082121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270934875625295252266776161 203201156718971439200082121)
    ·
      refine ⟨152400867539228579400061591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203201156718971439200082121 152400867539228579400061591)
      ·
        refine ⟨228601301308842869100092387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152400867539228579400061591 228601301308842869100092387)
        ·
          refine ⟨342901951963264303650138581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228601301308842869100092387 342901951963264303650138581)
          ·
            refine ⟨8036764499139007116800123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 342901951963264303650138581 8036764499139007116800123)
            ·
              refine ⟨12055146748708510675200185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8036764499139007116800123 12055146748708510675200185)
              ·
                refine ⟨9041360061531383006400139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12055146748708510675200185 9041360061531383006400139)
                ·
                  refine ⟨13562040092297074509600209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9041360061531383006400139 13562040092297074509600209)
                  ·
                    refine ⟨10171530069222805882200157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13562040092297074509600209 10171530069222805882200157)
                    ·
                      refine ⟨3814323775958552205825059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10171530069222805882200157 3814323775958552205825059)
                      ·
                        rfl

theorem cell23_7428369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_7428369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428369 prefixEnd_7428369 := by exact prefixLift 7428369
  have htrace : WordTrace (prefixWord ++ tailWord_7428369) baseStart_7428369 baseEnd_7428369 := by
    simpa [prefixWord, tailWord_7428369, baseEnd_7428369] using wordTrace_append hprefix tailTrace_7428369
  have hstable : (prefixWord ++ tailWord_7428369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428369).length < 2 ^ (prefixWord ++ tailWord_7428369).sum := by decide
  have hdescent : baseEnd_7428369 < baseStart_7428369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428386 : List Nat := [3, 3, 1, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_7428386 : Nat := 118140960795 + 7428386 * 2 ^ 59
def prefixEnd_7428386 : Nat := 4983230072969 + 3 ^ 40 * 7428386 * 2
def baseEnd_7428386 : Nat := 3814332505129678639312481

theorem tailTrace_7428386 : CollatzResearch.WordTrace tailWord_7428386 prefixEnd_7428386 3814332505129678639312481 := by
  unfold tailWord_7428386
  simp only [CollatzResearch.WordTrace]
  refine ⟨67733873916558416042536253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180623663777489109446763341 67733873916558416042536253)
  ·
    refine ⟨25400202718709406015951095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67733873916558416042536253 25400202718709406015951095)
    ·
      refine ⟨38100304078064109023926643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25400202718709406015951095 38100304078064109023926643)
      ·
        refine ⟨57150456117096163535889965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38100304078064109023926643 57150456117096163535889965)
        ·
          refine ⟨21431421043911061325958737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57150456117096163535889965 21431421043911061325958737)
          ·
            refine ⟨16073565782933295994469053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21431421043911061325958737 16073565782933295994469053)
            ·
              refine ⟨6027587168599985997925895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16073565782933295994469053 6027587168599985997925895)
              ·
                refine ⟨9041380752899978996888843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6027587168599985997925895 9041380752899978996888843)
                ·
                  refine ⟨13562071129349968495333265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9041380752899978996888843 13562071129349968495333265)
                  ·
                    refine ⟨10171553347012476371499949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13562071129349968495333265 10171553347012476371499949)
                    ·
                      refine ⟨3814332505129678639312481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10171553347012476371499949 3814332505129678639312481)
                      ·
                        rfl

theorem cell23_7428386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_7428386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428386 prefixEnd_7428386 := by exact prefixLift 7428386
  have htrace : WordTrace (prefixWord ++ tailWord_7428386) baseStart_7428386 baseEnd_7428386 := by
    simpa [prefixWord, tailWord_7428386, baseEnd_7428386] using wordTrace_append hprefix tailTrace_7428386
  have hstable : (prefixWord ++ tailWord_7428386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428386).length < 2 ^ (prefixWord ++ tailWord_7428386).sum := by decide
  have hdescent : baseEnd_7428386 < baseStart_7428386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428405 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_7428405 : Nat := 118140960795 + 7428405 * 2 ^ 59
def prefixEnd_7428405 : Nat := 4983230072969 + 3 ^ 40 * 7428405 * 2
def baseEnd_7428405 : Nat := 3814342261262114064974893

theorem tailTrace_7428405 : CollatzResearch.WordTrace tailWord_7428405 prefixEnd_7428405 3814342261262114064974893 := by
  unfold tailWord_7428405
  simp only [CollatzResearch.WordTrace]
  refine ⟨270936188653164830415086669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180624125768776553610057779 270936188653164830415086669)
  ·
    refine ⟨101601070744936811405657501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270936188653164830415086669 101601070744936811405657501)
    ·
      refine ⟨38100401529351304277121563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101601070744936811405657501 38100401529351304277121563)
      ·
        refine ⟨57150602294026956415682345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38100401529351304277121563 57150602294026956415682345)
        ·
          refine ⟨42862951720520217311761759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57150602294026956415682345 42862951720520217311761759)
          ·
            refine ⟨64294427580780325967642639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42862951720520217311761759 64294427580780325967642639)
            ·
              refine ⟨96441641371170488951463959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64294427580780325967642639 96441641371170488951463959)
              ·
                refine ⟨144662462056755733427195939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96441641371170488951463959 144662462056755733427195939)
                ·
                  refine ⟨216993693085133600140793909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144662462056755733427195939 216993693085133600140793909)
                  ·
                    refine ⟨20343158726731275013199429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 216993693085133600140793909 20343158726731275013199429)
                    ·
                      refine ⟨3814342261262114064974893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20343158726731275013199429 3814342261262114064974893)
                      ·
                        rfl

theorem cell23_7428405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_7428405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428405 prefixEnd_7428405 := by exact prefixLift 7428405
  have htrace : WordTrace (prefixWord ++ tailWord_7428405) baseStart_7428405 baseEnd_7428405 := by
    simpa [prefixWord, tailWord_7428405, baseEnd_7428405] using wordTrace_append hprefix tailTrace_7428405
  have hstable : (prefixWord ++ tailWord_7428405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428405).length < 2 ^ (prefixWord ++ tailWord_7428405).sum := by decide
  have hdescent : baseEnd_7428405 < baseStart_7428405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428409 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 3, 3, 2]
def baseStart_7428409 : Nat := 118140960795 + 7428409 * 2 ^ 59
def prefixEnd_7428409 : Nat := 4983230072969 + 3 ^ 40 * 7428409 * 2
def baseEnd_7428409 : Nat := 3814344315184732049324875

theorem tailTrace_7428409 : CollatzResearch.WordTrace tailWord_7428409 prefixEnd_7428409 3814344315184732049324875 := by
  unfold tailWord_7428409
  simp only [CollatzResearch.WordTrace]
  refine ⟨270936334545150339098232281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180624223030100226065488187 270936334545150339098232281)
  ·
    refine ⟨203202250908862754323674211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270936334545150339098232281 203202250908862754323674211)
    ·
      refine ⟨304803376363294131485511317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203202250908862754323674211 304803376363294131485511317)
      ·
        refine ⟨14287658267029412413383343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 304803376363294131485511317 14287658267029412413383343)
        ·
          refine ⟨21431487400544118620075015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14287658267029412413383343 21431487400544118620075015)
          ·
            refine ⟨32147231100816177930112523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21431487400544118620075015 32147231100816177930112523)
            ·
              refine ⟨48220846651224266895168785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32147231100816177930112523 48220846651224266895168785)
              ·
                refine ⟨36165634988418200171376589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48220846651224266895168785 36165634988418200171376589)
                ·
                  refine ⟨13562113120656825064266221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36165634988418200171376589 13562113120656825064266221)
                  ·
                    refine ⟨5085792420246309399099833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13562113120656825064266221 5085792420246309399099833)
                    ·
                      refine ⟨3814344315184732049324875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5085792420246309399099833 3814344315184732049324875)
                      ·
                        rfl

theorem cell23_7428409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_7428409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428409 prefixEnd_7428409 := by exact prefixLift 7428409
  have htrace : WordTrace (prefixWord ++ tailWord_7428409) baseStart_7428409 baseEnd_7428409 := by
    simpa [prefixWord, tailWord_7428409, baseEnd_7428409] using wordTrace_append hprefix tailTrace_7428409
  have hstable : (prefixWord ++ tailWord_7428409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428409).length < 2 ^ (prefixWord ++ tailWord_7428409).sum := by decide
  have hdescent : baseEnd_7428409 < baseStart_7428409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428415 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 2, 6]
def baseStart_7428415 : Nat := 118140960795 + 7428415 * 2 ^ 59
def prefixEnd_7428415 : Nat := 4983230072969 + 3 ^ 40 * 7428415 * 2
def baseEnd_7428415 : Nat := 1271449132022886341949949

theorem tailTrace_7428415 : CollatzResearch.WordTrace tailWord_7428415 prefixEnd_7428415 1271449132022886341949949 := by
  unfold tailWord_7428415
  simp only [CollatzResearch.WordTrace]
  refine ⟨270936553383128602122950699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180624368922085734748633799 270936553383128602122950699)
  ·
    refine ⟨406404830074692903184426049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270936553383128602122950699 406404830074692903184426049)
    ·
      refine ⟨304803622556019677388319537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406404830074692903184426049 304803622556019677388319537)
      ·
        refine ⟨228602716917014758041239653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304803622556019677388319537 228602716917014758041239653)
        ·
          refine ⟨42863009421940267132732435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228602716917014758041239653 42863009421940267132732435)
          ·
            refine ⟨64294514132910400699098653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42863009421940267132732435 64294514132910400699098653)
            ·
              refine ⟨24110442799841400262161995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64294514132910400699098653 24110442799841400262161995)
              ·
                refine ⟨36165664199762100393242993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24110442799841400262161995 36165664199762100393242993)
                ·
                  refine ⟨27124248149821575294932245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36165664199762100393242993 27124248149821575294932245)
                  ·
                    refine ⟨1271449132022886341949949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27124248149821575294932245 1271449132022886341949949)
                    ·
                      rfl

theorem cell23_7428415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 6].length) (baseStart_7428415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428415 prefixEnd_7428415 := by exact prefixLift 7428415
  have htrace : WordTrace (prefixWord ++ tailWord_7428415) baseStart_7428415 baseEnd_7428415 := by
    simpa [prefixWord, tailWord_7428415, baseEnd_7428415] using wordTrace_append hprefix tailTrace_7428415
  have hstable : (prefixWord ++ tailWord_7428415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428415).length < 2 ^ (prefixWord ++ tailWord_7428415).sum := by decide
  have hdescent : baseEnd_7428415 < baseStart_7428415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428425 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 4, 4, 3]
def baseStart_7428425 : Nat := 118140960795 + 7428425 * 2 ^ 59
def prefixEnd_7428425 : Nat := 4983230072969 + 3 ^ 40 * 7428425 * 2
def baseEnd_7428425 : Nat := 3814352530875203986724801

theorem tailTrace_7428425 : CollatzResearch.WordTrace tailWord_7428425 prefixEnd_7428425 3814352530875203986724801 := by
  unfold tailWord_7428425
  simp only [CollatzResearch.WordTrace]
  refine ⟨270936918113092373830814729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180624612075394915887209819 270936918113092373830814729)
  ·
    refine ⟨203202688584819280373111047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270936918113092373830814729 203202688584819280373111047)
    ·
      refine ⟨304804032877228920559666571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203202688584819280373111047 304804032877228920559666571)
      ·
        refine ⟨457206049315843380839499857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304804032877228920559666571 457206049315843380839499857)
        ·
          refine ⟨342904536986882535629624893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457206049315843380839499857 342904536986882535629624893)
          ·
            refine ⟨128589201370080950861109335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342904536986882535629624893 128589201370080950861109335)
            ·
              refine ⟨192883802055121426291664003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128589201370080950861109335 192883802055121426291664003)
              ·
                refine ⟨289325703082682139437496005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192883802055121426291664003 289325703082682139437496005)
                ·
                  refine ⟨54248569328002901144530501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289325703082682139437496005 54248569328002901144530501)
                  ·
                    refine ⟨10171606749000543964599469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54248569328002901144530501 10171606749000543964599469)
                    ·
                      refine ⟨3814352530875203986724801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10171606749000543964599469 3814352530875203986724801)
                      ·
                        rfl

theorem cell23_7428425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 4, 3].length) (baseStart_7428425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428425 prefixEnd_7428425 := by exact prefixLift 7428425
  have htrace : WordTrace (prefixWord ++ tailWord_7428425) baseStart_7428425 baseEnd_7428425 := by
    simpa [prefixWord, tailWord_7428425, baseEnd_7428425] using wordTrace_append hprefix tailTrace_7428425
  have hstable : (prefixWord ++ tailWord_7428425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428425).length < 2 ^ (prefixWord ++ tailWord_7428425).sum := by decide
  have hdescent : baseEnd_7428425 < baseStart_7428425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428439 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 4, 2, 2]
def baseStart_7428439 : Nat := 118140960795 + 7428439 * 2 ^ 59
def prefixEnd_7428439 : Nat := 4983230072969 + 3 ^ 40 * 7428439 * 2
def baseEnd_7428439 : Nat := 3814359719604366931949737

theorem tailTrace_7428439 : CollatzResearch.WordTrace tailWord_7428439 prefixEnd_7428439 3814359719604366931949737 := by
  unfold tailWord_7428439
  simp only [CollatzResearch.WordTrace]
  refine ⟨270937428735041654221824371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180624952490027769481216247 270937428735041654221824371)
  ·
    refine ⟨406406143102562481332736557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270937428735041654221824371 406406143102562481332736557)
    ·
      refine ⟨152402303663460930499776209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406406143102562481332736557 152402303663460930499776209)
      ·
        refine ⟨114301727747595697874832157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152402303663460930499776209 114301727747595697874832157)
        ·
          refine ⟨42863147905348386703062059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114301727747595697874832157 42863147905348386703062059)
          ·
            refine ⟨64294721858022580054593089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42863147905348386703062059 64294721858022580054593089)
            ·
              refine ⟨48221041393516935040944817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64294721858022580054593089 48221041393516935040944817)
              ·
                refine ⟨36165781045137701280708613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48221041393516935040944817 36165781045137701280708613)
                ·
                  refine ⟨6781083945963318990132865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36165781045137701280708613 6781083945963318990132865)
                  ·
                    refine ⟨5085812959472489242599649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6781083945963318990132865 5085812959472489242599649)
                    ·
                      refine ⟨3814359719604366931949737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5085812959472489242599649 3814359719604366931949737)
                      ·
                        rfl

theorem cell23_7428439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_7428439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428439 prefixEnd_7428439 := by exact prefixLift 7428439
  have htrace : WordTrace (prefixWord ++ tailWord_7428439) baseStart_7428439 baseEnd_7428439 := by
    simpa [prefixWord, tailWord_7428439, baseEnd_7428439] using wordTrace_append hprefix tailTrace_7428439
  have hstable : (prefixWord ++ tailWord_7428439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428439).length < 2 ^ (prefixWord ++ tailWord_7428439).sum := by decide
  have hdescent : baseEnd_7428439 < baseStart_7428439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428456 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_7428456 : Nat := 118140960795 + 7428456 * 2 ^ 59
def prefixEnd_7428456 : Nat := 4983230072969 + 3 ^ 40 * 7428456 * 2
def baseEnd_7428456 : Nat := 3814368448775493365437159

theorem tailTrace_7428456 : CollatzResearch.WordTrace tailWord_7428456 prefixEnd_7428456 3814368448775493365437159 := by
  unfold tailWord_7428456
  simp only [CollatzResearch.WordTrace]
  refine ⟨135469024387990033062596611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180625365850653377416795481 135469024387990033062596611)
  ·
    refine ⟨203203536581985049593894917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135469024387990033062596611 203203536581985049593894917)
    ·
      refine ⟨38100663109122196798855297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203203536581985049593894917 38100663109122196798855297)
      ·
        refine ⟨28575497331841647599141473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38100663109122196798855297 28575497331841647599141473)
        ·
          refine ⟨21431622998881235699356105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28575497331841647599141473 21431622998881235699356105)
          ·
            refine ⟨16073717249160926774517079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21431622998881235699356105 16073717249160926774517079)
            ·
              refine ⟨24110575873741390161775619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16073717249160926774517079 24110575873741390161775619)
              ·
                refine ⟨36165863810612085242663429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24110575873741390161775619 36165863810612085242663429)
                ·
                  refine ⟨6781099464489765982999393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36165863810612085242663429 6781099464489765982999393)
                  ·
                    refine ⟨5085824598367324487249545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6781099464489765982999393 5085824598367324487249545)
                    ·
                      refine ⟨3814368448775493365437159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5085824598367324487249545 3814368448775493365437159)
                      ·
                        rfl

theorem cell23_7428456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_7428456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428456 prefixEnd_7428456 := by exact prefixLift 7428456
  have htrace : WordTrace (prefixWord ++ tailWord_7428456) baseStart_7428456 baseEnd_7428456 := by
    simpa [prefixWord, tailWord_7428456, baseEnd_7428456] using wordTrace_append hprefix tailTrace_7428456
  have hstable : (prefixWord ++ tailWord_7428456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428456).length < 2 ^ (prefixWord ++ tailWord_7428456).sum := by decide
  have hdescent : baseEnd_7428456 < baseStart_7428456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428475 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 1, 7]
def baseStart_7428475 : Nat := 118140960795 + 7428475 * 2 ^ 59
def prefixEnd_7428475 : Nat := 4983230072969 + 3 ^ 40 * 7428475 * 2
def baseEnd_7428475 : Nat := 1271459401635976263699857

theorem tailTrace_7428475 : CollatzResearch.WordTrace tailWord_7428475 prefixEnd_7428475 1271459401635976263699857 := by
  unfold tailWord_7428475
  simp only [CollatzResearch.WordTrace]
  refine ⟨270938741762911232370134879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180625827841940821580089919 270938741762911232370134879)
  ·
    refine ⟨406408112644366848555202319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270938741762911232370134879 406408112644366848555202319)
    ·
      refine ⟨609612168966550272832803479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406408112644366848555202319 609612168966550272832803479)
      ·
        refine ⟨914418253449825409249205219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609612168966550272832803479 914418253449825409249205219)
        ·
          refine ⟨1371627380174738113873807829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914418253449825409249205219 1371627380174738113873807829)
          ·
            refine ⟨32147516722845424543917371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1371627380174738113873807829 32147516722845424543917371)
            ·
              refine ⟨48221275084268136815876057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32147516722845424543917371 48221275084268136815876057)
              ·
                refine ⟨36165956313201102611907043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48221275084268136815876057 36165956313201102611907043)
                ·
                  refine ⟨54248934469801653917860565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36165956313201102611907043 54248934469801653917860565)
                  ·
                    refine ⟨1271459401635976263699857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54248934469801653917860565 1271459401635976263699857)
                    ·
                      rfl

theorem cell23_7428475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 7].length) (baseStart_7428475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428475 prefixEnd_7428475 := by exact prefixLift 7428475
  have htrace : WordTrace (prefixWord ++ tailWord_7428475) baseStart_7428475 baseEnd_7428475 := by
    simpa [prefixWord, tailWord_7428475, baseEnd_7428475] using wordTrace_append hprefix tailTrace_7428475
  have hstable : (prefixWord ++ tailWord_7428475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428475).length < 2 ^ (prefixWord ++ tailWord_7428475).sum := by decide
  have hdescent : baseEnd_7428475 < baseStart_7428475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428485 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_7428485 : Nat := 118140960795 + 7428485 * 2 ^ 59
def prefixEnd_7428485 : Nat := 4983230072969 + 3 ^ 40 * 7428485 * 2
def baseEnd_7428485 : Nat := 3814383339714473751974525

theorem tailTrace_7428485 : CollatzResearch.WordTrace tailWord_7428485 prefixEnd_7428485 3814383339714473751974525 := by
  unfold tailWord_7428485
  simp only [CollatzResearch.WordTrace]
  refine ⟨270939106492875004077998909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180626070995250002718665939 270939106492875004077998909)
  ·
    refine ⟨101602164934828126529249591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270939106492875004077998909 101602164934828126529249591)
    ·
      refine ⟨152403247402242189793874387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101602164934828126529249591 152403247402242189793874387)
      ·
        refine ⟨228604871103363284690811581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152403247402242189793874387 228604871103363284690811581)
        ·
          refine ⟨85726826663761231759054343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228604871103363284690811581 85726826663761231759054343)
          ·
            refine ⟨128590239995641847638581515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85726826663761231759054343 128590239995641847638581515)
            ·
              refine ⟨192885359993462771457872273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128590239995641847638581515 192885359993462771457872273)
              ·
                refine ⟨144664019995097078593404205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192885359993462771457872273 144664019995097078593404205)
                ·
                  refine ⟨54249007498161404472526577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144664019995097078593404205 54249007498161404472526577)
                  ·
                    refine ⟨40686755623621053354394933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54249007498161404472526577 40686755623621053354394933)
                    ·
                      refine ⟨3814383339714473751974525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40686755623621053354394933 3814383339714473751974525)
                      ·
                        rfl

theorem cell23_7428485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_7428485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428485 prefixEnd_7428485 := by exact prefixLift 7428485
  have htrace : WordTrace (prefixWord ++ tailWord_7428485) baseStart_7428485 baseEnd_7428485 := by
    simpa [prefixWord, tailWord_7428485, baseEnd_7428485] using wordTrace_append hprefix tailTrace_7428485
  have hstable : (prefixWord ++ tailWord_7428485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428485).length < 2 ^ (prefixWord ++ tailWord_7428485).sum := by decide
  have hdescent : baseEnd_7428485 < baseStart_7428485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428509 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_7428509 : Nat := 118140960795 + 7428509 * 2 ^ 59
def prefixEnd_7428509 : Nat := 4983230072969 + 3 ^ 40 * 7428509 * 2
def baseEnd_7428509 : Nat := 1271465221083393886024805

theorem tailTrace_7428509 : CollatzResearch.WordTrace tailWord_7428509 prefixEnd_7428509 1271465221083393886024805 := by
  unfold tailWord_7428509
  simp only [CollatzResearch.WordTrace]
  refine ⟨270939981844788056176872581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180626654563192037451248387 270939981844788056176872581)
  ·
    refine ⟨50801246595897760533163609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270939981844788056176872581 50801246595897760533163609)
    ·
      refine ⟨38100934946923320399872707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50801246595897760533163609 38100934946923320399872707)
      ·
        refine ⟨57151402420384980599809061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38100934946923320399872707 57151402420384980599809061)
        ·
          refine ⟨10715887953822183862464199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57151402420384980599809061 10715887953822183862464199)
          ·
            refine ⟨16073831930733275793696299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10715887953822183862464199 16073831930733275793696299)
            ·
              refine ⟨24110747896099913690544449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16073831930733275793696299 24110747896099913690544449)
              ·
                refine ⟨18083060922074935267908337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24110747896099913690544449 18083060922074935267908337)
                ·
                  refine ⟨13562295691556201450931253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18083060922074935267908337 13562295691556201450931253)
                  ·
                    refine ⟨1271465221083393886024805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13562295691556201450931253 1271465221083393886024805)
                    ·
                      rfl

theorem cell23_7428509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_7428509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428509 prefixEnd_7428509 := by exact prefixLift 7428509
  have htrace : WordTrace (prefixWord ++ tailWord_7428509) baseStart_7428509 baseEnd_7428509 := by
    simpa [prefixWord, tailWord_7428509, baseEnd_7428509] using wordTrace_append hprefix tailTrace_7428509
  have hstable : (prefixWord ++ tailWord_7428509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428509).length < 2 ^ (prefixWord ++ tailWord_7428509).sum := by decide
  have hdescent : baseEnd_7428509 < baseStart_7428509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428512 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 4]
def baseStart_7428512 : Nat := 118140960795 + 7428512 * 2 ^ 59
def prefixEnd_7428512 : Nat := 4983230072969 + 3 ^ 40 * 7428512 * 2
def baseEnd_7428512 : Nat := 3814397203692145146336901

theorem tailTrace_7428512 : CollatzResearch.WordTrace tailWord_7428512 prefixEnd_7428512 3814397203692145146336901 := by
  unfold tailWord_7428512
  simp only [CollatzResearch.WordTrace]
  refine ⟨135470045631888593844615895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180626727509184791792821193 135470045631888593844615895)
  ·
    refine ⟨203205068447832890766923843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135470045631888593844615895 203205068447832890766923843)
    ·
      refine ⟨304807602671749336150385765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203205068447832890766923843 304807602671749336150385765)
      ·
        refine ⟨57151425500953000528197331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304807602671749336150385765 57151425500953000528197331)
        ·
          refine ⟨85727138251429500792295997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57151425500953000528197331 85727138251429500792295997)
          ·
            refine ⟨32147676844286062797110999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85727138251429500792295997 32147676844286062797110999)
            ·
              refine ⟨48221515266429094195666499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32147676844286062797110999 48221515266429094195666499)
              ·
                refine ⟨72332272899643641293499749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48221515266429094195666499 72332272899643641293499749)
                ·
                  refine ⟨13562301168683182742531203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72332272899643641293499749 13562301168683182742531203)
                  ·
                    refine ⟨20343451753024774113796805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13562301168683182742531203 20343451753024774113796805)
                    ·
                      refine ⟨3814397203692145146336901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20343451753024774113796805 3814397203692145146336901)
                      ·
                        rfl

theorem cell23_7428512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_7428512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428512 prefixEnd_7428512 := by exact prefixLift 7428512
  have htrace : WordTrace (prefixWord ++ tailWord_7428512) baseStart_7428512 baseEnd_7428512 := by
    simpa [prefixWord, tailWord_7428512, baseEnd_7428512] using wordTrace_append hprefix tailTrace_7428512
  have hstable : (prefixWord ++ tailWord_7428512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428512).length < 2 ^ (prefixWord ++ tailWord_7428512).sum := by decide
  have hdescent : baseEnd_7428512 < baseStart_7428512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428513 : List Nat := [1, 2, 3, 5, 1, 1, 3, 2, 5]
def baseStart_7428513 : Nat := 118140960795 + 7428513 * 2 ^ 59
def prefixEnd_7428513 : Nat := 4983230072969 + 3 ^ 40 * 7428513 * 2
def baseEnd_7428513 : Nat := 423821968574755515824933

theorem tailTrace_7428513 : CollatzResearch.WordTrace tailWord_7428513 prefixEnd_7428513 423821968574755515824933 := by
  unfold tailWord_7428513
  simp only [CollatzResearch.WordTrace]
  refine ⟨270940127736773564860018193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180626751824515709906678795 270940127736773564860018193)
  ·
    refine ⟨203205095802580173645013645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270940127736773564860018193 203205095802580173645013645)
    ·
      refine ⟨76201910925967565116880117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203205095802580173645013645 76201910925967565116880117)
      ·
        refine ⟨7143929149309459229707511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76201910925967565116880117 7143929149309459229707511)
        ·
          refine ⟨10715893723964188844561267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7143929149309459229707511 10715893723964188844561267)
          ·
            refine ⟨16073840585946283266841901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10715893723964188844561267 16073840585946283266841901)
            ·
              refine ⟨6027690219729856225065713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16073840585946283266841901 6027690219729856225065713)
              ·
                refine ⟨4520767664797392168799285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6027690219729856225065713 4520767664797392168799285)
                ·
                  refine ⟨423821968574755515824933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4520767664797392168799285 423821968574755515824933)
                  ·
                    rfl

theorem cell23_7428513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 5].length) (baseStart_7428513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428513 prefixEnd_7428513 := by exact prefixLift 7428513
  have htrace : WordTrace (prefixWord ++ tailWord_7428513) baseStart_7428513 baseEnd_7428513 := by
    simpa [prefixWord, tailWord_7428513, baseEnd_7428513] using wordTrace_append hprefix tailTrace_7428513
  have hstable : (prefixWord ++ tailWord_7428513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428513).length < 2 ^ (prefixWord ++ tailWord_7428513).sum := by decide
  have hdescent : baseEnd_7428513 < baseStart_7428513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428542 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_7428542 : Nat := 118140960795 + 7428542 * 2 ^ 59
def prefixEnd_7428542 : Nat := 4983230072969 + 3 ^ 40 * 7428542 * 2
def baseEnd_7428542 : Nat := 3814412608111780028961763

theorem tailTrace_7428542 : CollatzResearch.WordTrace tailWord_7428542 prefixEnd_7428542 3814412608111780028961763 := by
  unfold tailWord_7428542
  simp only [CollatzResearch.WordTrace]
  refine ⟨33867648181708562851602985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180627456969112335208549253 33867648181708562851602985)
  ·
    refine ⟨25400736136281422138702239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33867648181708562851602985 25400736136281422138702239)
    ·
      refine ⟨38101104204422133208053359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25400736136281422138702239 38101104204422133208053359)
      ·
        refine ⟨57151656306633199812080039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38101104204422133208053359 57151656306633199812080039)
        ·
          refine ⟨85727484459949799718120059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57151656306633199812080039 85727484459949799718120059)
          ·
            refine ⟨128591226689924699577180089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85727484459949799718120059 128591226689924699577180089)
            ·
              refine ⟨96443420017443524682885067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128591226689924699577180089 96443420017443524682885067)
              ·
                refine ⟨144665130026165287024327601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96443420017443524682885067 144665130026165287024327601)
                ·
                  refine ⟨108498847519623965268245701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144665130026165287024327601 108498847519623965268245701)
                  ·
                    refine ⟨20343533909929493487796069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108498847519623965268245701 20343533909929493487796069)
                    ·
                      refine ⟨3814412608111780028961763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20343533909929493487796069 3814412608111780028961763)
                      ·
                        rfl

theorem cell23_7428542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_7428542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428542 prefixEnd_7428542 := by exact prefixLift 7428542
  have htrace : WordTrace (prefixWord ++ tailWord_7428542) baseStart_7428542 baseEnd_7428542 := by
    simpa [prefixWord, tailWord_7428542, baseEnd_7428542] using wordTrace_append hprefix tailTrace_7428542
  have hstable : (prefixWord ++ tailWord_7428542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428542).length < 2 ^ (prefixWord ++ tailWord_7428542).sum := by decide
  have hdescent : baseEnd_7428542 < baseStart_7428542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428555 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 8]
def baseStart_7428555 : Nat := 118140960795 + 7428555 * 2 ^ 59
def prefixEnd_7428555 : Nat := 4983230072969 + 3 ^ 40 * 7428555 * 2
def baseEnd_7428555 : Nat := 3814419283360288478099203

theorem tailTrace_7428555 : CollatzResearch.WordTrace tailWord_7428555 prefixEnd_7428555 3814419283360288478099203 := by
  unfold tailWord_7428555
  simp only [CollatzResearch.WordTrace]
  refine ⟨270941659602621406033047119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180627773068414270688698079 270941659602621406033047119)
  ·
    refine ⟨406412489403932109049570679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270941659602621406033047119 406412489403932109049570679)
    ·
      refine ⟨609618734105898163574356019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406412489403932109049570679 609618734105898163574356019)
      ·
        refine ⟨914428101158847245361534029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609618734105898163574356019 914428101158847245361534029)
        ·
          refine ⟨342910537934567717010575261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 914428101158847245361534029 342910537934567717010575261)
          ·
            refine ⟨128591451725462893878965723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342910537934567717010575261 128591451725462893878965723)
            ·
              refine ⟨192887177588194340818448585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128591451725462893878965723 192887177588194340818448585)
              ·
                refine ⟨144665383191145755613836439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192887177588194340818448585 144665383191145755613836439)
                ·
                  refine ⟨216998074786718633420754659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144665383191145755613836439 216998074786718633420754659)
                  ·
                    refine ⟨325497112180077950131131989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 216998074786718633420754659 325497112180077950131131989)
                    ·
                      refine ⟨3814419283360288478099203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 325497112180077950131131989 3814419283360288478099203)
                      ·
                        rfl

theorem cell23_7428555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_7428555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428555 prefixEnd_7428555 := by exact prefixLift 7428555
  have htrace : WordTrace (prefixWord ++ tailWord_7428555) baseStart_7428555 baseEnd_7428555 := by
    simpa [prefixWord, tailWord_7428555, baseEnd_7428555] using wordTrace_append hprefix tailTrace_7428555
  have hstable : (prefixWord ++ tailWord_7428555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428555).length < 2 ^ (prefixWord ++ tailWord_7428555).sum := by decide
  have hdescent : baseEnd_7428555 < baseStart_7428555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428566 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_7428566 : Nat := 118140960795 + 7428566 * 2 ^ 59
def prefixEnd_7428566 : Nat := 4983230072969 + 3 ^ 40 * 7428566 * 2
def baseEnd_7428566 : Nat := 3814424931647487935061653

theorem tailTrace_7428566 : CollatzResearch.WordTrace tailWord_7428566 prefixEnd_7428566 3814424931647487935061653 := by
  unfold tailWord_7428566
  simp only [CollatzResearch.WordTrace]
  refine ⟨16933878800348847181981097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180628040537054369941131701 16933878800348847181981097)
  ·
    refine ⟨12700409100261635386485823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16933878800348847181981097 12700409100261635386485823)
    ·
      refine ⟨19050613650392453079728735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12700409100261635386485823 19050613650392453079728735)
      ·
        refine ⟨28575920475588679619593103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19050613650392453079728735 28575920475588679619593103)
        ·
          refine ⟨42863880713383019429389655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28575920475588679619593103 42863880713383019429389655)
          ·
            refine ⟨64295821070074529144084483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42863880713383019429389655 64295821070074529144084483)
            ·
              refine ⟨96443731605111793716126725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64295821070074529144084483 96443731605111793716126725)
              ·
                refine ⟨18083199675958461321773761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96443731605111793716126725 18083199675958461321773761)
                ·
                  refine ⟨13562399756968845991330321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18083199675958461321773761 13562399756968845991330321)
                  ·
                    refine ⟨10171799817726634493497741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13562399756968845991330321 10171799817726634493497741)
                    ·
                      refine ⟨3814424931647487935061653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10171799817726634493497741 3814424931647487935061653)
                      ·
                        rfl

theorem cell23_7428566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_7428566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428566 prefixEnd_7428566 := by exact prefixLift 7428566
  have htrace : WordTrace (prefixWord ++ tailWord_7428566) baseStart_7428566 baseEnd_7428566 := by
    simpa [prefixWord, tailWord_7428566, baseEnd_7428566] using wordTrace_append hprefix tailTrace_7428566
  have hstable : (prefixWord ++ tailWord_7428566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428566).length < 2 ^ (prefixWord ++ tailWord_7428566).sum := by decide
  have hdescent : baseEnd_7428566 < baseStart_7428566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428629 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 4, 4]
def baseStart_7428629 : Nat := 118140960795 + 7428629 * 2 ^ 59
def prefixEnd_7428629 : Nat := 4983230072969 + 3 ^ 40 * 7428629 * 2
def baseEnd_7428629 : Nat := 1271485760309573729524621

theorem tailTrace_7428629 : CollatzResearch.WordTrace tailWord_7428629 prefixEnd_7428629 1271485760309573729524621 := by
  unfold tailWord_7428629
  simp only [CollatzResearch.WordTrace]
  refine ⟨270944358604353316671240941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180629572402902211114160627 270944358604353316671240941)
  ·
    refine ⟨101604134476632493751715353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270944358604353316671240941 101604134476632493751715353)
    ·
      refine ⟨76203100857474370313786515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101604134476632493751715353 76203100857474370313786515)
      ·
        refine ⟨114304651286211555470679773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76203100857474370313786515 114304651286211555470679773)
        ·
          refine ⟨42864244232329333301504915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114304651286211555470679773 42864244232329333301504915)
          ·
            refine ⟨64296366348493999952257373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42864244232329333301504915 64296366348493999952257373)
            ·
              refine ⟨24111137380685249982096515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64296366348493999952257373 24111137380685249982096515)
              ·
                refine ⟨36166706071027874973144773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24111137380685249982096515 36166706071027874973144773)
                ·
                  refine ⟨6781257388317726557464645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36166706071027874973144773 6781257388317726557464645)
                  ·
                    refine ⟨1271485760309573729524621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6781257388317726557464645 1271485760309573729524621)
                    ·
                      rfl

theorem cell23_7428629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_7428629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428629 prefixEnd_7428629 := by exact prefixLift 7428629
  have htrace : WordTrace (prefixWord ++ tailWord_7428629) baseStart_7428629 baseEnd_7428629 := by
    simpa [prefixWord, tailWord_7428629, baseEnd_7428629] using wordTrace_append hprefix tailTrace_7428629
  have hstable : (prefixWord ++ tailWord_7428629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428629).length < 2 ^ (prefixWord ++ tailWord_7428629).sum := by decide
  have hdescent : baseEnd_7428629 < baseStart_7428629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428642 : List Nat := [3, 3, 1, 1, 1, 1, 1, 12]
def baseStart_7428642 : Nat := 118140960795 + 7428642 * 2 ^ 59
def prefixEnd_7428642 : Nat := 4983230072969 + 3 ^ 40 * 7428642 * 2
def baseEnd_7428642 : Nat := 141276442821378875470789

theorem tailTrace_7428642 : CollatzResearch.WordTrace tailWord_7428642 prefixEnd_7428642 141276442821378875470789 := by
  unfold tailWord_7428642
  simp only [CollatzResearch.WordTrace]
  refine ⟨67736208188326554972866045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180629888502204146594309453 67736208188326554972866045)
  ·
    refine ⟨25401078070622458114824767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67736208188326554972866045 25401078070622458114824767)
    ·
      refine ⟨38101617105933687172237151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25401078070622458114824767 38101617105933687172237151)
      ·
        refine ⟨57152425658900530758355727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38101617105933687172237151 57152425658900530758355727)
        ·
          refine ⟨85728638488350796137533591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57152425658900530758355727 85728638488350796137533591)
          ·
            refine ⟨128592957732526194206300387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85728638488350796137533591 128592957732526194206300387)
            ·
              refine ⟨192889436598789291309450581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128592957732526194206300387 192889436598789291309450581)
              ·
                refine ⟨141276442821378875470789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 192889436598789291309450581 141276442821378875470789)
                ·
                  rfl

theorem cell23_7428642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 12].length) (baseStart_7428642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428642 prefixEnd_7428642 := by exact prefixLift 7428642
  have htrace : WordTrace (prefixWord ++ tailWord_7428642) baseStart_7428642 baseEnd_7428642 := by
    simpa [prefixWord, tailWord_7428642, baseEnd_7428642] using wordTrace_append hprefix tailTrace_7428642
  have hstable : (prefixWord ++ tailWord_7428642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428642).length < 2 ^ (prefixWord ++ tailWord_7428642).sum := by decide
  have hdescent : baseEnd_7428642 < baseStart_7428642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428686 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3]
def baseStart_7428686 : Nat := 118140960795 + 7428686 * 2 ^ 59
def prefixEnd_7428686 : Nat := 4983230072969 + 3 ^ 40 * 7428686 * 2
def baseEnd_7428686 : Nat := 3814486549326027465561101

theorem tailTrace_7428686 : CollatzResearch.WordTrace tailWord_7428686 prefixEnd_7428686 3814486549326027465561101 := by
  unfold tailWord_7428686
  simp only [CollatzResearch.WordTrace]
  refine ⟨33868304695643351925758239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180630958376764543604043941 33868304695643351925758239)
  ·
    refine ⟨50802457043465027888637359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33868304695643351925758239 50802457043465027888637359)
    ·
      refine ⟨76203685565197541832956039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50802457043465027888637359 76203685565197541832956039)
      ·
        refine ⟨114305528347796312749434059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76203685565197541832956039 114305528347796312749434059)
        ·
          refine ⟨171458292521694469124151089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114305528347796312749434059 171458292521694469124151089)
          ·
            refine ⟨128593719391270851843113317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171458292521694469124151089 128593719391270851843113317)
            ·
              refine ⟨24111322385863284720583747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128593719391270851843113317 24111322385863284720583747)
              ·
                refine ⟨36166983578794927080875621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24111322385863284720583747 36166983578794927080875621)
                ·
                  refine ⟨6781309421024048827664179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36166983578794927080875621 6781309421024048827664179)
                  ·
                    refine ⟨10171964131536073241496269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6781309421024048827664179 10171964131536073241496269)
                    ·
                      refine ⟨3814486549326027465561101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10171964131536073241496269 3814486549326027465561101)
                      ·
                        rfl

theorem cell23_7428686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_7428686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428686 prefixEnd_7428686 := by exact prefixLift 7428686
  have htrace : WordTrace (prefixWord ++ tailWord_7428686) baseStart_7428686 baseEnd_7428686 := by
    simpa [prefixWord, tailWord_7428686, baseEnd_7428686] using wordTrace_append hprefix tailTrace_7428686
  have hstable : (prefixWord ++ tailWord_7428686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428686).length < 2 ^ (prefixWord ++ tailWord_7428686).sum := by decide
  have hdescent : baseEnd_7428686 < baseStart_7428686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428729 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 2, 1, 5]
def baseStart_7428729 : Nat := 118140960795 + 7428729 * 2 ^ 59
def prefixEnd_7428729 : Nat := 4983230072969 + 3 ^ 40 * 7428729 * 2
def baseEnd_7428729 : Nat := 3814508628994170797323403

theorem tailTrace_7428729 : CollatzResearch.WordTrace tailWord_7428729 prefixEnd_7428729 3814508628994170797323403 := by
  unfold tailWord_7428729
  simp only [CollatzResearch.WordTrace]
  refine ⟨270948005903991033749881241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180632003935994022499920827 270948005903991033749881241)
  ·
    refine ⟨203211004427993275312410931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270948005903991033749881241 203211004427993275312410931)
    ·
      refine ⟨304816506641989912968616397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203211004427993275312410931 304816506641989912968616397)
      ·
        refine ⟨114306189990746217363231149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304816506641989912968616397 114306189990746217363231149)
        ·
          refine ⟨42864821246529831511211681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114306189990746217363231149 42864821246529831511211681)
          ·
            refine ⟨32148615934897373633408761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42864821246529831511211681 32148615934897373633408761)
            ·
              refine ⟨24111461951173030225056571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32148615934897373633408761 24111461951173030225056571)
              ·
                refine ⟨36167192926759545337584857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24111461951173030225056571 36167192926759545337584857)
                ·
                  refine ⟨27125394695069659003188643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36167192926759545337584857 27125394695069659003188643)
                  ·
                    refine ⟨40688092042604488504782965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27125394695069659003188643 40688092042604488504782965)
                    ·
                      refine ⟨3814508628994170797323403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40688092042604488504782965 3814508628994170797323403)
                      ·
                        rfl

theorem cell23_7428729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_7428729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428729 prefixEnd_7428729 := by exact prefixLift 7428729
  have htrace : WordTrace (prefixWord ++ tailWord_7428729) baseStart_7428729 baseEnd_7428729 := by
    simpa [prefixWord, tailWord_7428729, baseEnd_7428729] using wordTrace_append hprefix tailTrace_7428729
  have hstable : (prefixWord ++ tailWord_7428729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428729).length < 2 ^ (prefixWord ++ tailWord_7428729).sum := by decide
  have hdescent : baseEnd_7428729 < baseStart_7428729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428752 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 8]
def baseStart_7428752 : Nat := 118140960795 + 7428752 * 2 ^ 59
def prefixEnd_7428752 : Nat := 4983230072969 + 3 ^ 40 * 7428752 * 2
def baseEnd_7428752 : Nat := 3814520439049224207335797

theorem tailTrace_7428752 : CollatzResearch.WordTrace tailWord_7428752 prefixEnd_7428752 3814520439049224207335797 := by
  unfold tailWord_7428752
  simp only [CollatzResearch.WordTrace]
  refine ⟨135474422391453854338984255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180632563188605139118645673 135474422391453854338984255)
  ·
    refine ⟨203211633587180781508476383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135474422391453854338984255 203211633587180781508476383)
    ·
      refine ⟨304817450380771172262714575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203211633587180781508476383 304817450380771172262714575)
      ·
        refine ⟨457226175571156758394071863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304817450380771172262714575 457226175571156758394071863)
        ·
          refine ⟨685839263356735137591107795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457226175571156758394071863 685839263356735137591107795)
          ·
            refine ⟨1028758895035102706386661693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685839263356735137591107795 1028758895035102706386661693)
            ·
              refine ⟨385784585638163514894998135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1028758895035102706386661693 385784585638163514894998135)
              ·
                refine ⟨578676878457245272342497203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385784585638163514894998135 578676878457245272342497203)
                ·
                  refine ⟨868015317685867908513745805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578676878457245272342497203 868015317685867908513745805)
                  ·
                    refine ⟨325505744132200465692654677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 868015317685867908513745805 325505744132200465692654677)
                    ·
                      refine ⟨3814520439049224207335797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 325505744132200465692654677 3814520439049224207335797)
                      ·
                        rfl

theorem cell23_7428752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_7428752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428752 prefixEnd_7428752 := by exact prefixLift 7428752
  have htrace : WordTrace (prefixWord ++ tailWord_7428752) baseStart_7428752 baseEnd_7428752 := by
    simpa [prefixWord, tailWord_7428752, baseEnd_7428752] using wordTrace_append hprefix tailTrace_7428752
  have hstable : (prefixWord ++ tailWord_7428752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428752).length < 2 ^ (prefixWord ++ tailWord_7428752).sum := by decide
  have hdescent : baseEnd_7428752 < baseStart_7428752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428756 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_7428756 : Nat := 118140960795 + 7428756 * 2 ^ 59
def prefixEnd_7428756 : Nat := 4983230072969 + 3 ^ 40 * 7428756 * 2
def baseEnd_7428756 : Nat := 3814522492971842191685779

theorem tailTrace_7428756 : CollatzResearch.WordTrace tailWord_7428756 prefixEnd_7428756 3814522492971842191685779 := by
  unfold tailWord_7428756
  simp only [CollatzResearch.WordTrace]
  refine ⟨135474495337446608680557061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180632660449928811574076081 135474495337446608680557061)
  ·
    refine ⟨25401467875771239127604449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135474495337446608680557061 25401467875771239127604449)
    ·
      refine ⟨19051100906828429345703337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25401467875771239127604449 19051100906828429345703337)
      ·
        refine ⟨14288325680121322009277503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19051100906828429345703337 14288325680121322009277503)
        ·
          refine ⟨21432488520181983013916255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14288325680121322009277503 21432488520181983013916255)
          ·
            refine ⟨32148732780272974520874383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21432488520181983013916255 32148732780272974520874383)
            ·
              refine ⟨48223099170409461781311575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32148732780272974520874383 48223099170409461781311575)
              ·
                refine ⟨72334648755614192671967363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48223099170409461781311575 72334648755614192671967363)
                ·
                  refine ⟨108501973133421289007951045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72334648755614192671967363 108501973133421289007951045)
                  ·
                    refine ⟨20344119962516491688990821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108501973133421289007951045 20344119962516491688990821)
                    ·
                      refine ⟨3814522492971842191685779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20344119962516491688990821 3814522492971842191685779)
                      ·
                        rfl

theorem cell23_7428756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_7428756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428756 prefixEnd_7428756 := by exact prefixLift 7428756
  have htrace : WordTrace (prefixWord ++ tailWord_7428756) baseStart_7428756 baseEnd_7428756 := by
    simpa [prefixWord, tailWord_7428756, baseEnd_7428756] using wordTrace_append hprefix tailTrace_7428756
  have hstable : (prefixWord ++ tailWord_7428756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428756).length < 2 ^ (prefixWord ++ tailWord_7428756).sum := by decide
  have hdescent : baseEnd_7428756 < baseStart_7428756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428766 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 7]
def baseStart_7428766 : Nat := 118140960795 + 7428766 * 2 ^ 59
def prefixEnd_7428766 : Nat := 4983230072969 + 3 ^ 40 * 7428766 * 2
def baseEnd_7428766 : Nat := 423836403086487461395637

theorem tailTrace_7428766 : CollatzResearch.WordTrace tailWord_7428766 prefixEnd_7428766 423836403086487461395637 := by
  unfold tailWord_7428766
  simp only [CollatzResearch.WordTrace]
  refine ⟨33868669425607123633622269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180632903603237992712652101 33868669425607123633622269)
  ·
    refine ⟨12700751034602671362608351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33868669425607123633622269 12700751034602671362608351)
    ·
      refine ⟨19051126551904007043912527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12700751034602671362608351 19051126551904007043912527)
      ·
        refine ⟨28576689827856010565868791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19051126551904007043912527 28576689827856010565868791)
        ·
          refine ⟨42865034741784015848803187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28576689827856010565868791 42865034741784015848803187)
          ·
            refine ⟨64297552112676023773204781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42865034741784015848803187 64297552112676023773204781)
            ·
              refine ⟨24111582042253508914951793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64297552112676023773204781 24111582042253508914951793)
              ·
                refine ⟨18083686531690131686213845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24111582042253508914951793 18083686531690131686213845)
                ·
                  refine ⟨423836403086487461395637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18083686531690131686213845 423836403086487461395637)
                  ·
                    rfl

theorem cell23_7428766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_7428766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428766 prefixEnd_7428766 := by exact prefixLift 7428766
  have htrace : WordTrace (prefixWord ++ tailWord_7428766) baseStart_7428766 baseEnd_7428766 := by
    simpa [prefixWord, tailWord_7428766, baseEnd_7428766] using wordTrace_append hprefix tailTrace_7428766
  have hstable : (prefixWord ++ tailWord_7428766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428766).length < 2 ^ (prefixWord ++ tailWord_7428766).sum := by decide
  have hdescent : baseEnd_7428766 < baseStart_7428766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428826 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 3, 4]
def baseStart_7428826 : Nat := 118140960795 + 7428826 * 2 ^ 59
def prefixEnd_7428826 : Nat := 4983230072969 + 3 ^ 40 * 7428826 * 2
def baseEnd_7428826 : Nat := 1271519478872552305936819

theorem tailTrace_7428826 : CollatzResearch.WordTrace tailWord_7428826 prefixEnd_7428826 1271519478872552305936819 := by
  unfold tailWord_7428826
  simp only [CollatzResearch.WordTrace]
  refine ⟨67737885946159904829040583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180634362523093079544108221 67737885946159904829040583)
  ·
    refine ⟨101606828919239857243560875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67737885946159904829040583 101606828919239857243560875)
    ·
      refine ⟨152410243378859785865341313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101606828919239857243560875 152410243378859785865341313)
      ·
        refine ⟨114307682534144839399005985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152410243378859785865341313 114307682534144839399005985)
        ·
          refine ⟨85730761900608629549254489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114307682534144839399005985 85730761900608629549254489)
          ·
            refine ⟨64298071425456472161940867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85730761900608629549254489 64298071425456472161940867)
            ·
              refine ⟨96447107138184708242911301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64298071425456472161940867 96447107138184708242911301)
              ·
                refine ⟨18083832588409632795545869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96447107138184708242911301 18083832588409632795545869)
                ·
                  refine ⟨6781437220653612298329701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18083832588409632795545869 6781437220653612298329701)
                  ·
                    refine ⟨1271519478872552305936819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6781437220653612298329701 1271519478872552305936819)
                    ·
                      rfl

theorem cell23_7428826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_7428826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428826 prefixEnd_7428826 := by exact prefixLift 7428826
  have htrace : WordTrace (prefixWord ++ tailWord_7428826) baseStart_7428826 baseEnd_7428826 := by
    simpa [prefixWord, tailWord_7428826, baseEnd_7428826] using wordTrace_append hprefix tailTrace_7428826
  have hstable : (prefixWord ++ tailWord_7428826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428826).length < 2 ^ (prefixWord ++ tailWord_7428826).sum := by decide
  have hdescent : baseEnd_7428826 < baseStart_7428826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428836 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_7428836 : Nat := 118140960795 + 7428836 * 2 ^ 59
def prefixEnd_7428836 : Nat := 4983230072969 + 3 ^ 40 * 7428836 * 2
def baseEnd_7428836 : Nat := 3814563571424201878685411

theorem tailTrace_7428836 : CollatzResearch.WordTrace tailWord_7428836 prefixEnd_7428836 3814563571424201878685411 := by
  unfold tailWord_7428836
  simp only [CollatzResearch.WordTrace]
  refine ⟨135475954257301695512013181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180634605676402260682684241 135475954257301695512013181)
  ·
    refine ⟨50803482846488135817004943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135475954257301695512013181 50803482846488135817004943)
    ·
      refine ⟨76205224269732203725507415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50803482846488135817004943 76205224269732203725507415)
      ·
        refine ⟨114307836404598305588261123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76205224269732203725507415 114307836404598305588261123)
        ·
          refine ⟨171461754606897458382391685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114307836404598305588261123 171461754606897458382391685)
          ·
            refine ⟨32149078988793273446698441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171461754606897458382391685 32149078988793273446698441)
            ·
              refine ⟨24111809241594955085023831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32149078988793273446698441 24111809241594955085023831)
              ·
                refine ⟨36167713862392432627535747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24111809241594955085023831 36167713862392432627535747)
                ·
                  refine ⟨54251570793588648941303621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36167713862392432627535747 54251570793588648941303621)
                  ·
                    refine ⟨10172169523797871676494429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54251570793588648941303621 10172169523797871676494429)
                    ·
                      refine ⟨3814563571424201878685411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10172169523797871676494429 3814563571424201878685411)
                      ·
                        rfl

theorem cell23_7428836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_7428836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428836 prefixEnd_7428836 := by exact prefixLift 7428836
  have htrace : WordTrace (prefixWord ++ tailWord_7428836) baseStart_7428836 baseEnd_7428836 := by
    simpa [prefixWord, tailWord_7428836, baseEnd_7428836] using wordTrace_append hprefix tailTrace_7428836
  have hstable : (prefixWord ++ tailWord_7428836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428836).length < 2 ^ (prefixWord ++ tailWord_7428836).sum := by decide
  have hdescent : baseEnd_7428836 < baseStart_7428836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428917 : List Nat := [1, 3, 3, 1, 3, 2, 1, 4, 1, 1, 3]
def baseStart_7428917 : Nat := 118140960795 + 7428917 * 2 ^ 59
def prefixEnd_7428917 : Nat := 4983230072969 + 3 ^ 40 * 7428917 * 2
def baseEnd_7428917 : Nat := 3814605163357216061772539

theorem tailTrace_7428917 : CollatzResearch.WordTrace tailWord_7428917 prefixEnd_7428917 3814605163357216061772539 := by
  unfold tailWord_7428917
  simp only [CollatzResearch.WordTrace]
  refine ⟨270954862827309941857725005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180636575218206627905150003 270954862827309941857725005)
  ·
    refine ⟨101608073560241228196646877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270954862827309941857725005 101608073560241228196646877)
    ·
      refine ⟨38103027585090460573742579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101608073560241228196646877 38103027585090460573742579)
      ·
        refine ⟨57154541377635690860613869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38103027585090460573742579 57154541377635690860613869)
        ·
          refine ⟨21432953016613384072730201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57154541377635690860613869 21432953016613384072730201)
          ·
            refine ⟨16074714762460038054547651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21432953016613384072730201 16074714762460038054547651)
            ·
              refine ⟨24112072143690057081821477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16074714762460038054547651 24112072143690057081821477)
              ·
                refine ⟨4521013526941885702841527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24112072143690057081821477 4521013526941885702841527)
                ·
                  refine ⟨6781520290412828554262291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521013526941885702841527 6781520290412828554262291)
                  ·
                    refine ⟨10172280435619242831393437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6781520290412828554262291 10172280435619242831393437)
                    ·
                      refine ⟨3814605163357216061772539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10172280435619242831393437 3814605163357216061772539)
                      ·
                        rfl

theorem cell23_7428917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_7428917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428917 prefixEnd_7428917 := by exact prefixLift 7428917
  have htrace : WordTrace (prefixWord ++ tailWord_7428917) baseStart_7428917 baseEnd_7428917 := by
    simpa [prefixWord, tailWord_7428917, baseEnd_7428917] using wordTrace_append hprefix tailTrace_7428917
  have hstable : (prefixWord ++ tailWord_7428917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428917).length < 2 ^ (prefixWord ++ tailWord_7428917).sum := by decide
  have hdescent : baseEnd_7428917 < baseStart_7428917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428934 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_7428934 : Nat := 118140960795 + 7428934 * 2 ^ 59
def prefixEnd_7428934 : Nat := 4983230072969 + 3 ^ 40 * 7428934 * 2
def baseEnd_7428934 : Nat := 3814613892528342495259961

theorem tailTrace_7428934 : CollatzResearch.WordTrace tailWord_7428934 prefixEnd_7428934 3814613892528342495259961 := by
  unfold tailWord_7428934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8467358839632761055034183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 180636988578832235840729237 8467358839632761055034183)
  ·
    refine ⟨12701038259449141582551275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8467358839632761055034183 12701038259449141582551275)
    ·
      refine ⟨19051557389173712373826913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12701038259449141582551275 19051557389173712373826913)
      ·
        refine ⟨14288668041880284280370185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19051557389173712373826913 14288668041880284280370185)
        ·
          refine ⟨10716501031410213210277639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14288668041880284280370185 10716501031410213210277639)
          ·
            refine ⟨16074751547115319815416459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10716501031410213210277639 16074751547115319815416459)
            ·
              refine ⟨24112127320672979723124689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16074751547115319815416459 24112127320672979723124689)
              ·
                refine ⟨18084095490504734792343517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24112127320672979723124689 18084095490504734792343517)
                ·
                  refine ⟨6781535808939275547128819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18084095490504734792343517 6781535808939275547128819)
                  ·
                    refine ⟨10172303713408913320693229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6781535808939275547128819 10172303713408913320693229)
                    ·
                      refine ⟨3814613892528342495259961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10172303713408913320693229 3814613892528342495259961)
                      ·
                        rfl

theorem cell23_7428934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_7428934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428934 prefixEnd_7428934 := by exact prefixLift 7428934
  have htrace : WordTrace (prefixWord ++ tailWord_7428934) baseStart_7428934 baseEnd_7428934 := by
    simpa [prefixWord, tailWord_7428934, baseEnd_7428934] using wordTrace_append hprefix tailTrace_7428934
  have hstable : (prefixWord ++ tailWord_7428934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428934).length < 2 ^ (prefixWord ++ tailWord_7428934).sum := by decide
  have hdescent : baseEnd_7428934 < baseStart_7428934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428939 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 7]
def baseStart_7428939 : Nat := 118140960795 + 7428939 * 2 ^ 59
def prefixEnd_7428939 : Nat := 4983230072969 + 3 ^ 40 * 7428939 * 2
def baseEnd_7428939 : Nat := 3814616459931614975697437

theorem tailTrace_7428939 : CollatzResearch.WordTrace tailWord_7428939 prefixEnd_7428939 3814616459931614975697437 := by
  unfold tailWord_7428939
  simp only [CollatzResearch.WordTrace]
  refine ⟨270955665233230239615025871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180637110155486826410017247 270955665233230239615025871)
  ·
    refine ⟨406433497849845359422538807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270955665233230239615025871 406433497849845359422538807)
    ·
      refine ⟨609650246774768039133808211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406433497849845359422538807 609650246774768039133808211)
      ·
        refine ⟨914475370162152058700712317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609650246774768039133808211 914475370162152058700712317)
        ·
          refine ⟨342928263810807022012767119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 914475370162152058700712317 342928263810807022012767119)
          ·
            refine ⟨514392395716210533019150679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342928263810807022012767119 514392395716210533019150679)
            ·
              refine ⟨771588593574315799528726019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514392395716210533019150679 771588593574315799528726019)
              ·
                refine ⟨1157382890361473699293089029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771588593574315799528726019 1157382890361473699293089029)
                ·
                  refine ⟨217009291942776318617454193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1157382890361473699293089029 217009291942776318617454193)
                  ·
                    refine ⟨162756968957082238963090645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 217009291942776318617454193 162756968957082238963090645)
                    ·
                      refine ⟨3814616459931614975697437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162756968957082238963090645 3814616459931614975697437)
                      ·
                        rfl

theorem cell23_7428939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_7428939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428939 prefixEnd_7428939 := by exact prefixLift 7428939
  have htrace : WordTrace (prefixWord ++ tailWord_7428939) baseStart_7428939 baseEnd_7428939 := by
    simpa [prefixWord, tailWord_7428939, baseEnd_7428939] using wordTrace_append hprefix tailTrace_7428939
  have hstable : (prefixWord ++ tailWord_7428939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428939).length < 2 ^ (prefixWord ++ tailWord_7428939).sum := by decide
  have hdescent : baseEnd_7428939 < baseStart_7428939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428940 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 5, 2, 2]
def baseStart_7428940 : Nat := 118140960795 + 7428940 * 2 ^ 59
def prefixEnd_7428940 : Nat := 4983230072969 + 3 ^ 40 * 7428940 * 2
def baseEnd_7428940 : Nat := 3814616973412269471784933

theorem tailTrace_7428940 : CollatzResearch.WordTrace tailWord_7428940 prefixEnd_7428940 3814616973412269471784933 := by
  unfold tailWord_7428940
  simp only [CollatzResearch.WordTrace]
  refine ⟨135477850853113308392906137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180637134470817744523874849 135477850853113308392906137)
  ·
    refine ⟨101608388139834981294679603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135477850853113308392906137 101608388139834981294679603)
    ·
      refine ⟨152412582209752471942019405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101608388139834981294679603 152412582209752471942019405)
      ·
        refine ⟨57154718328657176978257277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152412582209752471942019405 57154718328657176978257277)
        ·
          refine ⟨21433019373246441366846479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57154718328657176978257277 21433019373246441366846479)
          ·
            refine ⟨32149529059869662050269719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21433019373246441366846479 32149529059869662050269719)
            ·
              refine ⟨48224293589804493075404579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32149529059869662050269719 48224293589804493075404579)
              ·
                refine ⟨72336440384706739613106869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48224293589804493075404579 72336440384706739613106869)
                ·
                  refine ⟨6781541286066256838728769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72336440384706739613106869 6781541286066256838728769)
                  ·
                    refine ⟨5086155964549692629046577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6781541286066256838728769 5086155964549692629046577)
                    ·
                      refine ⟨3814616973412269471784933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5086155964549692629046577 3814616973412269471784933)
                      ·
                        rfl

theorem cell23_7428940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_7428940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428940 prefixEnd_7428940 := by exact prefixLift 7428940
  have htrace : WordTrace (prefixWord ++ tailWord_7428940) baseStart_7428940 baseEnd_7428940 := by
    simpa [prefixWord, tailWord_7428940, baseEnd_7428940] using wordTrace_append hprefix tailTrace_7428940
  have hstable : (prefixWord ++ tailWord_7428940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428940).length < 2 ^ (prefixWord ++ tailWord_7428940).sum := by decide
  have hdescent : baseEnd_7428940 < baseStart_7428940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428974 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_7428974 : Nat := 118140960795 + 7428974 * 2 ^ 59
def prefixEnd_7428974 : Nat := 4983230072969 + 3 ^ 40 * 7428974 * 2
def baseEnd_7428974 : Nat := 3814634431754522338759777

theorem tailTrace_7428974 : CollatzResearch.WordTrace tailWord_7428974 prefixEnd_7428974 3814634431754522338759777 := by
  unfold tailWord_7428974
  simp only [CollatzResearch.WordTrace]
  refine ⟨33869617723512930074068747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180637961192068960395033317 33869617723512930074068747)
  ·
    refine ⟨50804426585269395111103121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33869617723512930074068747 50804426585269395111103121)
    ·
      refine ⟨38103319938952046333327341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50804426585269395111103121 38103319938952046333327341)
      ·
        refine ⟨14288744977107017374997753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38103319938952046333327341 14288744977107017374997753)
        ·
          refine ⟨10716558732830263031248315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14288744977107017374997753 10716558732830263031248315)
          ·
            refine ⟨16074838099245394546872473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10716558732830263031248315 16074838099245394546872473)
            ·
              refine ⟨12056128574434045910154355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16074838099245394546872473 12056128574434045910154355)
              ·
                refine ⟨18084192861651068865231533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12056128574434045910154355 18084192861651068865231533)
                ·
                  refine ⟨6781572323119150824461825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18084192861651068865231533 6781572323119150824461825)
                  ·
                    refine ⟨5086179242339363118346369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6781572323119150824461825 5086179242339363118346369)
                    ·
                      refine ⟨3814634431754522338759777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5086179242339363118346369 3814634431754522338759777)
                      ·
                        rfl

theorem cell23_7428974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_7428974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428974 prefixEnd_7428974 := by exact prefixLift 7428974
  have htrace : WordTrace (prefixWord ++ tailWord_7428974) baseStart_7428974 baseEnd_7428974 := by
    simpa [prefixWord, tailWord_7428974, baseEnd_7428974] using wordTrace_append hprefix tailTrace_7428974
  have hstable : (prefixWord ++ tailWord_7428974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428974).length < 2 ^ (prefixWord ++ tailWord_7428974).sum := by decide
  have hdescent : baseEnd_7428974 < baseStart_7428974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428983 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 5, 3, 2]
def baseStart_7428983 : Nat := 118140960795 + 7428983 * 2 ^ 59
def prefixEnd_7428983 : Nat := 4983230072969 + 3 ^ 40 * 7428983 * 2
def baseEnd_7428983 : Nat := 3814639053080412803547235

theorem tailTrace_7428983 : CollatzResearch.WordTrace tailWord_7428983 prefixEnd_7428983 3814639053080412803547235 := by
  unfold tailWord_7428983
  simp only [CollatzResearch.WordTrace]
  refine ⟨270957270045070835129627603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180638180030047223419751735 270957270045070835129627603)
  ·
    refine ⟨406435905067606252694441405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270957270045070835129627603 406435905067606252694441405)
    ·
      refine ⟨152413464400352344760415527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406435905067606252694441405 152413464400352344760415527)
      ·
        refine ⟨228620196600528517140623291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152413464400352344760415527 228620196600528517140623291)
        ·
          refine ⟨342930294900792775710934937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228620196600528517140623291 342930294900792775710934937)
          ·
            refine ⟨257197721175594581783201203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342930294900792775710934937 257197721175594581783201203)
            ·
              refine ⟨385796581763391872674801805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257197721175594581783201203 385796581763391872674801805)
              ·
                refine ⟨144673718161271952253050677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385796581763391872674801805 144673718161271952253050677)
                ·
                  refine ⟨13563161077619245523723501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144673718161271952253050677 13563161077619245523723501)
                  ·
                    refine ⟨5086185404107217071396313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13563161077619245523723501 5086185404107217071396313)
                    ·
                      refine ⟨3814639053080412803547235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5086185404107217071396313 3814639053080412803547235)
                      ·
                        rfl

theorem cell23_7428983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 3, 2].length) (baseStart_7428983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428983 prefixEnd_7428983 := by exact prefixLift 7428983
  have htrace : WordTrace (prefixWord ++ tailWord_7428983) baseStart_7428983 baseEnd_7428983 := by
    simpa [prefixWord, tailWord_7428983, baseEnd_7428983] using wordTrace_append hprefix tailTrace_7428983
  have hstable : (prefixWord ++ tailWord_7428983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428983).length < 2 ^ (prefixWord ++ tailWord_7428983).sum := by decide
  have hdescent : baseEnd_7428983 < baseStart_7428983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429041 : List Nat := [1, 2, 2, 4, 4, 1, 2, 1, 2, 1, 3]
def baseStart_7429041 : Nat := 118140960795 + 7429041 * 2 ^ 59
def prefixEnd_7429041 : Nat := 4983230072969 + 3 ^ 40 * 7429041 * 2
def baseEnd_7429041 : Nat := 3814668834958373576621969

theorem tailTrace_7429041 : CollatzResearch.WordTrace tailWord_7429041 prefixEnd_7429041 3814668834958373576621969 := by
  unfold tailWord_7429041
  simp only [CollatzResearch.WordTrace]
  refine ⟨270959385478860711035238977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180639590319240474023492651 270959385478860711035238977)
  ·
    refine ⟨203219539109145533276429233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270959385478860711035238977 203219539109145533276429233)
    ·
      refine ⟨152414654331859149957321925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203219539109145533276429233 152414654331859149957321925)
      ·
        refine ⟨28577747687223590616997861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152414654331859149957321925 28577747687223590616997861)
        ·
          refine ⟨5358327691354423240687099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28577747687223590616997861 5358327691354423240687099)
          ·
            refine ⟨8037491537031634861030649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5358327691354423240687099 8037491537031634861030649)
            ·
              refine ⟨6028118652773726145772987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8037491537031634861030649 6028118652773726145772987)
              ·
                refine ⟨9042177979160589218659481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6028118652773726145772987 9042177979160589218659481)
                ·
                  refine ⟨6781633484370441913994611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9042177979160589218659481 6781633484370441913994611)
                  ·
                    refine ⟨10172450226555662870991917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6781633484370441913994611 10172450226555662870991917)
                    ·
                      refine ⟨3814668834958373576621969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10172450226555662870991917 3814668834958373576621969)
                      ·
                        rfl

theorem cell23_7429041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_7429041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429041 prefixEnd_7429041 := by exact prefixLift 7429041
  have htrace : WordTrace (prefixWord ++ tailWord_7429041) baseStart_7429041 baseEnd_7429041 := by
    simpa [prefixWord, tailWord_7429041, baseEnd_7429041] using wordTrace_append hprefix tailTrace_7429041
  have hstable : (prefixWord ++ tailWord_7429041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429041).length < 2 ^ (prefixWord ++ tailWord_7429041).sum := by decide
  have hdescent : baseEnd_7429041 < baseStart_7429041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429204 : List Nat := [2, 4, 1, 1, 1, 1, 2, 6, 1, 1, 3]
def baseStart_7429204 : Nat := 118140960795 + 7429204 * 2 ^ 59
def prefixEnd_7429204 : Nat := 4983230072969 + 3 ^ 40 * 7429204 * 2
def baseEnd_7429204 : Nat := 3814752532305056438883719

theorem tailTrace_7429204 : CollatzResearch.WordTrace tailWord_7429204 prefixEnd_7429204 3814752532305056438883719 := by
  unfold tailWord_7429204
  simp only [CollatzResearch.WordTrace]
  refine ⟨135482665288635094936711333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180643553718180126582281777 135482665288635094936711333)
  ·
    refine ⟨25402999741619080300633375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135482665288635094936711333 25402999741619080300633375)
    ·
      refine ⟨38104499612428620450950063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25402999741619080300633375 38104499612428620450950063)
      ·
        refine ⟨57156749418642930676425095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38104499612428620450950063 57156749418642930676425095)
        ·
          refine ⟨85735124127964396014637643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57156749418642930676425095 85735124127964396014637643)
          ·
            refine ⟨128602686191946594021956465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85735124127964396014637643 128602686191946594021956465)
            ·
              refine ⟨96452014643959945516467349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128602686191946594021956465 96452014643959945516467349)
              ·
                refine ⟨4521188186435622446084407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96452014643959945516467349 4521188186435622446084407)
                ·
                  refine ⟨6781782279653433669126611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521188186435622446084407 6781782279653433669126611)
                  ·
                    refine ⟨10172673419480150503689917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6781782279653433669126611 10172673419480150503689917)
                    ·
                      refine ⟨3814752532305056438883719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10172673419480150503689917 3814752532305056438883719)
                      ·
                        rfl

theorem cell23_7429204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_7429204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429204 prefixEnd_7429204 := by exact prefixLift 7429204
  have htrace : WordTrace (prefixWord ++ tailWord_7429204) baseStart_7429204 baseEnd_7429204 := by
    simpa [prefixWord, tailWord_7429204, baseEnd_7429204] using wordTrace_append hprefix tailTrace_7429204
  have hstable : (prefixWord ++ tailWord_7429204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429204).length < 2 ^ (prefixWord ++ tailWord_7429204).sum := by decide
  have hdescent : baseEnd_7429204 < baseStart_7429204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429210 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2]
def baseStart_7429210 : Nat := 118140960795 + 7429210 * 2 ^ 59
def prefixEnd_7429210 : Nat := 4983230072969 + 3 ^ 40 * 7429210 * 2
def baseEnd_7429210 : Nat := 3814755613188983415408691

theorem tailTrace_7429210 : CollatzResearch.WordTrace tailWord_7429210 prefixEnd_7429210 3814755613188983415408691 := by
  unfold tailWord_7429210
  simp only [CollatzResearch.WordTrace]
  refine ⟨67741387353812113224535271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180643699610165635265427389 67741387353812113224535271)
  ·
    refine ⟨101612081030718169836802907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67741387353812113224535271 101612081030718169836802907)
    ·
      refine ⟨152418121546077254755204361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101612081030718169836802907 152418121546077254755204361)
      ·
        refine ⟨114313591159557941066403271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152418121546077254755204361 114313591159557941066403271)
        ·
          refine ⟨171470386739336911599604907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114313591159557941066403271 171470386739336911599604907)
          ·
            refine ⟨257205580109005367399407361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171470386739336911599604907 257205580109005367399407361)
            ·
              refine ⟨192904185081754025549555521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257205580109005367399407361 192904185081754025549555521)
              ·
                refine ⟨144678138811315519162166641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192904185081754025549555521 144678138811315519162166641)
                ·
                  refine ⟨108508604108486639371624981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144678138811315519162166641 108508604108486639371624981)
                  ·
                    refine ⟨5086340817585311220544921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108508604108486639371624981 5086340817585311220544921)
                    ·
                      refine ⟨3814755613188983415408691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5086340817585311220544921 3814755613188983415408691)
                      ·
                        rfl

theorem cell23_7429210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_7429210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429210 prefixEnd_7429210 := by exact prefixLift 7429210
  have htrace : WordTrace (prefixWord ++ tailWord_7429210) baseStart_7429210 baseEnd_7429210 := by
    simpa [prefixWord, tailWord_7429210, baseEnd_7429210] using wordTrace_append hprefix tailTrace_7429210
  have hstable : (prefixWord ++ tailWord_7429210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429210).length < 2 ^ (prefixWord ++ tailWord_7429210).sum := by decide
  have hdescent : baseEnd_7429210 < baseStart_7429210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429273 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 5]
def baseStart_7429273 : Nat := 118140960795 + 7429273 * 2 ^ 59
def prefixEnd_7429273 : Nat := 4983230072969 + 3 ^ 40 * 7429273 * 2
def baseEnd_7429273 : Nat := 3814787962470216668920901

theorem tailTrace_7429273 : CollatzResearch.WordTrace tailWord_7429273 prefixEnd_7429273 3814787962470216668920901 := by
  unfold tailWord_7429273
  simp only [CollatzResearch.WordTrace]
  refine ⟨270967847214020214657684473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180645231476013476438456315 270967847214020214657684473)
  ·
    refine ⟨203225885410515160993263355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270967847214020214657684473 203225885410515160993263355)
    ·
      refine ⟨304838828115772741489895033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203225885410515160993263355 304838828115772741489895033)
      ·
        refine ⟨228629121086829556117421275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304838828115772741489895033 228629121086829556117421275)
        ·
          refine ⟨342943681630244334176131913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228629121086829556117421275 342943681630244334176131913)
          ·
            refine ⟨257207761222683250632098935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342943681630244334176131913 257207761222683250632098935)
            ·
              refine ⟨385811641834024875948148403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257207761222683250632098935 385811641834024875948148403)
              ·
                refine ⟨578717462751037313922222605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385811641834024875948148403 578717462751037313922222605)
                ·
                  refine ⟨217019048531638992720833477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 578717462751037313922222605 217019048531638992720833477)
                  ·
                    refine ⟨40691071599682311135156277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217019048531638992720833477 40691071599682311135156277)
                    ·
                      refine ⟨3814787962470216668920901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40691071599682311135156277 3814787962470216668920901)
                      ·
                        rfl

theorem cell23_7429273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_7429273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429273 prefixEnd_7429273 := by exact prefixLift 7429273
  have htrace : WordTrace (prefixWord ++ tailWord_7429273) baseStart_7429273 baseEnd_7429273 := by
    simpa [prefixWord, tailWord_7429273, baseEnd_7429273] using wordTrace_append hprefix tailTrace_7429273
  have hstable : (prefixWord ++ tailWord_7429273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429273).length < 2 ^ (prefixWord ++ tailWord_7429273).sum := by decide
  have hdescent : baseEnd_7429273 < baseStart_7429273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429277 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_7429277 : Nat := 118140960795 + 7429277 * 2 ^ 59
def prefixEnd_7429277 : Nat := 4983230072969 + 3 ^ 40 * 7429277 * 2
def baseEnd_7429277 : Nat := 3814790016392834653270883

theorem tailTrace_7429277 : CollatzResearch.WordTrace tailWord_7429277 prefixEnd_7429277 3814790016392834653270883 := by
  unfold tailWord_7429277
  simp only [CollatzResearch.WordTrace]
  refine ⟨270967993106005723340830085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180645328737337148893886723 270967993106005723340830085)
  ·
    refine ⟨50806498707376073126405641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270967993106005723340830085 50806498707376073126405641)
    ·
      refine ⟨38104874030532054844804231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50806498707376073126405641 38104874030532054844804231)
      ·
        refine ⟨57157311045798082267206347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38104874030532054844804231 57157311045798082267206347)
        ·
          refine ⟨85735966568697123400809521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57157311045798082267206347 85735966568697123400809521)
          ·
            refine ⟨64301974926522842550607141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85735966568697123400809521 64301974926522842550607141)
            ·
              refine ⟨12056620298723032978238839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64301974926522842550607141 12056620298723032978238839)
              ·
                refine ⟨18084930448084549467358259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12056620298723032978238839 18084930448084549467358259)
                ·
                  refine ⟨27127395672126824201037389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18084930448084549467358259 27127395672126824201037389)
                  ·
                    refine ⟨10172773377047559075389021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27127395672126824201037389 10172773377047559075389021)
                    ·
                      refine ⟨3814790016392834653270883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10172773377047559075389021 3814790016392834653270883)
                      ·
                        rfl

theorem cell23_7429277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_7429277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429277 prefixEnd_7429277 := by exact prefixLift 7429277
  have htrace : WordTrace (prefixWord ++ tailWord_7429277) baseStart_7429277 baseEnd_7429277 := by
    simpa [prefixWord, tailWord_7429277, baseEnd_7429277] using wordTrace_append hprefix tailTrace_7429277
  have hstable : (prefixWord ++ tailWord_7429277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429277).length < 2 ^ (prefixWord ++ tailWord_7429277).sum := by decide
  have hdescent : baseEnd_7429277 < baseStart_7429277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429320 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_7429320 : Nat := 118140960795 + 7429320 * 2 ^ 59
def prefixEnd_7429320 : Nat := 4983230072969 + 3 ^ 40 * 7429320 * 2
def baseEnd_7429320 : Nat := 3814812096060977985033185

theorem tailTrace_7429320 : CollatzResearch.WordTrace tailWord_7429320 prefixEnd_7429320 3814812096060977985033185 := by
  unfold tailWord_7429320
  simp only [CollatzResearch.WordTrace]
  refine ⟨135484780722424970842322707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180646374296566627789763609 135484780722424970842322707)
  ·
    refine ⟨203227171083637456263484061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135484780722424970842322707 203227171083637456263484061)
    ·
      refine ⟨76210189156364046098806523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203227171083637456263484061 76210189156364046098806523)
      ·
        refine ⟨114315283734546069148209785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76210189156364046098806523 114315283734546069148209785)
        ·
          refine ⟨85736462800909551861157339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114315283734546069148209785 85736462800909551861157339)
          ·
            refine ⟨128604694201364327791736009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85736462800909551861157339 128604694201364327791736009)
            ·
              refine ⟨96453520651023245843802007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128604694201364327791736009 96453520651023245843802007)
              ·
                refine ⟨144680280976534868765703011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96453520651023245843802007 144680280976534868765703011)
                ·
                  refine ⟨217020421464802303148554517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144680280976534868765703011 217020421464802303148554517)
                  ·
                    refine ⟨10172832256162607960088493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 217020421464802303148554517 10172832256162607960088493)
                    ·
                      refine ⟨3814812096060977985033185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10172832256162607960088493 3814812096060977985033185)
                      ·
                        rfl

theorem cell23_7429320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_7429320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429320 prefixEnd_7429320 := by exact prefixLift 7429320
  have htrace : WordTrace (prefixWord ++ tailWord_7429320) baseStart_7429320 baseEnd_7429320 := by
    simpa [prefixWord, tailWord_7429320, baseEnd_7429320] using wordTrace_append hprefix tailTrace_7429320
  have hstable : (prefixWord ++ tailWord_7429320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429320).length < 2 ^ (prefixWord ++ tailWord_7429320).sum := by decide
  have hdescent : baseEnd_7429320 < baseStart_7429320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429374 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 7]
def baseStart_7429374 : Nat := 118140960795 + 7429374 * 2 ^ 59
def prefixEnd_7429374 : Nat := 4983230072969 + 3 ^ 40 * 7429374 * 2
def baseEnd_7429374 : Nat := 423871091557368974861993

theorem tailTrace_7429374 : CollatzResearch.WordTrace tailWord_7429374 prefixEnd_7429374 423871091557368974861993 := by
  unfold tailWord_7429374
  simp only [CollatzResearch.WordTrace]
  refine ⟨33871441373331788613388897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180647687324436205938074117 33871441373331788613388897)
  ·
    refine ⟨25403581029998841460041673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33871441373331788613388897 25403581029998841460041673)
    ·
      refine ⟨19052685772499131095031255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25403581029998841460041673 19052685772499131095031255)
      ·
        refine ⟨28579028658748696642546883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19052685772499131095031255 28579028658748696642546883)
        ·
          refine ⟨42868542988123044963820325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28579028658748696642546883 42868542988123044963820325)
          ·
            refine ⟨8037851810273070930716311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42868542988123044963820325 8037851810273070930716311)
            ·
              refine ⟨12056777715409606396074467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8037851810273070930716311 12056777715409606396074467)
              ·
                refine ⟨18085166573114409594111701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12056777715409606396074467 18085166573114409594111701)
                ·
                  refine ⟨423871091557368974861993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18085166573114409594111701 423871091557368974861993)
                  ·
                    rfl

theorem cell23_7429374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_7429374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429374 prefixEnd_7429374 := by exact prefixLift 7429374
  have htrace : WordTrace (prefixWord ++ tailWord_7429374) baseStart_7429374 baseEnd_7429374 := by
    simpa [prefixWord, tailWord_7429374, baseEnd_7429374] using wordTrace_append hprefix tailTrace_7429374
  have hstable : (prefixWord ++ tailWord_7429374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429374).length < 2 ^ (prefixWord ++ tailWord_7429374).sum := by decide
  have hdescent : baseEnd_7429374 < baseStart_7429374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429420 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_7429420 : Nat := 118140960795 + 7429420 * 2 ^ 59
def prefixEnd_7429420 : Nat := 4983230072969 + 3 ^ 40 * 7429420 * 2
def baseEnd_7429420 : Nat := 3814863444126427593782725

theorem tailTrace_7429420 : CollatzResearch.WordTrace tailWord_7429420 prefixEnd_7429420 3814863444126427593782725 := by
  unfold tailWord_7429420
  simp only [CollatzResearch.WordTrace]
  refine ⟨135486604372243829381642857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180648805829658439175523809 135486604372243829381642857)
  ·
    refine ⟨101614953279182872036232143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135486604372243829381642857 101614953279182872036232143)
    ·
      refine ⟨152422429918774308054348215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101614953279182872036232143 152422429918774308054348215)
      ·
        refine ⟨228633644878161462081522323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152422429918774308054348215 228633644878161462081522323)
        ·
          refine ⟨342950467317242193122283485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228633644878161462081522323 342950467317242193122283485)
          ·
            refine ⟨128606425243965822420856307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342950467317242193122283485 128606425243965822420856307)
            ·
              refine ⟨192909637865948733631284461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128606425243965822420856307 192909637865948733631284461)
              ·
                refine ⟨72341114199730775111731673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192909637865948733631284461 72341114199730775111731673)
                ·
                  refine ⟨54255835649798081333798755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72341114199730775111731673 54255835649798081333798755)
                  ·
                    refine ⟨81383753474697122000698133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54255835649798081333798755 81383753474697122000698133)
                    ·
                      refine ⟨3814863444126427593782725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81383753474697122000698133 3814863444126427593782725)
                      ·
                        rfl

theorem cell23_7429420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_7429420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429420 prefixEnd_7429420 := by exact prefixLift 7429420
  have htrace : WordTrace (prefixWord ++ tailWord_7429420) baseStart_7429420 baseEnd_7429420 := by
    simpa [prefixWord, tailWord_7429420, baseEnd_7429420] using wordTrace_append hprefix tailTrace_7429420
  have hstable : (prefixWord ++ tailWord_7429420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429420).length < 2 ^ (prefixWord ++ tailWord_7429420).sum := by decide
  have hdescent : baseEnd_7429420 < baseStart_7429420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429441 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_7429441 : Nat := 118140960795 + 7429441 * 2 ^ 59
def prefixEnd_7429441 : Nat := 4983230072969 + 3 ^ 40 * 7429441 * 2
def baseEnd_7429441 : Nat := 3814874227220172011620129

theorem tailTrace_7429441 : CollatzResearch.WordTrace tailWord_7429441 prefixEnd_7429441 3814874227220172011620129 := by
  unfold tailWord_7429441
  simp only [CollatzResearch.WordTrace]
  refine ⟨270973974677411579349800177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180649316451607719566533451 270973974677411579349800177)
  ·
    refine ⟨203230481008058684512350133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270973974677411579349800177 203230481008058684512350133)
    ·
      refine ⟨19052857594505501673032825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203230481008058684512350133 19052857594505501673032825)
      ·
        refine ⟨14289643195879126254774619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19052857594505501673032825 14289643195879126254774619)
        ·
          refine ⟨21434464793818689382161929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14289643195879126254774619 21434464793818689382161929)
          ·
            refine ⟨16075848595364017036621447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21434464793818689382161929 16075848595364017036621447)
            ·
              refine ⟨24113772893046025554932171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16075848595364017036621447 24113772893046025554932171)
              ·
                refine ⟨36170659339569038332398257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24113772893046025554932171 36170659339569038332398257)
                ·
                  refine ⟨27127994504676778749298693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36170659339569038332398257 27127994504676778749298693)
                  ·
                    refine ⟨5086498969626896015493505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27127994504676778749298693 5086498969626896015493505)
                    ·
                      refine ⟨3814874227220172011620129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5086498969626896015493505 3814874227220172011620129)
                      ·
                        rfl

theorem cell23_7429441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_7429441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429441 prefixEnd_7429441 := by exact prefixLift 7429441
  have htrace : WordTrace (prefixWord ++ tailWord_7429441) baseStart_7429441 baseEnd_7429441 := by
    simpa [prefixWord, tailWord_7429441, baseEnd_7429441] using wordTrace_append hprefix tailTrace_7429441
  have hstable : (prefixWord ++ tailWord_7429441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429441).length < 2 ^ (prefixWord ++ tailWord_7429441).sum := by decide
  have hdescent : baseEnd_7429441 < baseStart_7429441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429447 : List Nat := [1, 1, 4, 1, 2, 3, 2, 3, 6]
def baseStart_7429447 : Nat := 118140960795 + 7429447 * 2 ^ 59
def prefixEnd_7429447 : Nat := 4983230072969 + 3 ^ 40 * 7429447 * 2
def baseEnd_7429447 : Nat := 423875256456010998682789

theorem tailTrace_7429447 : CollatzResearch.WordTrace tailWord_7429447 prefixEnd_7429447 423875256456010998682789 := by
  unfold tailWord_7429447
  simp only [CollatzResearch.WordTrace]
  refine ⟨270974193515389842374518595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180649462343593228249679063 270974193515389842374518595)
  ·
    refine ⟨406461290273084763561777893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270974193515389842374518595 406461290273084763561777893)
    ·
      refine ⟨76211491926203393167833355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 406461290273084763561777893 76211491926203393167833355)
      ·
        refine ⟨114317237889305089751750033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76211491926203393167833355 114317237889305089751750033)
        ·
          refine ⟨85737928416978817313812525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114317237889305089751750033 85737928416978817313812525)
          ·
            refine ⟨32151723156367056492679697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85737928416978817313812525 32151723156367056492679697)
            ·
              refine ⟨24113792367275292369509773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32151723156367056492679697 24113792367275292369509773)
              ·
                refine ⟨9042672137728234638566165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24113792367275292369509773 9042672137728234638566165)
                ·
                  refine ⟨423875256456010998682789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9042672137728234638566165 423875256456010998682789)
                  ·
                    rfl

theorem cell23_7429447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 6].length) (baseStart_7429447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429447 prefixEnd_7429447 := by exact prefixLift 7429447
  have htrace : WordTrace (prefixWord ++ tailWord_7429447) baseStart_7429447 baseEnd_7429447 := by
    simpa [prefixWord, tailWord_7429447, baseEnd_7429447] using wordTrace_append hprefix tailTrace_7429447
  have hstable : (prefixWord ++ tailWord_7429447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429447).length < 2 ^ (prefixWord ++ tailWord_7429447).sum := by decide
  have hdescent : baseEnd_7429447 < baseStart_7429447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429461 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 2, 2, 3]
def baseStart_7429461 : Nat := 118140960795 + 7429461 * 2 ^ 59
def prefixEnd_7429461 : Nat := 4983230072969 + 3 ^ 40 * 7429461 * 2
def baseEnd_7429461 : Nat := 3814884496833261933370037

theorem tailTrace_7429461 : CollatzResearch.WordTrace tailWord_7429461 prefixEnd_7429461 3814884496833261933370037 := by
  unfold tailWord_7429461
  simp only [CollatzResearch.WordTrace]
  refine ⟨270974704137339122765528237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180649802758226081843685491 270974704137339122765528237)
  ·
    refine ⟨101615514051502171037073089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270974704137339122765528237 101615514051502171037073089)
    ·
      refine ⟨76211635538626628277804817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101615514051502171037073089 76211635538626628277804817)
      ·
        refine ⟨57158726653969971208353613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76211635538626628277804817 57158726653969971208353613)
        ·
          refine ⟨21434522495238739203132605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57158726653969971208353613 21434522495238739203132605)
          ·
            refine ⟨8037945935714527201174727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21434522495238739203132605 8037945935714527201174727)
            ·
              refine ⟨12056918903571790801762091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8037945935714527201174727 12056918903571790801762091)
              ·
                refine ⟨18085378355357686202643137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12056918903571790801762091 18085378355357686202643137)
                ·
                  refine ⟨13564033766518264651982353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18085378355357686202643137 13564033766518264651982353)
                  ·
                    refine ⟨10173025324888698488986765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13564033766518264651982353 10173025324888698488986765)
                    ·
                      refine ⟨3814884496833261933370037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10173025324888698488986765 3814884496833261933370037)
                      ·
                        rfl

theorem cell23_7429461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_7429461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429461 prefixEnd_7429461 := by exact prefixLift 7429461
  have htrace : WordTrace (prefixWord ++ tailWord_7429461) baseStart_7429461 baseEnd_7429461 := by
    simpa [prefixWord, tailWord_7429461, baseEnd_7429461] using wordTrace_append hprefix tailTrace_7429461
  have hstable : (prefixWord ++ tailWord_7429461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429461).length < 2 ^ (prefixWord ++ tailWord_7429461).sum := by decide
  have hdescent : baseEnd_7429461 < baseStart_7429461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429497 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 5, 1, 4]
def baseStart_7429497 : Nat := 118140960795 + 7429497 * 2 ^ 59
def prefixEnd_7429497 : Nat := 4983230072969 + 3 ^ 40 * 7429497 * 2
def baseEnd_7429497 : Nat := 3814902982136823792519871

theorem tailTrace_7429497 : CollatzResearch.WordTrace tailWord_7429497 prefixEnd_7429497 3814902982136823792519871 := by
  unfold tailWord_7429497
  simp only [CollatzResearch.WordTrace]
  refine ⟨270976017165208700913838745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180650678110139133942559163 270976017165208700913838745)
  ·
    refine ⟨203232012873906525685379059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270976017165208700913838745 203232012873906525685379059)
    ·
      refine ⟨304848019310859788528068589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203232012873906525685379059 304848019310859788528068589)
      ·
        refine ⟨114318007241572420698025721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304848019310859788528068589 114318007241572420698025721)
        ·
          refine ⟨85738505431179315523519291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114318007241572420698025721 85738505431179315523519291)
          ·
            refine ⟨128607758146768973285278937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85738505431179315523519291 128607758146768973285278937)
            ·
              refine ⟨96455818610076729963959203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128607758146768973285278937 96455818610076729963959203)
              ·
                refine ⟨144683727915115094945938805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96455818610076729963959203 144683727915115094945938805)
                ·
                  refine ⟨13564099492042040151181763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144683727915115094945938805 13564099492042040151181763)
                  ·
                    refine ⟨20346149238063060226772645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13564099492042040151181763 20346149238063060226772645)
                    ·
                      refine ⟨3814902982136823792519871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20346149238063060226772645 3814902982136823792519871)
                      ·
                        rfl

theorem cell23_7429497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_7429497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429497 prefixEnd_7429497 := by exact prefixLift 7429497
  have htrace : WordTrace (prefixWord ++ tailWord_7429497) baseStart_7429497 baseEnd_7429497 := by
    simpa [prefixWord, tailWord_7429497, baseEnd_7429497] using wordTrace_append hprefix tailTrace_7429497
  have hstable : (prefixWord ++ tailWord_7429497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429497).length < 2 ^ (prefixWord ++ tailWord_7429497).sum := by decide
  have hdescent : baseEnd_7429497 < baseStart_7429497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429527 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_7429527 : Nat := 118140960795 + 7429527 * 2 ^ 59
def prefixEnd_7429527 : Nat := 4983230072969 + 3 ^ 40 * 7429527 * 2
def baseEnd_7429527 : Nat := 3814918386556458675144733

theorem tailTrace_7429527 : CollatzResearch.WordTrace tailWord_7429527 prefixEnd_7429527 3814918386556458675144733 := by
  unfold tailWord_7429527
  simp only [CollatzResearch.WordTrace]
  refine ⟨270977111355100016037430835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180651407570066677358287223 270977111355100016037430835)
  ·
    refine ⟨406465667032650024056146253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270977111355100016037430835 406465667032650024056146253)
    ·
      refine ⟨152424625137243759021054845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406465667032650024056146253 152424625137243759021054845)
      ·
        refine ⟨57159234426466409632895567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152424625137243759021054845 57159234426466409632895567)
        ·
          refine ⟨85738851639699614449343351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57159234426466409632895567 85738851639699614449343351)
          ·
            refine ⟨128608277459549421674015027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85738851639699614449343351 128608277459549421674015027)
            ·
              refine ⟨192912416189324132511022541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128608277459549421674015027 192912416189324132511022541)
              ·
                refine ⟨72342156070996549691633453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192912416189324132511022541 72342156070996549691633453)
                ·
                  refine ⟨27128308526623706134362545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72342156070996549691633453 27128308526623706134362545)
                  ·
                    refine ⟨20346231394967779600771909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27128308526623706134362545 20346231394967779600771909)
                    ·
                      refine ⟨3814918386556458675144733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20346231394967779600771909 3814918386556458675144733)
                      ·
                        rfl

theorem cell23_7429527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_7429527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429527 prefixEnd_7429527 := by exact prefixLift 7429527
  have htrace : WordTrace (prefixWord ++ tailWord_7429527) baseStart_7429527 baseEnd_7429527 := by
    simpa [prefixWord, tailWord_7429527, baseEnd_7429527] using wordTrace_append hprefix tailTrace_7429527
  have hstable : (prefixWord ++ tailWord_7429527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429527).length < 2 ^ (prefixWord ++ tailWord_7429527).sum := by decide
  have hdescent : baseEnd_7429527 < baseStart_7429527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429548 : List Nat := [2, 2, 1, 1, 1, 1, 4, 6, 1, 2, 2]
def baseStart_7429548 : Nat := 118140960795 + 7429548 * 2 ^ 59
def prefixEnd_7429548 : Nat := 4983230072969 + 3 ^ 40 * 7429548 * 2
def baseEnd_7429548 : Nat := 3814929169650203092982137

theorem tailTrace_7429548 : CollatzResearch.WordTrace tailWord_7429548 prefixEnd_7429548 3814929169650203092982137 := by
  unfold tailWord_7429548
  simp only [CollatzResearch.WordTrace]
  refine ⟨135488938644011968311972649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180651918192015957749296865 135488938644011968311972649)
  ·
    refine ⟨101616703983008976233979487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135488938644011968311972649 101616703983008976233979487)
    ·
      refine ⟨152425055974513464350969231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101616703983008976233979487 152425055974513464350969231)
      ·
        refine ⟨228637583961770196526453847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152425055974513464350969231 228637583961770196526453847)
        ·
          refine ⟨342956375942655294789680771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228637583961770196526453847 342956375942655294789680771)
          ·
            refine ⟨514434563913982942184521157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342956375942655294789680771 514434563913982942184521157)
            ·
              refine ⟨96456480733871801659597717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 514434563913982942184521157 96456480733871801659597717)
              ·
                refine ⟨4521397534400240702793643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96456480733871801659597717 4521397534400240702793643)
                ·
                  refine ⟨6782096301600361054190465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521397534400240702793643 6782096301600361054190465)
                  ·
                    refine ⟨5086572226200270790642849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6782096301600361054190465 5086572226200270790642849)
                    ·
                      refine ⟨3814929169650203092982137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5086572226200270790642849 3814929169650203092982137)
                      ·
                        rfl

theorem cell23_7429548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 1, 2, 2].length) (baseStart_7429548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429548 prefixEnd_7429548 := by exact prefixLift 7429548
  have htrace : WordTrace (prefixWord ++ tailWord_7429548) baseStart_7429548 baseEnd_7429548 := by
    simpa [prefixWord, tailWord_7429548, baseEnd_7429548] using wordTrace_append hprefix tailTrace_7429548
  have hstable : (prefixWord ++ tailWord_7429548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429548).length < 2 ^ (prefixWord ++ tailWord_7429548).sum := by decide
  have hdescent : baseEnd_7429548 < baseStart_7429548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429591 : List Nat := [1, 1, 3, 2, 1, 1, 1, 7, 1, 3, 2]
def baseStart_7429591 : Nat := 118140960795 + 7429591 * 2 ^ 59
def prefixEnd_7429591 : Nat := 4983230072969 + 3 ^ 40 * 7429591 * 2
def baseEnd_7429591 : Nat := 3814951249318346424744439

theorem tailTrace_7429591 : CollatzResearch.WordTrace tailWord_7429591 prefixEnd_7429591 3814951249318346424744439 := by
  unfold tailWord_7429591
  simp only [CollatzResearch.WordTrace]
  refine ⟨270979445626868154967760627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180652963751245436645173751 270979445626868154967760627)
  ·
    refine ⟨406469168440302232451640941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270979445626868154967760627 406469168440302232451640941)
    ·
      refine ⟨152425938165113337169365353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406469168440302232451640941 152425938165113337169365353)
      ·
        refine ⟨114319453623835002877024015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152425938165113337169365353 114319453623835002877024015)
        ·
          refine ⟨171479180435752504315536023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114319453623835002877024015 171479180435752504315536023)
          ·
            refine ⟨257218770653628756473304035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171479180435752504315536023 257218770653628756473304035)
            ·
              refine ⟨385828155980443134709956053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257218770653628756473304035 385828155980443134709956053)
              ·
                refine ⟨9042847405791635969764595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 385828155980443134709956053 9042847405791635969764595)
                ·
                  refine ⟨13564271108687453954646893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9042847405791635969764595 13564271108687453954646893)
                  ·
                    refine ⟨5086601665757795232992585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13564271108687453954646893 5086601665757795232992585)
                    ·
                      refine ⟨3814951249318346424744439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5086601665757795232992585 3814951249318346424744439)
                      ·
                        rfl

theorem cell23_7429591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_7429591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429591 prefixEnd_7429591 := by exact prefixLift 7429591
  have htrace : WordTrace (prefixWord ++ tailWord_7429591) baseStart_7429591 baseEnd_7429591 := by
    simpa [prefixWord, tailWord_7429591, baseEnd_7429591] using wordTrace_append hprefix tailTrace_7429591
  have hstable : (prefixWord ++ tailWord_7429591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429591).length < 2 ^ (prefixWord ++ tailWord_7429591).sum := by decide
  have hdescent : baseEnd_7429591 < baseStart_7429591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429614 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_7429614 : Nat := 118140960795 + 7429614 * 2 ^ 59
def prefixEnd_7429614 : Nat := 4983230072969 + 3 ^ 40 * 7429614 * 2
def baseEnd_7429614 : Nat := 1271654353124466611585611

theorem tailTrace_7429614 : CollatzResearch.WordTrace tailWord_7429614 prefixEnd_7429614 1271654353124466611585611 := by
  unfold tailWord_7429614
  simp only [CollatzResearch.WordTrace]
  refine ⟨33872535563223103736980987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180653523003856553263898597 33872535563223103736980987)
  ·
    refine ⟨50808803344834655605471481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33872535563223103736980987 50808803344834655605471481)
    ·
      refine ⟨38106602508625991704103611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50808803344834655605471481 38106602508625991704103611)
      ·
        refine ⟨57159903762938987556155417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38106602508625991704103611 57159903762938987556155417)
        ·
          refine ⟨42869927822204240667116563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57159903762938987556155417 42869927822204240667116563)
          ·
            refine ⟨64304891733306361000674845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42869927822204240667116563 64304891733306361000674845)
            ·
              refine ⟨24114334399989885375253067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64304891733306361000674845 24114334399989885375253067)
              ·
                refine ⟨36171501599984828062879601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24114334399989885375253067 36171501599984828062879601)
                ·
                  refine ⟨27128626199988621047159701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36171501599984828062879601 27128626199988621047159701)
                  ·
                    refine ⟨1271654353124466611585611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27128626199988621047159701 1271654353124466611585611)
                    ·
                      rfl

theorem cell23_7429614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_7429614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429614 prefixEnd_7429614 := by exact prefixLift 7429614
  have htrace : WordTrace (prefixWord ++ tailWord_7429614) baseStart_7429614 baseEnd_7429614 := by
    simpa [prefixWord, tailWord_7429614, baseEnd_7429614] using wordTrace_append hprefix tailTrace_7429614
  have hstable : (prefixWord ++ tailWord_7429614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429614).length < 2 ^ (prefixWord ++ tailWord_7429614).sum := by decide
  have hdescent : baseEnd_7429614 < baseStart_7429614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429627 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 7]
def baseStart_7429627 : Nat := 118140960795 + 7429627 * 2 ^ 59
def prefixEnd_7429627 : Nat := 4983230072969 + 3 ^ 40 * 7429627 * 2
def baseEnd_7429627 : Nat := 423885526069100920432697

theorem tailTrace_7429627 : CollatzResearch.WordTrace tailWord_7429627 prefixEnd_7429627 423885526069100920432697 := by
  unfold tailWord_7429627
  simp only [CollatzResearch.WordTrace]
  refine ⟨270980758654737733116071135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180653839103158488744047423 270980758654737733116071135)
  ·
    refine ⟨406471137982106599674106703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270980758654737733116071135 406471137982106599674106703)
    ·
      refine ⟨609706706973159899511160055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406471137982106599674106703 609706706973159899511160055)
      ·
        refine ⟨914560060459739849266740083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609706706973159899511160055 914560060459739849266740083)
        ·
          refine ⟨1371840090689609773900110125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914560060459739849266740083 1371840090689609773900110125)
          ·
            refine ⟨514440034008603665212541297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1371840090689609773900110125 514440034008603665212541297)
            ·
              refine ⟨385830025506452748909405973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514440034008603665212541297 385830025506452748909405973)
              ·
                refine ⟨18085782445614972605128405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 385830025506452748909405973 18085782445614972605128405)
                ·
                  refine ⟨423885526069100920432697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18085782445614972605128405 423885526069100920432697)
                  ·
                    rfl

theorem cell23_7429627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 7].length) (baseStart_7429627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429627 prefixEnd_7429627 := by exact prefixLift 7429627
  have htrace : WordTrace (prefixWord ++ tailWord_7429627) baseStart_7429627 baseEnd_7429627 := by
    simpa [prefixWord, tailWord_7429627, baseEnd_7429627] using wordTrace_append hprefix tailTrace_7429627
  have hstable : (prefixWord ++ tailWord_7429627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429627).length < 2 ^ (prefixWord ++ tailWord_7429627).sum := by decide
  have hdescent : baseEnd_7429627 < baseStart_7429627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429637 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_7429637 : Nat := 118140960795 + 7429637 * 2 ^ 59
def prefixEnd_7429637 : Nat := 4983230072969 + 3 ^ 40 * 7429637 * 2
def baseEnd_7429637 : Nat := 3814974869428453244769227

theorem tailTrace_7429637 : CollatzResearch.WordTrace tailWord_7429637 prefixEnd_7429637 3814974869428453244769227 := by
  unfold tailWord_7429637
  simp only [CollatzResearch.WordTrace]
  refine ⟨270981123384701504823935165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180654082256467669882623443 270981123384701504823935165)
  ·
    refine ⟨101617921269263064308975687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270981123384701504823935165 101617921269263064308975687)
    ·
      refine ⟨152426881903894596463463531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101617921269263064308975687 152426881903894596463463531)
      ·
        refine ⟨228640322855841894695195297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152426881903894596463463531 228640322855841894695195297)
        ·
          refine ⟨171480242141881421021396473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228640322855841894695195297 171480242141881421021396473)
          ·
            refine ⟨128610181606411065766047355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171480242141881421021396473 128610181606411065766047355)
            ·
              refine ⟨192915272409616598649071033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128610181606411065766047355 192915272409616598649071033)
              ·
                refine ⟨144686454307212448986803275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192915272409616598649071033 144686454307212448986803275)
                ·
                  refine ⟨217029681460818673480204913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144686454307212448986803275 217029681460818673480204913)
                  ·
                    refine ⟨162772261095614005110153685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 217029681460818673480204913 162772261095614005110153685)
                    ·
                      refine ⟨3814974869428453244769227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162772261095614005110153685 3814974869428453244769227)
                      ·
                        rfl

theorem cell23_7429637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_7429637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429637 prefixEnd_7429637 := by exact prefixLift 7429637
  have htrace : WordTrace (prefixWord ++ tailWord_7429637) baseStart_7429637 baseEnd_7429637 := by
    simpa [prefixWord, tailWord_7429637, baseEnd_7429637] using wordTrace_append hprefix tailTrace_7429637
  have hstable : (prefixWord ++ tailWord_7429637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429637).length < 2 ^ (prefixWord ++ tailWord_7429637).sum := by decide
  have hdescent : baseEnd_7429637 < baseStart_7429637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429657 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 5, 7]
def baseStart_7429657 : Nat := 118140960795 + 7429657 * 2 ^ 59
def prefixEnd_7429657 : Nat := 4983230072969 + 3 ^ 40 * 7429657 * 2
def baseEnd_7429657 : Nat := 1271661713013847722173045

theorem tailTrace_7429657 : CollatzResearch.WordTrace tailWord_7429657 prefixEnd_7429657 1271661713013847722173045 := by
  unfold tailWord_7429657
  simp only [CollatzResearch.WordTrace]
  refine ⟨270981852844629048239663225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180654568563086032159775483 270981852844629048239663225)
  ·
    refine ⟨203236389633471786179747419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270981852844629048239663225 203236389633471786179747419)
    ·
      refine ⟨304854584450207679269621129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203236389633471786179747419 304854584450207679269621129)
      ·
        refine ⟨228640938337655759452215847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304854584450207679269621129 228640938337655759452215847)
        ·
          refine ⟨342961407506483639178323771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228640938337655759452215847 342961407506483639178323771)
          ·
            refine ⟨514442111259725458767485657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342961407506483639178323771 514442111259725458767485657)
            ·
              refine ⟨385831583444794094075614243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514442111259725458767485657 385831583444794094075614243)
              ·
                refine ⟨578747375167191141113421365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385831583444794094075614243 578747375167191141113421365)
                ·
                  refine ⟨54257566421924169479383253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 578747375167191141113421365 54257566421924169479383253)
                  ·
                    refine ⟨1271661713013847722173045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54257566421924169479383253 1271661713013847722173045)
                    ·
                      rfl

theorem cell23_7429657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_7429657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429657 prefixEnd_7429657 := by exact prefixLift 7429657
  have htrace : WordTrace (prefixWord ++ tailWord_7429657) baseStart_7429657 baseEnd_7429657 := by
    simpa [prefixWord, tailWord_7429657, baseEnd_7429657] using wordTrace_append hprefix tailTrace_7429657
  have hstable : (prefixWord ++ tailWord_7429657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429657).length < 2 ^ (prefixWord ++ tailWord_7429657).sum := by decide
  have hdescent : baseEnd_7429657 < baseStart_7429657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429661 : List Nat := [1, 4, 2, 2, 1, 1, 1, 6, 5]
def baseStart_7429661 : Nat := 118140960795 + 7429661 * 2 ^ 59
def prefixEnd_7429661 : Nat := 4983230072969 + 3 ^ 40 * 7429661 * 2
def baseEnd_7429661 : Nat := 423887465884906794541013

theorem tailTrace_7429661 : CollatzResearch.WordTrace tailWord_7429661 prefixEnd_7429661 423887465884906794541013 := by
  unfold tailWord_7429661
  simp only [CollatzResearch.WordTrace]
  refine ⟨270981998736614556922808837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180654665824409704615205891 270981998736614556922808837)
  ·
    refine ⟨50809124763115229423026657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270981998736614556922808837 50809124763115229423026657)
    ·
      refine ⟨38106843572336422067269993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50809124763115229423026657 38106843572336422067269993)
      ·
        refine ⟨28580132679252316550452495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38106843572336422067269993 28580132679252316550452495)
        ·
          refine ⟨42870199018878474825678743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28580132679252316550452495 42870199018878474825678743)
          ·
            refine ⟨64305298528317712238518115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42870199018878474825678743 64305298528317712238518115)
            ·
              refine ⟨96457947792476568357777173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64305298528317712238518115 96457947792476568357777173)
              ·
                refine ⟨4521466302772339141770805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96457947792476568357777173 4521466302772339141770805)
                ·
                  refine ⟨423887465884906794541013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4521466302772339141770805 423887465884906794541013)
                  ·
                    rfl

theorem cell23_7429661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_7429661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429661 prefixEnd_7429661 := by exact prefixLift 7429661
  have htrace : WordTrace (prefixWord ++ tailWord_7429661) baseStart_7429661 baseEnd_7429661 := by
    simpa [prefixWord, tailWord_7429661, baseEnd_7429661] using wordTrace_append hprefix tailTrace_7429661
  have hstable : (prefixWord ++ tailWord_7429661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429661).length < 2 ^ (prefixWord ++ tailWord_7429661).sum := by decide
  have hdescent : baseEnd_7429661 < baseStart_7429661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429672 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_7429672 : Nat := 118140960795 + 7429672 * 2 ^ 59
def prefixEnd_7429672 : Nat := 4983230072969 + 3 ^ 40 * 7429672 * 2
def baseEnd_7429672 : Nat := 3814992841251360607831567

theorem tailTrace_7429672 : CollatzResearch.WordTrace tailWord_7429672 prefixEnd_7429672 3814992841251360607831567 := by
  unfold tailWord_7429672
  simp only [CollatzResearch.WordTrace]
  refine ⟨135491199969787352900729635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180654933293049803867639513 135491199969787352900729635)
  ·
    refine ⟨203236799954681029351094453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135491199969787352900729635 203236799954681029351094453)
    ·
      refine ⟨19053449995751346501665105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203236799954681029351094453 19053449995751346501665105)
      ·
        refine ⟨14290087496813509876248829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19053449995751346501665105 14290087496813509876248829)
        ·
          refine ⟨5358782811305066203593311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14290087496813509876248829 5358782811305066203593311)
          ·
            refine ⟨8038174216957599305389967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5358782811305066203593311 8038174216957599305389967)
            ·
              refine ⟨12057261325436398958084951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8038174216957599305389967 12057261325436398958084951)
              ·
                refine ⟨18085891988154598437127427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12057261325436398958084951 18085891988154598437127427)
                ·
                  refine ⟨27128837982231897655691141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18085891988154598437127427 27128837982231897655691141)
                  ·
                    refine ⟨5086657121668480810442089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27128837982231897655691141 5086657121668480810442089)
                    ·
                      refine ⟨3814992841251360607831567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5086657121668480810442089 3814992841251360607831567)
                      ·
                        rfl

theorem cell23_7429672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_7429672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429672 prefixEnd_7429672 := by exact prefixLift 7429672
  have htrace : WordTrace (prefixWord ++ tailWord_7429672) baseStart_7429672 baseEnd_7429672 := by
    simpa [prefixWord, tailWord_7429672, baseEnd_7429672] using wordTrace_append hprefix tailTrace_7429672
  have hstable : (prefixWord ++ tailWord_7429672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429672).length < 2 ^ (prefixWord ++ tailWord_7429672).sum := by decide
  have hdescent : baseEnd_7429672 < baseStart_7429672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429674 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 3, 7]
def baseStart_7429674 : Nat := 118140960795 + 7429674 * 2 ^ 59
def prefixEnd_7429674 : Nat := 4983230072969 + 3 ^ 40 * 7429674 * 2
def baseEnd_7429674 : Nat := 1271664622737556533335519

theorem tailTrace_7429674 : CollatzResearch.WordTrace tailWord_7429674 prefixEnd_7429674 1271664622737556533335519 := by
  unfold tailWord_7429674
  simp only [CollatzResearch.WordTrace]
  refine ⟨67745618221391865035758019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180654981923711640095354717 67745618221391865035758019)
  ·
    refine ⟨101618427332087797553637029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67745618221391865035758019 101618427332087797553637029)
    ·
      refine ⟨19053455124766462041306943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101618427332087797553637029 19053455124766462041306943)
      ·
        refine ⟨28580182687149693061960415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19053455124766462041306943 28580182687149693061960415)
        ·
          refine ⟨42870274030724539592940623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28580182687149693061960415 42870274030724539592940623)
          ·
            refine ⟨64305411046086809389410935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42870274030724539592940623 64305411046086809389410935)
            ·
              refine ⟨96458116569130214084116403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64305411046086809389410935 96458116569130214084116403)
              ·
                refine ⟨144687174853695321126174605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96458116569130214084116403 144687174853695321126174605)
                ·
                  refine ⟨54257690570135745422315477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144687174853695321126174605 54257690570135745422315477)
                  ·
                    refine ⟨1271664622737556533335519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54257690570135745422315477 1271664622737556533335519)
                    ·
                      rfl

theorem cell23_7429674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_7429674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429674 prefixEnd_7429674 := by exact prefixLift 7429674
  have htrace : WordTrace (prefixWord ++ tailWord_7429674) baseStart_7429674 baseEnd_7429674 := by
    simpa [prefixWord, tailWord_7429674, baseEnd_7429674] using wordTrace_append hprefix tailTrace_7429674
  have hstable : (prefixWord ++ tailWord_7429674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429674).length < 2 ^ (prefixWord ++ tailWord_7429674).sum := by decide
  have hdescent : baseEnd_7429674 < baseStart_7429674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429811 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 4, 4]
def baseStart_7429811 : Nat := 118140960795 + 7429811 * 2 ^ 59
def prefixEnd_7429811 : Nat := 4983230072969 + 3 ^ 40 * 7429811 * 2
def baseEnd_7429811 : Nat := 1271688071687445187997809

theorem tailTrace_7429811 : CollatzResearch.WordTrace tailWord_7429811 prefixEnd_7429811 1271688071687445187997809 := by
  unfold tailWord_7429811
  simp only [CollatzResearch.WordTrace]
  refine ⟨270987469686071132540769287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180658313124047421693846191 270987469686071132540769287)
  ·
    refine ⟨406481204529106698811153931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270987469686071132540769287 406481204529106698811153931)
    ·
      refine ⟨609721806793660048216730897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406481204529106698811153931 609721806793660048216730897)
      ·
        refine ⟨457291355095245036162548173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609721806793660048216730897 457291355095245036162548173)
        ·
          refine ⟨171484258160716888560955565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457291355095245036162548173 171484258160716888560955565)
          ·
            refine ⟨64306596810268833210358337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171484258160716888560955565 64306596810268833210358337)
            ·
              refine ⟨48229947607701624907768753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64306596810268833210358337 48229947607701624907768753)
              ·
                refine ⟨36172460705776218680826565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48229947607701624907768753 36172460705776218680826565)
                ·
                  refine ⟨6782336382333041002654981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36172460705776218680826565 6782336382333041002654981)
                  ·
                    refine ⟨1271688071687445187997809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6782336382333041002654981 1271688071687445187997809)
                    ·
                      rfl

theorem cell23_7429811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 4].length) (baseStart_7429811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429811 prefixEnd_7429811 := by exact prefixLift 7429811
  have htrace : WordTrace (prefixWord ++ tailWord_7429811) baseStart_7429811 baseEnd_7429811 := by
    simpa [prefixWord, tailWord_7429811, baseEnd_7429811] using wordTrace_append hprefix tailTrace_7429811
  have hstable : (prefixWord ++ tailWord_7429811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429811).length < 2 ^ (prefixWord ++ tailWord_7429811).sum := by decide
  have hdescent : baseEnd_7429811 < baseStart_7429811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429815 : List Nat := [1, 1, 3, 1, 5, 3, 2, 1, 1, 5]
def baseStart_7429815 : Nat := 118140960795 + 7429815 * 2 ^ 59
def prefixEnd_7429815 : Nat := 4983230072969 + 3 ^ 40 * 7429815 * 2
def baseEnd_7429815 : Nat := 1271688756328317849447803

theorem tailTrace_7429815 : CollatzResearch.WordTrace tailWord_7429815 prefixEnd_7429815 1271688756328317849447803 := by
  unfold tailWord_7429815
  simp only [CollatzResearch.WordTrace]
  refine ⟨270987615578056641223914899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180658410385371094149276599 270987615578056641223914899)
  ·
    refine ⟨406481423367084961835872349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270987615578056641223914899 406481423367084961835872349)
    ·
      refine ⟨152430533762656860688452131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406481423367084961835872349 152430533762656860688452131)
      ·
        refine ⟨228645800643985291032678197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152430533762656860688452131 228645800643985291032678197)
        ·
          refine ⟨21435543810373621034313581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228645800643985291032678197 21435543810373621034313581)
          ·
            refine ⟨8038328928890107887867593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21435543810373621034313581 8038328928890107887867593)
            ·
              refine ⟨6028746696667580915900695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8038328928890107887867593 6028746696667580915900695)
              ·
                refine ⟨9043120045001371373851043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6028746696667580915900695 9043120045001371373851043)
                ·
                  refine ⟨13564680067502057060776565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9043120045001371373851043 13564680067502057060776565)
                  ·
                    refine ⟨1271688756328317849447803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13564680067502057060776565 1271688756328317849447803)
                    ·
                      rfl

theorem cell23_7429815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_7429815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429815 prefixEnd_7429815 := by exact prefixLift 7429815
  have htrace : WordTrace (prefixWord ++ tailWord_7429815) baseStart_7429815 baseEnd_7429815 := by
    simpa [prefixWord, tailWord_7429815, baseEnd_7429815] using wordTrace_append hprefix tailTrace_7429815
  have hstable : (prefixWord ++ tailWord_7429815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429815).length < 2 ^ (prefixWord ++ tailWord_7429815).sum := by decide
  have hdescent : baseEnd_7429815 < baseStart_7429815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429818 : List Nat := [3, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4]
def baseStart_7429818 : Nat := 118140960795 + 7429818 * 2 ^ 59
def prefixEnd_7429818 : Nat := 4983230072969 + 3 ^ 40 * 7429818 * 2
def baseEnd_7429818 : Nat := 3815067809426917036605895

theorem tailTrace_7429818 : CollatzResearch.WordTrace tailWord_7429818 prefixEnd_7429818 3815067809426917036605895 := by
  unfold tailWord_7429818
  simp only [CollatzResearch.WordTrace]
  refine ⟨67746931249261443184068527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180658483331363848490849405 67746931249261443184068527)
  ·
    refine ⟨101620396873892164776102791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67746931249261443184068527 101620396873892164776102791)
    ·
      refine ⟨152430595310838247164154187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101620396873892164776102791 152430595310838247164154187)
      ·
        refine ⟨228645892966257370746231281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152430595310838247164154187 228645892966257370746231281)
        ·
          refine ⟨171484419724693028059673461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228645892966257370746231281 171484419724693028059673461)
          ·
            refine ⟨16076664349189971380594387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171484419724693028059673461 16076664349189971380594387)
            ·
              refine ⟨24114996523784957070891581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16076664349189971380594387 24114996523784957070891581)
              ·
                refine ⟨9043123696419358901584343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24114996523784957070891581 9043123696419358901584343)
                ·
                  refine ⟨13564685544629038352376515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9043123696419358901584343 13564685544629038352376515)
                  ·
                    refine ⟨20347028316943557528564773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13564685544629038352376515 20347028316943557528564773)
                    ·
                      refine ⟨3815067809426917036605895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20347028316943557528564773 3815067809426917036605895)
                      ·
                        rfl

theorem cell23_7429818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_7429818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429818 prefixEnd_7429818 := by exact prefixLift 7429818
  have htrace : WordTrace (prefixWord ++ tailWord_7429818) baseStart_7429818 baseEnd_7429818 := by
    simpa [prefixWord, tailWord_7429818, baseEnd_7429818] using wordTrace_append hprefix tailTrace_7429818
  have hstable : (prefixWord ++ tailWord_7429818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429818).length < 2 ^ (prefixWord ++ tailWord_7429818).sum := by decide
  have hdescent : baseEnd_7429818 < baseStart_7429818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429821 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_7429821 : Nat := 118140960795 + 7429821 * 2 ^ 59
def prefixEnd_7429821 : Nat := 4983230072969 + 3 ^ 40 * 7429821 * 2
def baseEnd_7429821 : Nat := 3815069349868880524868381

theorem tailTrace_7429821 : CollatzResearch.WordTrace tailWord_7429821 prefixEnd_7429821 3815069349868880524868381 := by
  unfold tailWord_7429821
  simp only [CollatzResearch.WordTrace]
  refine ⟨270987834416034904248633317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180658556277356602832422211 270987834416034904248633317)
  ·
    refine ⟨50810218953006544546618747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270987834416034904248633317 50810218953006544546618747)
    ·
      refine ⟨76215328429509816819928121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50810218953006544546618747 76215328429509816819928121)
      ·
        refine ⟨57161496322132362614946091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76215328429509816819928121 57161496322132362614946091)
        ·
          refine ⟨85742244483198543922419137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57161496322132362614946091 85742244483198543922419137)
          ·
            refine ⟨64306683362398907941814353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85742244483198543922419137 64306683362398907941814353)
            ·
              refine ⟨48230012521799180956360765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64306683362398907941814353 48230012521799180956360765)
              ·
                refine ⟨18086254695674692858635287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48230012521799180956360765 18086254695674692858635287)
                ·
                  refine ⟨27129382043512039287952931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18086254695674692858635287 27129382043512039287952931)
                  ·
                    refine ⟨40694073065268058931929397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27129382043512039287952931 40694073065268058931929397)
                    ·
                      refine ⟨3815069349868880524868381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40694073065268058931929397 3815069349868880524868381)
                      ·
                        rfl

theorem cell23_7429821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_7429821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429821 prefixEnd_7429821 := by exact prefixLift 7429821
  have htrace : WordTrace (prefixWord ++ tailWord_7429821) baseStart_7429821 baseEnd_7429821 := by
    simpa [prefixWord, tailWord_7429821, baseEnd_7429821] using wordTrace_append hprefix tailTrace_7429821
  have hstable : (prefixWord ++ tailWord_7429821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429821).length < 2 ^ (prefixWord ++ tailWord_7429821).sum := by decide
  have hdescent : baseEnd_7429821 < baseStart_7429821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429824 : List Nat := [2, 1, 1, 2, 4, 1, 12]
def baseStart_7429824 : Nat := 118140960795 + 7429824 * 2 ^ 59
def prefixEnd_7429824 : Nat := 4983230072969 + 3 ^ 40 * 7429824 * 2
def baseEnd_7429824 : Nat := 47099640621121531026307

theorem tailTrace_7429824 : CollatzResearch.WordTrace tailWord_7429824 prefixEnd_7429824 47099640621121531026307 := by
  unfold tailWord_7429824
  simp only [CollatzResearch.WordTrace]
  refine ⟨135493971917512017880496263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180658629223349357173995017 135493971917512017880496263)
  ·
    refine ⟨203240957876268026820744395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135493971917512017880496263 203240957876268026820744395)
    ·
      refine ⟨304861436814402040231116593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203240957876268026820744395 304861436814402040231116593)
      ·
        refine ⟨228646077610801530173337445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304861436814402040231116593 228646077610801530173337445)
        ·
          refine ⟨42871139552025286907500771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228646077610801530173337445 42871139552025286907500771)
          ·
            refine ⟨64306709328037930361251157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42871139552025286907500771 64306709328037930361251157)
            ·
              refine ⟨47099640621121531026307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 64306709328037930361251157 47099640621121531026307)
              ·
                rfl

theorem cell23_7429824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 12].length) (baseStart_7429824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429824 prefixEnd_7429824 := by exact prefixLift 7429824
  have htrace : WordTrace (prefixWord ++ tailWord_7429824) baseStart_7429824 baseEnd_7429824 := by
    simpa [prefixWord, tailWord_7429824, baseEnd_7429824] using wordTrace_append hprefix tailTrace_7429824
  have hstable : (prefixWord ++ tailWord_7429824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429824).length < 2 ^ (prefixWord ++ tailWord_7429824).sum := by decide
  have hdescent : baseEnd_7429824 < baseStart_7429824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429828 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_7429828 : Nat := 118140960795 + 7429828 * 2 ^ 59
def prefixEnd_7429828 : Nat := 4983230072969 + 3 ^ 40 * 7429828 * 2
def baseEnd_7429828 : Nat := 1271690981411153999160283

theorem tailTrace_7429828 : CollatzResearch.WordTrace tailWord_7429828 prefixEnd_7429828 1271690981411153999160283 := by
  unfold tailWord_7429828
  simp only [CollatzResearch.WordTrace]
  refine ⟨135494044863504772222069069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180658726484673029629425425 135494044863504772222069069)
  ·
    refine ⟨50810266823814289583275901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135494044863504772222069069 50810266823814289583275901)
    ·
      refine ⟨19053850058930358593728463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50810266823814289583275901 19053850058930358593728463)
      ·
        refine ⟨28580775088395537890592695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19053850058930358593728463 28580775088395537890592695)
        ·
          refine ⟨42871162632593306835889043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28580775088395537890592695 42871162632593306835889043)
          ·
            refine ⟨64306743948889960253833565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42871162632593306835889043 64306743948889960253833565)
            ·
              refine ⟨24115028980833735095187587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64306743948889960253833565 24115028980833735095187587)
              ·
                refine ⟨36172543471250602642781381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24115028980833735095187587 36172543471250602642781381)
                ·
                  refine ⟨6782351900859487995521509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36172543471250602642781381 6782351900859487995521509)
                  ·
                    refine ⟨1271690981411153999160283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6782351900859487995521509 1271690981411153999160283)
                    ·
                      rfl

theorem cell23_7429828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_7429828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429828 prefixEnd_7429828 := by exact prefixLift 7429828
  have htrace : WordTrace (prefixWord ++ tailWord_7429828) baseStart_7429828 baseEnd_7429828 := by
    simpa [prefixWord, tailWord_7429828, baseEnd_7429828] using wordTrace_append hprefix tailTrace_7429828
  have hstable : (prefixWord ++ tailWord_7429828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429828).length < 2 ^ (prefixWord ++ tailWord_7429828).sum := by decide
  have hdescent : baseEnd_7429828 < baseStart_7429828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429852 : List Nat := [2, 2, 5, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_7429852 : Nat := 118140960795 + 7429852 * 2 ^ 59
def prefixEnd_7429852 : Nat := 4983230072969 + 3 ^ 40 * 7429852 * 2
def baseEnd_7429852 : Nat := 3815085267769169903580739

theorem tailTrace_7429852 : CollatzResearch.WordTrace tailWord_7429852 prefixEnd_7429852 3815085267769169903580739 := by
  unfold tailWord_7429852
  simp only [CollatzResearch.WordTrace]
  refine ⟨135494482539461298271505905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180659310052615064362007873 135494482539461298271505905)
  ·
    refine ⟨101620861904595973703629429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135494482539461298271505905 101620861904595973703629429)
    ·
      refine ⟨9526955803555872534715259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101620861904595973703629429 9526955803555872534715259)
      ·
        refine ⟨14290433705333808802072889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9526955803555872534715259 14290433705333808802072889)
        ·
          refine ⟨10717825279000356601554667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14290433705333808802072889 10717825279000356601554667)
          ·
            refine ⟨16076737918500534902332001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10717825279000356601554667 16076737918500534902332001)
            ·
              refine ⟨12057553438875401176749001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16076737918500534902332001 12057553438875401176749001)
              ·
                refine ⟨9043165079156550882561751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12057553438875401176749001 9043165079156550882561751)
                ·
                  refine ⟨13564747618734826323842627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9043165079156550882561751 13564747618734826323842627)
                  ·
                    refine ⟨20347121428102239485763941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13564747618734826323842627 20347121428102239485763941)
                    ·
                      refine ⟨3815085267769169903580739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20347121428102239485763941 3815085267769169903580739)
                      ·
                        rfl

theorem cell23_7429852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_7429852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429852 prefixEnd_7429852 := by exact prefixLift 7429852
  have htrace : WordTrace (prefixWord ++ tailWord_7429852) baseStart_7429852 baseEnd_7429852 := by
    simpa [prefixWord, tailWord_7429852, baseEnd_7429852] using wordTrace_append hprefix tailTrace_7429852
  have hstable : (prefixWord ++ tailWord_7429852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429852).length < 2 ^ (prefixWord ++ tailWord_7429852).sum := by decide
  have hdescent : baseEnd_7429852 < baseStart_7429852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429868 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 3]
def baseStart_7429868 : Nat := 118140960795 + 7429868 * 2 ^ 59
def prefixEnd_7429868 : Nat := 4983230072969 + 3 ^ 40 * 7429868 * 2
def baseEnd_7429868 : Nat := 3815093483459641840980665

theorem tailTrace_7429868 : CollatzResearch.WordTrace tailWord_7429868 prefixEnd_7429868 3815093483459641840980665 := by
  unfold tailWord_7429868
  simp only [CollatzResearch.WordTrace]
  refine ⟨135494774323432315637797129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180659699097909754183729505 135494774323432315637797129)
  ·
    refine ⟨101621080742574236728347847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135494774323432315637797129 101621080742574236728347847)
    ·
      refine ⟨152431621113861355092521771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101621080742574236728347847 152431621113861355092521771)
      ·
        refine ⟨228647431670792032638782657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152431621113861355092521771 228647431670792032638782657)
        ·
          refine ⟨171485573753094024479086993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228647431670792032638782657 171485573753094024479086993)
          ·
            refine ⟨128614180314820518359315245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171485573753094024479086993 128614180314820518359315245)
            ·
              refine ⟨48230317618057694384743217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128614180314820518359315245 48230317618057694384743217)
              ·
                refine ⟨36172738213543270788557413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48230317618057694384743217 36172738213543270788557413)
                ·
                  refine ⟨6782388415039363272854515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36172738213543270788557413 6782388415039363272854515)
                  ·
                    refine ⟨10173582622559044909281773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6782388415039363272854515 10173582622559044909281773)
                    ·
                      refine ⟨3815093483459641840980665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10173582622559044909281773 3815093483459641840980665)
                      ·
                        rfl

theorem cell23_7429868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_7429868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429868 prefixEnd_7429868 := by exact prefixLift 7429868
  have htrace : WordTrace (prefixWord ++ tailWord_7429868) baseStart_7429868 baseEnd_7429868 := by
    simpa [prefixWord, tailWord_7429868, baseEnd_7429868] using wordTrace_append hprefix tailTrace_7429868
  have hstable : (prefixWord ++ tailWord_7429868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429868).length < 2 ^ (prefixWord ++ tailWord_7429868).sum := by decide
  have hdescent : baseEnd_7429868 < baseStart_7429868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429869 : List Nat := [1, 5, 1, 2, 1, 2, 3, 3, 1, 2, 2]
def baseStart_7429869 : Nat := 118140960795 + 7429869 * 2 ^ 59
def prefixEnd_7429869 : Nat := 4983230072969 + 3 ^ 40 * 7429869 * 2
def baseEnd_7429869 : Nat := 3815093996940296337068161

theorem tailTrace_7429869 : CollatzResearch.WordTrace tailWord_7429869 prefixEnd_7429869 3815093996940296337068161 := by
  unfold tailWord_7429869
  simp only [CollatzResearch.WordTrace]
  refine ⟨270989585119861008446380661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180659723413240672297587107 270989585119861008446380661)
  ·
    refine ⟨25405273604986969541848187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 270989585119861008446380661 25405273604986969541848187)
    ·
      refine ⟨38107910407480454312772281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25405273604986969541848187 38107910407480454312772281)
      ·
        refine ⟨28580932805610340734579211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38107910407480454312772281 28580932805610340734579211)
        ·
          refine ⟨42871399208415511101868817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28580932805610340734579211 42871399208415511101868817)
          ·
            refine ⟨32153549406311633326401613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42871399208415511101868817 32153549406311633326401613)
            ·
              refine ⟨12057581027366862497400605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32153549406311633326401613 12057581027366862497400605)
              ·
                refine ⟨4521592885262573436525227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12057581027366862497400605 4521592885262573436525227)
                ·
                  refine ⟨6782389327893860154787841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521592885262573436525227 6782389327893860154787841)
                  ·
                    refine ⟨5086791995920395116090881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6782389327893860154787841 5086791995920395116090881)
                    ·
                      refine ⟨3815093996940296337068161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5086791995920395116090881 3815093996940296337068161)
                      ·
                        rfl

theorem cell23_7429869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_7429869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429869 prefixEnd_7429869 := by exact prefixLift 7429869
  have htrace : WordTrace (prefixWord ++ tailWord_7429869) baseStart_7429869 baseEnd_7429869 := by
    simpa [prefixWord, tailWord_7429869, baseEnd_7429869] using wordTrace_append hprefix tailTrace_7429869
  have hstable : (prefixWord ++ tailWord_7429869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429869).length < 2 ^ (prefixWord ++ tailWord_7429869).sum := by decide
  have hdescent : baseEnd_7429869 < baseStart_7429869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429886 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_7429886 : Nat := 118140960795 + 7429886 * 2 ^ 59
def prefixEnd_7429886 : Nat := 4983230072969 + 3 ^ 40 * 7429886 * 2
def baseEnd_7429886 : Nat := 3815102726111422770555583

theorem tailTrace_7429886 : CollatzResearch.WordTrace tailWord_7429886 prefixEnd_7429886 3815102726111422770555583 := by
  unfold tailWord_7429886
  simp only [CollatzResearch.WordTrace]
  refine ⟨33873775645099927543718689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180660136773866280233166341 33873775645099927543718689)
  ·
    refine ⟨25405331733824945657789017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33873775645099927543718689 25405331733824945657789017)
    ·
      refine ⟨19053998800368709243341763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25405331733824945657789017 19053998800368709243341763)
      ·
        refine ⟨28580998200553063865012645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19053998800368709243341763 28580998200553063865012645)
        ·
          refine ⟨5358937162603699474689871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28580998200553063865012645 5358937162603699474689871)
          ·
            refine ⟨8038405743905549212034807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5358937162603699474689871 8038405743905549212034807)
            ·
              refine ⟨12057608615858323818052211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8038405743905549212034807 12057608615858323818052211)
              ·
                refine ⟨18086412923787485727078317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12057608615858323818052211 18086412923787485727078317)
                ·
                  refine ⟨6782404846420307147654369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18086412923787485727078317 6782404846420307147654369)
                  ·
                    refine ⟨5086803634815230360740777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6782404846420307147654369 5086803634815230360740777)
                    ·
                      refine ⟨3815102726111422770555583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5086803634815230360740777 3815102726111422770555583)
                      ·
                        rfl

theorem cell23_7429886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_7429886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429886 prefixEnd_7429886 := by exact prefixLift 7429886
  have htrace : WordTrace (prefixWord ++ tailWord_7429886) baseStart_7429886 baseEnd_7429886 := by
    simpa [prefixWord, tailWord_7429886, baseEnd_7429886] using wordTrace_append hprefix tailTrace_7429886
  have hstable : (prefixWord ++ tailWord_7429886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429886).length < 2 ^ (prefixWord ++ tailWord_7429886).sum := by decide
  have hdescent : baseEnd_7429886 < baseStart_7429886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429902 : List Nat := [4, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3]
def baseStart_7429902 : Nat := 118140960795 + 7429902 * 2 ^ 59
def prefixEnd_7429902 : Nat := 4983230072969 + 3 ^ 40 * 7429902 * 2
def baseEnd_7429902 : Nat := 3815110941801894707955509

theorem tailTrace_7429902 : CollatzResearch.WordTrace tailWord_7429902 prefixEnd_7429902 3815110941801894707955509 := by
  unfold tailWord_7429902
  simp only [CollatzResearch.WordTrace]
  refine ⟨33873848591092681885291495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180660525819160970054887973 33873848591092681885291495)
  ·
    refine ⟨50810772886639022827937243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33873848591092681885291495 50810772886639022827937243)
    ·
      refine ⟨76216159329958534241905865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50810772886639022827937243 76216159329958534241905865)
      ·
        refine ⟨57162119497468900681429399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76216159329958534241905865 57162119497468900681429399)
        ·
          refine ⟨85743179246203351022144099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57162119497468900681429399 85743179246203351022144099)
          ·
            refine ⟨128614768869305026533216149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85743179246203351022144099 128614768869305026533216149)
            ·
              refine ⟨6028817290748673118744507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128614768869305026533216149 6028817290748673118744507)
              ·
                refine ⟨9043225936123009678116761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6028817290748673118744507 9043225936123009678116761)
                ·
                  refine ⟨6782419452092257258587571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9043225936123009678116761 6782419452092257258587571)
                  ·
                    refine ⟨10173629178138385887881357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6782419452092257258587571 10173629178138385887881357)
                    ·
                      refine ⟨3815110941801894707955509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10173629178138385887881357 3815110941801894707955509)
                      ·
                        rfl

theorem cell23_7429902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_7429902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429902 prefixEnd_7429902 := by exact prefixLift 7429902
  have htrace : WordTrace (prefixWord ++ tailWord_7429902) baseStart_7429902 baseEnd_7429902 := by
    simpa [prefixWord, tailWord_7429902, baseEnd_7429902] using wordTrace_append hprefix tailTrace_7429902
  have hstable : (prefixWord ++ tailWord_7429902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429902).length < 2 ^ (prefixWord ++ tailWord_7429902).sum := by decide
  have hdescent : baseEnd_7429902 < baseStart_7429902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429925 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 1, 4, 2]
def baseStart_7429925 : Nat := 118140960795 + 7429925 * 2 ^ 59
def prefixEnd_7429925 : Nat := 4983230072969 + 3 ^ 40 * 7429925 * 2
def baseEnd_7429925 : Nat := 3815122751856948117967903

theorem tailTrace_7429925 : CollatzResearch.WordTrace tailWord_7429925 prefixEnd_7429925 3815122751856948117967903 := by
  unfold tailWord_7429925
  simp only [CollatzResearch.WordTrace]
  refine ⟨270991627607658130010419229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180661085071772086673612819 270991627607658130010419229)
  ·
    refine ⟨101621860352871798753907211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270991627607658130010419229 101621860352871798753907211)
    ·
      refine ⟨152432790529307698130860817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101621860352871798753907211 152432790529307698130860817)
      ·
        refine ⟨114324592896980773598145613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152432790529307698130860817 114324592896980773598145613)
        ·
          refine ⟨42871722336367790099304605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114324592896980773598145613 42871722336367790099304605)
          ·
            refine ⟨16076895876137921287239227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42871722336367790099304605 16076895876137921287239227)
            ·
              refine ⟨24115343814206881930858841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16076895876137921287239227 24115343814206881930858841)
              ·
                refine ⟨18086507860655161448144131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24115343814206881930858841 18086507860655161448144131)
                ·
                  refine ⟨27129761790982742172216197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18086507860655161448144131 27129761790982742172216197)
                  ·
                    refine ⟨5086830335809264157290537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27129761790982742172216197 5086830335809264157290537)
                    ·
                      refine ⟨3815122751856948117967903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5086830335809264157290537 3815122751856948117967903)
                      ·
                        rfl

theorem cell23_7429925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_7429925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429925 prefixEnd_7429925 := by exact prefixLift 7429925
  have htrace : WordTrace (prefixWord ++ tailWord_7429925) baseStart_7429925 baseEnd_7429925 := by
    simpa [prefixWord, tailWord_7429925, baseEnd_7429925] using wordTrace_append hprefix tailTrace_7429925
  have hstable : (prefixWord ++ tailWord_7429925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429925).length < 2 ^ (prefixWord ++ tailWord_7429925).sum := by decide
  have hdescent : baseEnd_7429925 < baseStart_7429925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429928 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_7429928 : Nat := 118140960795 + 7429928 * 2 ^ 59
def prefixEnd_7429928 : Nat := 4983230072969 + 3 ^ 40 * 7429928 * 2
def baseEnd_7429928 : Nat := 3815124292298911606230389

theorem tailTrace_7429928 : CollatzResearch.WordTrace tailWord_7429928 prefixEnd_7429928 3815124292298911606230389 := by
  unfold tailWord_7429928
  simp only [CollatzResearch.WordTrace]
  refine ⟨135495868513323630761389219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180661158017764841015185625 135495868513323630761389219)
  ·
    refine ⟨203243802769985446142083829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135495868513323630761389219 203243802769985446142083829)
    ·
      refine ⟨19054106509686135575820359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203243802769985446142083829 19054106509686135575820359)
      ·
        refine ⟨28581159764529203363730539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19054106509686135575820359 28581159764529203363730539)
        ·
          refine ⟨42871739646793805045595809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28581159764529203363730539 42871739646793805045595809)
          ·
            refine ⟨32153804735095353784196857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42871739646793805045595809 32153804735095353784196857)
            ·
              refine ⟨24115353551321515338147643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32153804735095353784196857 24115353551321515338147643)
              ·
                refine ⟨36173030326982273007221465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24115353551321515338147643 36173030326982273007221465)
                ·
                  refine ⟨27129772745236704755416099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36173030326982273007221465 27129772745236704755416099)
                  ·
                    refine ⟨40694659117855057133124149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27129772745236704755416099 40694659117855057133124149)
                    ·
                      refine ⟨3815124292298911606230389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40694659117855057133124149 3815124292298911606230389)
                      ·
                        rfl

theorem cell23_7429928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_7429928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429928 prefixEnd_7429928 := by exact prefixLift 7429928
  have htrace : WordTrace (prefixWord ++ tailWord_7429928) baseStart_7429928 baseEnd_7429928 := by
    simpa [prefixWord, tailWord_7429928, baseEnd_7429928] using wordTrace_append hprefix tailTrace_7429928
  have hstable : (prefixWord ++ tailWord_7429928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429928).length < 2 ^ (prefixWord ++ tailWord_7429928).sum := by decide
  have hdescent : baseEnd_7429928 < baseStart_7429928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429961 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 1, 7]
def baseStart_7429961 : Nat := 118140960795 + 7429961 * 2 ^ 59
def prefixEnd_7429961 : Nat := 4983230072969 + 3 ^ 40 * 7429961 * 2
def baseEnd_7429961 : Nat := 1271713745720169992372579

theorem tailTrace_7429961 : CollatzResearch.WordTrace tailWord_7429961 prefixEnd_7429961 1271713745720169992372579 := by
  unfold tailWord_7429961
  simp only [CollatzResearch.WordTrace]
  refine ⟨270992940635527708158729737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180661960423685138772486491 270992940635527708158729737)
  ·
    refine ⟨203244705476645781119047303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270992940635527708158729737 203244705476645781119047303)
    ·
      refine ⟨304867058214968671678570955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203244705476645781119047303 304867058214968671678570955)
      ·
        refine ⟨457300587322453007517856433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304867058214968671678570955 457300587322453007517856433)
        ·
          refine ⟨342975440491839755638392325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457300587322453007517856433 342975440491839755638392325)
          ·
            refine ⟨64307895092219954182198561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342975440491839755638392325 64307895092219954182198561)
            ·
              refine ⟨48230921319164965636648921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64307895092219954182198561 48230921319164965636648921)
              ·
                refine ⟨36173190989373724227486691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48230921319164965636648921 36173190989373724227486691)
                ·
                  refine ⟨54259786484060586341230037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36173190989373724227486691 54259786484060586341230037)
                  ·
                    refine ⟨1271713745720169992372579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54259786484060586341230037 1271713745720169992372579)
                    ·
                      rfl

theorem cell23_7429961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 7].length) (baseStart_7429961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429961 prefixEnd_7429961 := by exact prefixLift 7429961
  have htrace : WordTrace (prefixWord ++ tailWord_7429961) baseStart_7429961 baseEnd_7429961 := by
    simpa [prefixWord, tailWord_7429961, baseEnd_7429961] using wordTrace_append hprefix tailTrace_7429961
  have hstable : (prefixWord ++ tailWord_7429961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429961).length < 2 ^ (prefixWord ++ tailWord_7429961).sum := by decide
  have hdescent : baseEnd_7429961 < baseStart_7429961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429965 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 7]
def baseStart_7429965 : Nat := 118140960795 + 7429965 * 2 ^ 59
def prefixEnd_7429965 : Nat := 4983230072969 + 3 ^ 40 * 7429965 * 2
def baseEnd_7429965 : Nat := 423904810120347551274191

theorem tailTrace_7429965 : CollatzResearch.WordTrace tailWord_7429965 prefixEnd_7429965 423904810120347551274191 := by
  unfold tailWord_7429965
  simp only [CollatzResearch.WordTrace]
  refine ⟨270993086527513216841875349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180662057685008811227916899 270993086527513216841875349)
  ·
    refine ⟨12702800930977182039462907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 270993086527513216841875349 12702800930977182039462907)
    ·
      refine ⟨19054201396465773059194361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12702800930977182039462907 19054201396465773059194361)
      ·
        refine ⟨14290651047349329794395771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19054201396465773059194361 14290651047349329794395771)
        ·
          refine ⟨21435976571023994691593657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14290651047349329794395771 21435976571023994691593657)
          ·
            refine ⟨16076982428267996018695243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21435976571023994691593657 16076982428267996018695243)
            ·
              refine ⟨24115473642401994028042865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16076982428267996018695243 24115473642401994028042865)
              ·
                refine ⟨18086605231801495521032149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24115473642401994028042865 18086605231801495521032149)
                ·
                  refine ⟨423904810120347551274191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18086605231801495521032149 423904810120347551274191)
                  ·
                    rfl

theorem cell23_7429965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_7429965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429965 prefixEnd_7429965 := by exact prefixLift 7429965
  have htrace : WordTrace (prefixWord ++ tailWord_7429965) baseStart_7429965 baseEnd_7429965 := by
    simpa [prefixWord, tailWord_7429965, baseEnd_7429965] using wordTrace_append hprefix tailTrace_7429965
  have hstable : (prefixWord ++ tailWord_7429965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429965).length < 2 ^ (prefixWord ++ tailWord_7429965).sum := by decide
  have hdescent : baseEnd_7429965 < baseStart_7429965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7429968 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 4, 5, 2]
def baseStart_7429968 : Nat := 118140960795 + 7429968 * 2 ^ 59
def prefixEnd_7429968 : Nat := 4983230072969 + 3 ^ 40 * 7429968 * 2
def baseEnd_7429968 : Nat := 3815144831525091449730205

theorem tailTrace_7429968 : CollatzResearch.WordTrace tailWord_7429968 prefixEnd_7429968 3815144831525091449730205 := by
  unfold tailWord_7429968
  simp only [CollatzResearch.WordTrace]
  refine ⟨135496597973251174177117279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180662130631001565569489705 135496597973251174177117279)
  ·
    refine ⟨203244896959876761265675919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135496597973251174177117279 203244896959876761265675919)
    ·
      refine ⟨304867345439815141898513879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203244896959876761265675919 304867345439815141898513879)
      ·
        refine ⟨457301018159722712847770819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304867345439815141898513879 457301018159722712847770819)
        ·
          refine ⟨685951527239584069271656229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457301018159722712847770819 685951527239584069271656229)
          ·
            refine ⟨128615911357422012988435543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 685951527239584069271656229 128615911357422012988435543)
            ·
              refine ⟨192923867036133019482653315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128615911357422012988435543 192923867036133019482653315)
              ·
                refine ⟨289385800554199529223979973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192923867036133019482653315 289385800554199529223979973)
                ·
                  refine ⟨54259837603912411729496245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289385800554199529223979973 54259837603912411729496245)
                  ·
                    refine ⟨5086859775366788599640273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54259837603912411729496245 5086859775366788599640273)
                    ·
                      refine ⟨3815144831525091449730205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5086859775366788599640273 3815144831525091449730205)
                      ·
                        rfl

theorem cell23_7429968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 5, 2].length) (baseStart_7429968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7429968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7429968 prefixEnd_7429968 := by exact prefixLift 7429968
  have htrace : WordTrace (prefixWord ++ tailWord_7429968) baseStart_7429968 baseEnd_7429968 := by
    simpa [prefixWord, tailWord_7429968, baseEnd_7429968] using wordTrace_append hprefix tailTrace_7429968
  have hstable : (prefixWord ++ tailWord_7429968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7429968).length < 2 ^ (prefixWord ++ tailWord_7429968).sum := by decide
  have hdescent : baseEnd_7429968 < baseStart_7429968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7429968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430011 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 6]
def baseStart_7430011 : Nat := 118140960795 + 7430011 * 2 ^ 59
def prefixEnd_7430011 : Nat := 4983230072969 + 3 ^ 40 * 7430011 * 2
def baseEnd_7430011 : Nat := 3815166911193234781492507

theorem tailTrace_7430011 : CollatzResearch.WordTrace tailWord_7430011 prefixEnd_7430011 3815166911193234781492507 := by
  unfold tailWord_7430011
  simp only [CollatzResearch.WordTrace]
  refine ⟨270994764285346566698049887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180663176190231044465366591 270994764285346566698049887)
  ·
    refine ⟨406492146428019850047074831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270994764285346566698049887 406492146428019850047074831)
    ·
      refine ⟨609738219642029775070612247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406492146428019850047074831 609738219642029775070612247)
      ·
        refine ⟨914607329463044662605918371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609738219642029775070612247 914607329463044662605918371)
        ·
          refine ⟨1371910994194566993908877557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914607329463044662605918371 1371910994194566993908877557)
          ·
            refine ⟨128616655705740655678957271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1371910994194566993908877557 128616655705740655678957271)
            ·
              refine ⟨192924983558610983518435907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128616655705740655678957271 192924983558610983518435907)
              ·
                refine ⟨289387475337916475277653861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192924983558610983518435907 289387475337916475277653861)
                ·
                  refine ⟨54260151625859339114560099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289387475337916475277653861 54260151625859339114560099)
                  ·
                    refine ⟨81390227438789008671840149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54260151625859339114560099 81390227438789008671840149)
                    ·
                      refine ⟨3815166911193234781492507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81390227438789008671840149 3815166911193234781492507)
                      ·
                        rfl

theorem cell23_7430011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 6].length) (baseStart_7430011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430011 prefixEnd_7430011 := by exact prefixLift 7430011
  have htrace : WordTrace (prefixWord ++ tailWord_7430011) baseStart_7430011 baseEnd_7430011 := by
    simpa [prefixWord, tailWord_7430011, baseEnd_7430011] using wordTrace_append hprefix tailTrace_7430011
  have hstable : (prefixWord ++ tailWord_7430011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430011).length < 2 ^ (prefixWord ++ tailWord_7430011).sum := by decide
  have hdescent : baseEnd_7430011 < baseStart_7430011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430092 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 2, 3, 2]
def baseStart_7430092 : Nat := 118140960795 + 7430092 * 2 ^ 59
def prefixEnd_7430092 : Nat := 4983230072969 + 3 ^ 40 * 7430092 * 2
def baseEnd_7430092 : Nat := 3815208503126248964579635

theorem tailTrace_7430092 : CollatzResearch.WordTrace tailWord_7430092 prefixEnd_7430092 3815208503126248964579635 := by
  unfold tailWord_7430092
  simp only [CollatzResearch.WordTrace]
  refine ⟨135498859299026558765874265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180665145732035411687832353 135498859299026558765874265)
  ·
    refine ⟨101624144474269919074405699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135498859299026558765874265 101624144474269919074405699)
    ·
      refine ⟨152436216711404878611608549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101624144474269919074405699 152436216711404878611608549)
      ·
        refine ⟨28581790633388414739676603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152436216711404878611608549 28581790633388414739676603)
        ·
          refine ⟨42872685950082622109514905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28581790633388414739676603 42872685950082622109514905)
          ·
            refine ⟨32154514462561966582136179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42872685950082622109514905 32154514462561966582136179)
            ·
              refine ⟨48231771693842949873204269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32154514462561966582136179 48231771693842949873204269)
              ·
                refine ⟨18086914385191106202451601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48231771693842949873204269 18086914385191106202451601)
                ·
                  refine ⟨13565185788893329651838701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18086914385191106202451601 13565185788893329651838701)
                  ·
                    refine ⟨5086944670834998619439513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13565185788893329651838701 5086944670834998619439513)
                    ·
                      refine ⟨3815208503126248964579635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5086944670834998619439513 3815208503126248964579635)
                      ·
                        rfl

theorem cell23_7430092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_7430092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430092 prefixEnd_7430092 := by exact prefixLift 7430092
  have htrace : WordTrace (prefixWord ++ tailWord_7430092) baseStart_7430092 baseEnd_7430092 := by
    simpa [prefixWord, tailWord_7430092, baseEnd_7430092] using wordTrace_append hprefix tailTrace_7430092
  have hstable : (prefixWord ++ tailWord_7430092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430092).length < 2 ^ (prefixWord ++ tailWord_7430092).sum := by decide
  have hdescent : baseEnd_7430092 < baseStart_7430092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430128 : List Nat := [2, 1, 1, 1, 3, 2, 5, 8]
def baseStart_7430128 : Nat := 118140960795 + 7430128 * 2 ^ 59
def prefixEnd_7430128 : Nat := 4983230072969 + 3 ^ 40 * 7430128 * 2
def baseEnd_7430128 : Nat := 141304703275178178656647

theorem tailTrace_7430128 : CollatzResearch.WordTrace tailWord_7430128 prefixEnd_7430128 141304703275178178656647 := by
  unfold tailWord_7430128
  simp only [CollatzResearch.WordTrace]
  refine ⟨135499515812961347840029519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180666021083948463786706025 135499515812961347840029519)
  ·
    refine ⟨203249273719442021760044279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135499515812961347840029519 203249273719442021760044279)
    ·
      refine ⟨304873910579163032640066419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203249273719442021760044279 304873910579163032640066419)
      ·
        refine ⟨457310865868744548960099629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304873910579163032640066419 457310865868744548960099629)
        ·
          refine ⟨171491574700779205860037361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457310865868744548960099629 171491574700779205860037361)
          ·
            refine ⟨128618681025584404395028021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171491574700779205860037361 128618681025584404395028021)
            ·
              refine ⟨12058001346148537912033877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128618681025584404395028021 12058001346148537912033877)
              ·
                refine ⟨141304703275178178656647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12058001346148537912033877 141304703275178178656647)
                ·
                  rfl

theorem cell23_7430128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 8].length) (baseStart_7430128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430128 prefixEnd_7430128 := by exact prefixLift 7430128
  have htrace : WordTrace (prefixWord ++ tailWord_7430128) baseStart_7430128 baseEnd_7430128 := by
    simpa [prefixWord, tailWord_7430128, baseEnd_7430128] using wordTrace_append hprefix tailTrace_7430128
  have hstable : (prefixWord ++ tailWord_7430128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430128).length < 2 ^ (prefixWord ++ tailWord_7430128).sum := by decide
  have hdescent : baseEnd_7430128 < baseStart_7430128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430145 : List Nat := [1, 2, 4, 1, 2, 1, 5, 7]
def baseStart_7430145 : Nat := 118140960795 + 7430145 * 2 ^ 59
def prefixEnd_7430145 : Nat := 4983230072969 + 3 ^ 40 * 7430145 * 2
def baseEnd_7430145 : Nat := 141305026577812491008033

theorem tailTrace_7430145 : CollatzResearch.WordTrace tailWord_7430145 prefixEnd_7430145 141305026577812491008033 := by
  unfold tailWord_7430145
  simp only [CollatzResearch.WordTrace]
  refine ⟨270999651666861107583427889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180666434444574071722285259 270999651666861107583427889)
  ·
    refine ⟨203249738750145830687570917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270999651666861107583427889 203249738750145830687570917)
    ·
      refine ⟨38109326015652343253919547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203249738750145830687570917 38109326015652343253919547)
      ·
        refine ⟨57163989023478514880879321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38109326015652343253919547 57163989023478514880879321)
        ·
          refine ⟨42872991767608886160659491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57163989023478514880879321 42872991767608886160659491)
          ·
            refine ⟨64309487651413329240989237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42872991767608886160659491 64309487651413329240989237)
            ·
              refine ⟨6029014467319999616342741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64309487651413329240989237 6029014467319999616342741)
              ·
                refine ⟨141305026577812491008033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6029014467319999616342741 141305026577812491008033)
                ·
                  rfl

theorem cell23_7430145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 7].length) (baseStart_7430145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430145 prefixEnd_7430145 := by exact prefixLift 7430145
  have htrace : WordTrace (prefixWord ++ tailWord_7430145) baseStart_7430145 baseEnd_7430145 := by
    simpa [prefixWord, tailWord_7430145, baseEnd_7430145] using wordTrace_append hprefix tailTrace_7430145
  have hstable : (prefixWord ++ tailWord_7430145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430145).length < 2 ^ (prefixWord ++ tailWord_7430145).sum := by decide
  have hdescent : baseEnd_7430145 < baseStart_7430145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430155 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 3]
def baseStart_7430155 : Nat := 118140960795 + 7430155 * 2 ^ 59
def prefixEnd_7430155 : Nat := 4983230072969 + 3 ^ 40 * 7430155 * 2
def baseEnd_7430155 : Nat := 3815240852407482218091845

theorem tailTrace_7430155 : CollatzResearch.WordTrace tailWord_7430155 prefixEnd_7430155 3815240852407482218091845 := by
  unfold tailWord_7430155
  simp only [CollatzResearch.WordTrace]
  refine ⟨271000016396824879291291919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180666677597883252860861279 271000016396824879291291919)
  ·
    refine ⟨406500024595237318936937879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271000016396824879291291919 406500024595237318936937879)
    ·
      refine ⟨609750036892855978405406819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406500024595237318936937879 609750036892855978405406819)
      ·
        refine ⟨914625055339283967608110229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609750036892855978405406819 914625055339283967608110229)
        ·
          refine ⟨42873049469028935981630167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 914625055339283967608110229 42873049469028935981630167)
          ·
            refine ⟨64309574203543403972445251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42873049469028935981630167 64309574203543403972445251)
            ·
              refine ⟨96464361305315105958667877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64309574203543403972445251 96464361305315105958667877)
              ·
                refine ⟨18087067744746582367250227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96464361305315105958667877 18087067744746582367250227)
                ·
                  refine ⟨27130601617119873550875341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18087067744746582367250227 27130601617119873550875341)
                  ·
                    refine ⟨10173975606419952581578253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27130601617119873550875341 10173975606419952581578253)
                    ·
                      refine ⟨3815240852407482218091845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10173975606419952581578253 3815240852407482218091845)
                      ·
                        rfl

theorem cell23_7430155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 3].length) (baseStart_7430155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430155 prefixEnd_7430155 := by exact prefixLift 7430155
  have htrace : WordTrace (prefixWord ++ tailWord_7430155) baseStart_7430155 baseEnd_7430155 := by
    simpa [prefixWord, tailWord_7430155, baseEnd_7430155] using wordTrace_append hprefix tailTrace_7430155
  have hstable : (prefixWord ++ tailWord_7430155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430155).length < 2 ^ (prefixWord ++ tailWord_7430155).sum := by decide
  have hdescent : baseEnd_7430155 < baseStart_7430155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430156 : List Nat := [2, 2, 1, 2, 3, 1, 4, 3, 1, 2, 2]
def baseStart_7430156 : Nat := 118140960795 + 7430156 * 2 ^ 59
def prefixEnd_7430156 : Nat := 4983230072969 + 3 ^ 40 * 7430156 * 2
def baseEnd_7430156 : Nat := 3815241365888136714179341

theorem tailTrace_7430156 : CollatzResearch.WordTrace tailWord_7430156 prefixEnd_7430156 3815241365888136714179341 := by
  unfold tailWord_7430156
  simp only [CollatzResearch.WordTrace]
  refine ⟨135500026434910628231039161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180666701913214170974718881 135500026434910628231039161)
  ·
    refine ⟨101625019826182971173279371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135500026434910628231039161 101625019826182971173279371)
    ·
      refine ⟨152437529739274456759919057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101625019826182971173279371 152437529739274456759919057)
      ·
        refine ⟨114328147304455842569939293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152437529739274456759919057 114328147304455842569939293)
        ·
          refine ⟨42873055239170940963727235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114328147304455842569939293 42873055239170940963727235)
          ·
            refine ⟨64309582858756411445590853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42873055239170940963727235 64309582858756411445590853)
            ·
              refine ⟨12058046786016827146048285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64309582858756411445590853 12058046786016827146048285)
              ·
                refine ⟨4521767544756310179768107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12058046786016827146048285 4521767544756310179768107)
                ·
                  refine ⟨6782651317134465269652161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521767544756310179768107 6782651317134465269652161)
                  ·
                    refine ⟨5086988487850848952239121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6782651317134465269652161 5086988487850848952239121)
                    ·
                      refine ⟨3815241365888136714179341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5086988487850848952239121 3815241365888136714179341)
                      ·
                        rfl

theorem cell23_7430156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_7430156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430156 prefixEnd_7430156 := by exact prefixLift 7430156
  have htrace : WordTrace (prefixWord ++ tailWord_7430156) baseStart_7430156 baseEnd_7430156 := by
    simpa [prefixWord, tailWord_7430156, baseEnd_7430156] using wordTrace_append hprefix tailTrace_7430156
  have hstable : (prefixWord ++ tailWord_7430156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430156).length < 2 ^ (prefixWord ++ tailWord_7430156).sum := by decide
  have hdescent : baseEnd_7430156 < baseStart_7430156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430188 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 1, 8]
def baseStart_7430188 : Nat := 118140960795 + 7430188 * 2 ^ 59
def prefixEnd_7430188 : Nat := 4983230072969 + 3 ^ 40 * 7430188 * 2
def baseEnd_7430188 : Nat := 1271752599089693529659731

theorem tailTrace_7430188 : CollatzResearch.WordTrace tailWord_7430188 prefixEnd_7430188 1271752599089693529659731 := by
  unfold tailWord_7430188
  simp only [CollatzResearch.WordTrace]
  refine ⟨135500610002852662963621609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180667480003803550618162145 135500610002852662963621609)
  ·
    refine ⟨101625457502139497222716207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135500610002852662963621609 101625457502139497222716207)
    ·
      refine ⟨152438186253209245834074311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101625457502139497222716207 152438186253209245834074311)
      ·
        refine ⟨228657279379813868751111467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152438186253209245834074311 228657279379813868751111467)
        ·
          refine ⟨342985919069720803126667201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228657279379813868751111467 342985919069720803126667201)
          ·
            refine ⟨257239439302290602345000401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342985919069720803126667201 257239439302290602345000401)
            ·
              refine ⟨192929579476717951758750301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257239439302290602345000401 192929579476717951758750301)
              ·
                refine ⟨72348592303769231909531363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192929579476717951758750301 72348592303769231909531363)
                ·
                  refine ⟨108522888455653847864297045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72348592303769231909531363 108522888455653847864297045)
                  ·
                    refine ⟨1271752599089693529659731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108522888455653847864297045 1271752599089693529659731)
                    ·
                      rfl

theorem cell23_7430188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_7430188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430188 prefixEnd_7430188 := by exact prefixLift 7430188
  have htrace : WordTrace (prefixWord ++ tailWord_7430188) baseStart_7430188 baseEnd_7430188 := by
    simpa [prefixWord, tailWord_7430188, baseEnd_7430188] using wordTrace_append hprefix tailTrace_7430188
  have hstable : (prefixWord ++ tailWord_7430188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430188).length < 2 ^ (prefixWord ++ tailWord_7430188).sum := by decide
  have hdescent : baseEnd_7430188 < baseStart_7430188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430196 : List Nat := [2, 5, 1, 2, 3, 1, 2, 7]
def baseStart_7430196 : Nat := 118140960795 + 7430196 * 2 ^ 59
def prefixEnd_7430196 : Nat := 4983230072969 + 3 ^ 40 * 7430196 * 2
def baseEnd_7430196 : Nat := 141305996485715428062191

theorem tailTrace_7430196 : CollatzResearch.WordTrace tailWord_7430196 prefixEnd_7430196 141305996485715428062191 := by
  unfold tailWord_7430196
  simp only [CollatzResearch.WordTrace]
  refine ⟨135500755894838171646767221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180667674526450895529022961 135500755894838171646767221)
  ·
    refine ⟨12703195865141078591884427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135500755894838171646767221 12703195865141078591884427)
    ·
      refine ⟨19054793797711617887826641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12703195865141078591884427 19054793797711617887826641)
      ·
        refine ⟨14291095348283713415869981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19054793797711617887826641 14291095348283713415869981)
        ·
          refine ⟨5359160755606392530951243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14291095348283713415869981 5359160755606392530951243)
          ·
            refine ⟨8038741133409588796426865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5359160755606392530951243 8038741133409588796426865)
            ·
              refine ⟨6029055850057191597320149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8038741133409588796426865 6029055850057191597320149)
              ·
                refine ⟨141305996485715428062191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6029055850057191597320149 141305996485715428062191)
                ·
                  rfl

theorem cell23_7430196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 7].length) (baseStart_7430196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430196 prefixEnd_7430196 := by exact prefixLift 7430196
  have htrace : WordTrace (prefixWord ++ tailWord_7430196) baseStart_7430196 baseEnd_7430196 := by
    simpa [prefixWord, tailWord_7430196, baseEnd_7430196] using wordTrace_append hprefix tailTrace_7430196
  have hstable : (prefixWord ++ tailWord_7430196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430196).length < 2 ^ (prefixWord ++ tailWord_7430196).sum := by decide
  have hdescent : baseEnd_7430196 < baseStart_7430196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430215 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_7430215 : Nat := 118140960795 + 7430215 * 2 ^ 59
def prefixEnd_7430215 : Nat := 4983230072969 + 3 ^ 40 * 7430215 * 2
def baseEnd_7430215 : Nat := 3815271661246751983341569

theorem tailTrace_7430215 : CollatzResearch.WordTrace tailWord_7430215 prefixEnd_7430215 3815271661246751983341569 := by
  unfold tailWord_7430215
  simp only [CollatzResearch.WordTrace]
  refine ⟨271002204776607509538476099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180668136517738339692317399 271002204776607509538476099)
  ·
    refine ⟨406503307164911264307714149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271002204776607509538476099 406503307164911264307714149)
    ·
      refine ⟨76219370093420862057696403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 406503307164911264307714149 76219370093420862057696403)
      ·
        refine ⟨114329055140131293086544605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76219370093420862057696403 114329055140131293086544605)
        ·
          refine ⟨42873395677549234907454227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114329055140131293086544605 42873395677549234907454227)
          ·
            refine ⟨64310093516323852361181341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42873395677549234907454227 64310093516323852361181341)
            ·
              refine ⟨24116285068621444635443003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64310093516323852361181341 24116285068621444635443003)
              ·
                refine ⟨36174427602932166953164505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24116285068621444635443003 36174427602932166953164505)
                ·
                  refine ⟨27130820702199125214873379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36174427602932166953164505 27130820702199125214873379)
                  ·
                    refine ⟨40696231053298687822310069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27130820702199125214873379 40696231053298687822310069)
                    ·
                      refine ⟨3815271661246751983341569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40696231053298687822310069 3815271661246751983341569)
                      ·
                        rfl

theorem cell23_7430215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_7430215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430215 prefixEnd_7430215 := by exact prefixLift 7430215
  have htrace : WordTrace (prefixWord ++ tailWord_7430215) baseStart_7430215 baseEnd_7430215 := by
    simpa [prefixWord, tailWord_7430215, baseEnd_7430215] using wordTrace_append hprefix tailTrace_7430215
  have hstable : (prefixWord ++ tailWord_7430215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430215).length < 2 ^ (prefixWord ++ tailWord_7430215).sum := by decide
  have hdescent : baseEnd_7430215 < baseStart_7430215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430229 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 4, 2, 2]
def baseStart_7430229 : Nat := 118140960795 + 7430229 * 2 ^ 59
def prefixEnd_7430229 : Nat := 4983230072969 + 3 ^ 40 * 7430229 * 2
def baseEnd_7430229 : Nat := 3815278849975914928566505

theorem tailTrace_7430229 : CollatzResearch.WordTrace tailWord_7430229 prefixEnd_7430229 3815278849975914928566505 := by
  unfold tailWord_7430229
  simp only [CollatzResearch.WordTrace]
  refine ⟨271002715398556789929485741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180668476932371193286323827 271002715398556789929485741)
  ·
    refine ⟨101626018274458796223557153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271002715398556789929485741 101626018274458796223557153)
    ·
      refine ⟨76219513705844097167667865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101626018274458796223557153 76219513705844097167667865)
      ·
        refine ⟨57164635279383072875750899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76219513705844097167667865 57164635279383072875750899)
        ·
          refine ⟨85746952919074609313626349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57164635279383072875750899 85746952919074609313626349)
          ·
            refine ⟨32155107344652978492609881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85746952919074609313626349 32155107344652978492609881)
            ·
              refine ⟨24116330508489733869457411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32155107344652978492609881 24116330508489733869457411)
              ·
                refine ⟨36174495762734600804186117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24116330508489733869457411 36174495762734600804186117)
                ·
                  refine ⟨6782717955512737650784897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36174495762734600804186117 6782717955512737650784897)
                  ·
                    refine ⟨5087038466634553238088673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6782717955512737650784897 5087038466634553238088673)
                    ·
                      refine ⟨3815278849975914928566505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087038466634553238088673 3815278849975914928566505)
                      ·
                        rfl

theorem cell23_7430229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_7430229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430229 prefixEnd_7430229 := by exact prefixLift 7430229
  have htrace : WordTrace (prefixWord ++ tailWord_7430229) baseStart_7430229 baseEnd_7430229 := by
    simpa [prefixWord, tailWord_7430229, baseEnd_7430229] using wordTrace_append hprefix tailTrace_7430229
  have hstable : (prefixWord ++ tailWord_7430229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430229).length < 2 ^ (prefixWord ++ tailWord_7430229).sum := by decide
  have hdescent : baseEnd_7430229 < baseStart_7430229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430275 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 5]
def baseStart_7430275 : Nat := 118140960795 + 7430275 * 2 ^ 59
def prefixEnd_7430275 : Nat := 4983230072969 + 3 ^ 40 * 7430275 * 2
def baseEnd_7430275 : Nat := 3815302470086021748591293

theorem tailTrace_7430275 : CollatzResearch.WordTrace tailWord_7430275 prefixEnd_7430275 3815302470086021748591293 := by
  unfold tailWord_7430275
  simp only [CollatzResearch.WordTrace]
  refine ⟨271004393156390139785660279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180669595437593426523773519 271004393156390139785660279)
  ·
    refine ⟨406506589734585209678490419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271004393156390139785660279 406506589734585209678490419)
    ·
      refine ⟨609759884601877814517735629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406506589734585209678490419 609759884601877814517735629)
      ·
        refine ⟨228659956725704180444150861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 609759884601877814517735629 228659956725704180444150861)
        ·
          refine ⟨85747483772139067666556573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228659956725704180444150861 85747483772139067666556573)
          ·
            refine ⟨32155306414552150374958715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85747483772139067666556573 32155306414552150374958715)
            ·
              refine ⟨48232959621828225562438073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32155306414552150374958715 48232959621828225562438073)
              ·
                refine ⟨36174719716371169171828555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48232959621828225562438073 36174719716371169171828555)
                ·
                  refine ⟨54262079574556753757742833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36174719716371169171828555 54262079574556753757742833)
                  ·
                    refine ⟨40696559680917565318307125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54262079574556753757742833 40696559680917565318307125)
                    ·
                      refine ⟨3815302470086021748591293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40696559680917565318307125 3815302470086021748591293)
                      ·
                        rfl

theorem cell23_7430275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_7430275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430275 prefixEnd_7430275 := by exact prefixLift 7430275
  have htrace : WordTrace (prefixWord ++ tailWord_7430275) baseStart_7430275 baseEnd_7430275 := by
    simpa [prefixWord, tailWord_7430275, baseEnd_7430275] using wordTrace_append hprefix tailTrace_7430275
  have hstable : (prefixWord ++ tailWord_7430275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430275).length < 2 ^ (prefixWord ++ tailWord_7430275).sum := by decide
  have hdescent : baseEnd_7430275 < baseStart_7430275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430282 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 2, 5]
def baseStart_7430282 : Nat := 118140960795 + 7430282 * 2 ^ 59
def prefixEnd_7430282 : Nat := 4983230072969 + 3 ^ 40 * 7430282 * 2
def baseEnd_7430282 : Nat := 1271768688150201073734587

theorem tailTrace_7430282 : CollatzResearch.WordTrace tailWord_7430282 prefixEnd_7430282 1271768688150201073734587 := by
  unfold tailWord_7430282
  simp only [CollatzResearch.WordTrace]
  refine ⟨67751162116841194995291275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180669765644909853320776733 67751162116841194995291275)
  ·
    refine ⟨101626743175261792492936913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67751162116841194995291275 101626743175261792492936913)
    ·
      refine ⟨76220057381446344369702685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101626743175261792492936913 76220057381446344369702685)
      ·
        refine ⟨28582521518042379138638507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76220057381446344369702685 28582521518042379138638507)
        ·
          refine ⟨42873782277063568707957761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28582521518042379138638507 42873782277063568707957761)
          ·
            refine ⟨32155336707797676530968321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42873782277063568707957761 32155336707797676530968321)
            ·
              refine ⟨24116502530848257398226241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32155336707797676530968321 24116502530848257398226241)
              ·
                refine ⟨18087376898136193048669681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24116502530848257398226241 18087376898136193048669681)
                ·
                  refine ⟨13565532673602144786502261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18087376898136193048669681 13565532673602144786502261)
                  ·
                    refine ⟨1271768688150201073734587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13565532673602144786502261 1271768688150201073734587)
                    ·
                      rfl

theorem cell23_7430282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_7430282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430282 prefixEnd_7430282 := by exact prefixLift 7430282
  have htrace : WordTrace (prefixWord ++ tailWord_7430282) baseStart_7430282 baseEnd_7430282 := by
    simpa [prefixWord, tailWord_7430282, baseEnd_7430282] using wordTrace_append hprefix tailTrace_7430282
  have hstable : (prefixWord ++ tailWord_7430282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430282).length < 2 ^ (prefixWord ++ tailWord_7430282).sum := by decide
  have hdescent : baseEnd_7430282 < baseStart_7430282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430322 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_7430322 : Nat := 118140960795 + 7430322 * 2 ^ 59
def prefixEnd_7430322 : Nat := 4983230072969 + 3 ^ 40 * 7430322 * 2
def baseEnd_7430322 : Nat := 3815326603676783064703577

theorem tailTrace_7430322 : CollatzResearch.WordTrace tailWord_7430322 prefixEnd_7430322 3815326603676783064703577 := by
  unfold tailWord_7430322
  simp only [CollatzResearch.WordTrace]
  refine ⟨67751526846804966703155305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180670738258146577875080813 67751526846804966703155305)
  ·
    refine ⟨50813645135103725027366479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67751526846804966703155305 50813645135103725027366479)
    ·
      refine ⟨76220467702655587541049719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50813645135103725027366479 76220467702655587541049719)
      ·
        refine ⟨114330701553983381311574579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76220467702655587541049719 114330701553983381311574579)
        ·
          refine ⟨171496052330975071967361869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114330701553983381311574579 171496052330975071967361869)
          ·
            refine ⟨64311019624115651987760701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171496052330975071967361869 64311019624115651987760701)
            ·
              refine ⟨24116632359043369495410263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64311019624115651987760701 24116632359043369495410263)
              ·
                refine ⟨36174948538565054243115395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24116632359043369495410263 36174948538565054243115395)
                ·
                  refine ⟨54262422807847581364673093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36174948538565054243115395 54262422807847581364673093)
                  ·
                    refine ⟨10174204276471421505876205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54262422807847581364673093 10174204276471421505876205)
                    ·
                      refine ⟨3815326603676783064703577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10174204276471421505876205 3815326603676783064703577)
                      ·
                        rfl

theorem cell23_7430322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_7430322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430322 prefixEnd_7430322 := by exact prefixLift 7430322
  have htrace : WordTrace (prefixWord ++ tailWord_7430322) baseStart_7430322 baseEnd_7430322 := by
    simpa [prefixWord, tailWord_7430322, baseEnd_7430322] using wordTrace_append hprefix tailTrace_7430322
  have hstable : (prefixWord ++ tailWord_7430322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430322).length < 2 ^ (prefixWord ++ tailWord_7430322).sum := by decide
  have hdescent : baseEnd_7430322 < baseStart_7430322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430369 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 3, 1, 3]
def baseStart_7430369 : Nat := 118140960795 + 7430369 * 2 ^ 59
def prefixEnd_7430369 : Nat := 4983230072969 + 3 ^ 40 * 7430369 * 2
def baseEnd_7430369 : Nat := 3815350737267544380815861

theorem tailTrace_7430369 : CollatzResearch.WordTrace tailWord_7430369 prefixEnd_7430369 3815350737267544380815861 := by
  unfold tailWord_7430369
  simp only [CollatzResearch.WordTrace]
  refine ⟨271007821618049593839582161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180671881078699729226388107 271007821618049593839582161)
  ·
    refine ⟨203255866213537195379686621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271007821618049593839582161 203255866213537195379686621)
    ·
      refine ⟨76220949830076448267382483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203255866213537195379686621 76220949830076448267382483)
      ·
        refine ⟨114331424745114672401073725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76220949830076448267382483 114331424745114672401073725)
        ·
          refine ⟨42874284279418002150402647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114331424745114672401073725 42874284279418002150402647)
          ·
            refine ⟨64311426419127003225603971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42874284279418002150402647 64311426419127003225603971)
            ·
              refine ⟨96467139628690504838405957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64311426419127003225603971 96467139628690504838405957)
              ·
                refine ⟨18087588680379469657201117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96467139628690504838405957 18087588680379469657201117)
                ·
                  refine ⟨6782845755142301121450419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18087588680379469657201117 6782845755142301121450419)
                  ·
                    refine ⟨10174268632713451682175629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6782845755142301121450419 10174268632713451682175629)
                    ·
                      refine ⟨3815350737267544380815861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10174268632713451682175629 3815350737267544380815861)
                      ·
                        rfl

theorem cell23_7430369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_7430369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430369 prefixEnd_7430369 := by exact prefixLift 7430369
  have htrace : WordTrace (prefixWord ++ tailWord_7430369) baseStart_7430369 baseEnd_7430369 := by
    simpa [prefixWord, tailWord_7430369, baseEnd_7430369] using wordTrace_append hprefix tailTrace_7430369
  have hstable : (prefixWord ++ tailWord_7430369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430369).length < 2 ^ (prefixWord ++ tailWord_7430369).sum := by decide
  have hdescent : baseEnd_7430369 < baseStart_7430369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430379 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 2, 3, 2]
def baseStart_7430379 : Nat := 118140960795 + 7430379 * 2 ^ 59
def prefixEnd_7430379 : Nat := 4983230072969 + 3 ^ 40 * 7430379 * 2
def baseEnd_7430379 : Nat := 3815355872074089341690815

theorem tailTrace_7430379 : CollatzResearch.WordTrace tailWord_7430379 prefixEnd_7430379 3815355872074089341690815 := by
  unfold tailWord_7430379
  simp only [CollatzResearch.WordTrace]
  refine ⟨271008186348013365547446191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180672124232008910364964127 271008186348013365547446191)
  ·
    refine ⟨406512279522020048321169287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271008186348013365547446191 406512279522020048321169287)
    ·
      refine ⟨609768419283030072481753931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406512279522020048321169287 609768419283030072481753931)
      ·
        refine ⟨914652628924545108722630897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609768419283030072481753931 914652628924545108722630897)
        ·
          refine ⟨685989471693408831541973173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 914652628924545108722630897 685989471693408831541973173)
          ·
            refine ⟨64311512971257077957059985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 685989471693408831541973173 64311512971257077957059985)
            ·
              refine ⟨48233634728442808467794989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64311512971257077957059985 48233634728442808467794989)
              ·
                refine ⟨18087613023166053175423121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48233634728442808467794989 18087613023166053175423121)
                ·
                  refine ⟨13565709767374539881567341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18087613023166053175423121 13565709767374539881567341)
                  ·
                    refine ⟨5087141162765452455587753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13565709767374539881567341 5087141162765452455587753)
                    ·
                      refine ⟨3815355872074089341690815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087141162765452455587753 3815355872074089341690815)
                      ·
                        rfl

theorem cell23_7430379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 3, 2].length) (baseStart_7430379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430379 prefixEnd_7430379 := by exact prefixLift 7430379
  have htrace : WordTrace (prefixWord ++ tailWord_7430379) baseStart_7430379 baseEnd_7430379 := by
    simpa [prefixWord, tailWord_7430379, baseEnd_7430379] using wordTrace_append hprefix tailTrace_7430379
  have hstable : (prefixWord ++ tailWord_7430379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430379).length < 2 ^ (prefixWord ++ tailWord_7430379).sum := by decide
  have hdescent : baseEnd_7430379 < baseStart_7430379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430396 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 2, 3, 2]
def baseStart_7430396 : Nat := 118140960795 + 7430396 * 2 ^ 59
def prefixEnd_7430396 : Nat := 4983230072969 + 3 ^ 40 * 7430396 * 2
def baseEnd_7430396 : Nat := 3815364601245215775178237

theorem tailTrace_7430396 : CollatzResearch.WordTrace tailWord_7430396 prefixEnd_7430396 3815364601245215775178237 := by
  unfold tailWord_7430396
  simp only [CollatzResearch.WordTrace]
  refine ⟨135504403194475888725407521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180672537592634518300543361 135504403194475888725407521)
  ·
    refine ⟨101628302395856916544055641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135504403194475888725407521 101628302395856916544055641)
    ·
      refine ⟨76221226796892687408041731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101628302395856916544055641 76221226796892687408041731)
      ·
        refine ⟨114331840195339031112062597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76221226796892687408041731 114331840195339031112062597)
        ·
          refine ⟨21437220036626068333511737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114331840195339031112062597 21437220036626068333511737)
          ·
            refine ⟨16077915027469551250133803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21437220036626068333511737 16077915027469551250133803)
            ·
              refine ⟨24116872541204326875200705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16077915027469551250133803 24116872541204326875200705)
              ·
                refine ⟨18087654405903245156400529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24116872541204326875200705 18087654405903245156400529)
                ·
                  refine ⟨13565740804427433867300397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18087654405903245156400529 13565740804427433867300397)
                  ·
                    refine ⟨5087152801660287700237649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13565740804427433867300397 5087152801660287700237649)
                    ·
                      refine ⟨3815364601245215775178237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087152801660287700237649 3815364601245215775178237)
                      ·
                        rfl

theorem cell23_7430396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_7430396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430396 prefixEnd_7430396 := by exact prefixLift 7430396
  have htrace : WordTrace (prefixWord ++ tailWord_7430396) baseStart_7430396 baseEnd_7430396 := by
    simpa [prefixWord, tailWord_7430396, baseEnd_7430396] using wordTrace_append hprefix tailTrace_7430396
  have hstable : (prefixWord ++ tailWord_7430396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430396).length < 2 ^ (prefixWord ++ tailWord_7430396).sum := by decide
  have hdescent : baseEnd_7430396 < baseStart_7430396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430403 : List Nat := [1, 1, 1, 3, 2, 3, 5, 2, 1, 1, 3]
def baseStart_7430403 : Nat := 118140960795 + 7430403 * 2 ^ 59
def prefixEnd_7430403 : Nat := 4983230072969 + 3 ^ 40 * 7430403 * 2
def baseEnd_7430403 : Nat := 3815368195609797247790705

theorem tailTrace_7430403 : CollatzResearch.WordTrace tailWord_7430403 prefixEnd_7430403 3815368195609797247790705 := by
  unfold tailWord_7430403
  simp only [CollatzResearch.WordTrace]
  refine ⟨271009061699926417646319863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180672707799950945097546575 271009061699926417646319863)
  ·
    refine ⟨406513592549889626469479795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271009061699926417646319863 406513592549889626469479795)
    ·
      refine ⟨609770388824834439704219693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406513592549889626469479795 609770388824834439704219693)
      ·
        refine ⟨228663895809312914889082385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 609770388824834439704219693 228663895809312914889082385)
        ·
          refine ⟨171497921856984686166811789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228663895809312914889082385 171497921856984686166811789)
          ·
            refine ⟨64311720696369257312554421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171497921856984686166811789 64311720696369257312554421)
            ·
              refine ⟨6029223815284617873051977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64311720696369257312554421 6029223815284617873051977)
              ·
                refine ⟨4521917861463463404788983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6029223815284617873051977 4521917861463463404788983)
                ·
                  refine ⟨6782876792195195107183475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521917861463463404788983 6782876792195195107183475)
                  ·
                    refine ⟨10174315188292792660775213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6782876792195195107183475 10174315188292792660775213)
                    ·
                      refine ⟨3815368195609797247790705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10174315188292792660775213 3815368195609797247790705)
                      ·
                        rfl

theorem cell23_7430403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 1, 1, 3].length) (baseStart_7430403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430403 prefixEnd_7430403 := by exact prefixLift 7430403
  have htrace : WordTrace (prefixWord ++ tailWord_7430403) baseStart_7430403 baseEnd_7430403 := by
    simpa [prefixWord, tailWord_7430403, baseEnd_7430403] using wordTrace_append hprefix tailTrace_7430403
  have hstable : (prefixWord ++ tailWord_7430403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430403).length < 2 ^ (prefixWord ++ tailWord_7430403).sum := by decide
  have hdescent : baseEnd_7430403 < baseStart_7430403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430412 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 1, 1, 5]
def baseStart_7430412 : Nat := 118140960795 + 7430412 * 2 ^ 59
def prefixEnd_7430412 : Nat := 4983230072969 + 3 ^ 40 * 7430412 * 2
def baseEnd_7430412 : Nat := 3815372816935687712578163

theorem tailTrace_7430412 : CollatzResearch.WordTrace tailWord_7430412 prefixEnd_7430412 3815372816935687712578163 := by
  unfold tailWord_7430412
  simp only [CollatzResearch.WordTrace]
  refine ⟨135504694978446906091698745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180672926637929208122264993 135504694978446906091698745)
  ·
    refine ⟨101628521233835179568774059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135504694978446906091698745 101628521233835179568774059)
    ·
      refine ⟨152442781850752769353161089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101628521233835179568774059 152442781850752769353161089)
      ·
        refine ⟨114332086388064577014870817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152442781850752769353161089 114332086388064577014870817)
        ·
          refine ⟨85749064791048432761153113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114332086388064577014870817 85749064791048432761153113)
          ·
            refine ⟨64311798593286324570864835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85749064791048432761153113 64311798593286324570864835)
            ·
              refine ⟨96467697889929486856297253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64311798593286324570864835 96467697889929486856297253)
              ·
                refine ⟨18087693354361778785555735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96467697889929486856297253 18087693354361778785555735)
                ·
                  refine ⟨27131540031542668178333603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18087693354361778785555735 27131540031542668178333603)
                  ·
                    refine ⟨40697310047314002267500405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27131540031542668178333603 40697310047314002267500405)
                    ·
                      refine ⟨3815372816935687712578163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40697310047314002267500405 3815372816935687712578163)
                      ·
                        rfl

theorem cell23_7430412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_7430412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430412 prefixEnd_7430412 := by exact prefixLift 7430412
  have htrace : WordTrace (prefixWord ++ tailWord_7430412) baseStart_7430412 baseEnd_7430412 := by
    simpa [prefixWord, tailWord_7430412, baseEnd_7430412] using wordTrace_append hprefix tailTrace_7430412
  have hstable : (prefixWord ++ tailWord_7430412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430412).length < 2 ^ (prefixWord ++ tailWord_7430412).sum := by decide
  have hdescent : baseEnd_7430412 < baseStart_7430412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430430 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_7430430 : Nat := 118140960795 + 7430430 * 2 ^ 59
def prefixEnd_7430430 : Nat := 4983230072969 + 3 ^ 40 * 7430430 * 2
def baseEnd_7430430 : Nat := 3815382059587468642153081

theorem tailTrace_7430430 : CollatzResearch.WordTrace tailWord_7430430 prefixEnd_7430430 3815382059587468642153081 := by
  unfold tailWord_7430430
  simp only [CollatzResearch.WordTrace]
  refine ⟨33876255808853575157194093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180673364313885734171701829 33876255808853575157194093)
  ·
    refine ⟨12703595928320090683947785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33876255808853575157194093 12703595928320090683947785)
    ·
      refine ⟨9527696946240068012960839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12703595928320090683947785 9527696946240068012960839)
      ·
        refine ⟨14291545419360102019441259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9527696946240068012960839 14291545419360102019441259)
        ·
          refine ⟨21437318129040153029161889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14291545419360102019441259 21437318129040153029161889)
          ·
            refine ⟨16077988596780114771871417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21437318129040153029161889 16077988596780114771871417)
            ·
              refine ⟨12058491447585086078903563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16077988596780114771871417 12058491447585086078903563)
              ·
                refine ⟨18087737171377629118355345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12058491447585086078903563 18087737171377629118355345)
                ·
                  refine ⟨13565802878533221838766509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18087737171377629118355345 13565802878533221838766509)
                  ·
                    refine ⟨5087176079449958189537441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13565802878533221838766509 5087176079449958189537441)
                    ·
                      refine ⟨3815382059587468642153081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087176079449958189537441 3815382059587468642153081)
                      ·
                        rfl

theorem cell23_7430430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_7430430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430430 prefixEnd_7430430 := by exact prefixLift 7430430
  have htrace : WordTrace (prefixWord ++ tailWord_7430430) baseStart_7430430 baseEnd_7430430 := by
    simpa [prefixWord, tailWord_7430430, baseEnd_7430430] using wordTrace_append hprefix tailTrace_7430430
  have hstable : (prefixWord ++ tailWord_7430430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430430).length < 2 ^ (prefixWord ++ tailWord_7430430).sum := by decide
  have hdescent : baseEnd_7430430 < baseStart_7430430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430432 : List Nat := [2, 1, 1, 5, 2, 1, 2, 9]
def baseStart_7430432 : Nat := 118140960795 + 7430432 * 2 ^ 59
def prefixEnd_7430432 : Nat := 4983230072969 + 3 ^ 40 * 7430432 * 2
def baseEnd_7430432 : Nat := 141310484686991764234373

theorem tailTrace_7430432 : CollatzResearch.WordTrace tailWord_7430432 prefixEnd_7430432 141310484686991764234373 := by
  unfold tailWord_7430432
  simp only [CollatzResearch.WordTrace]
  refine ⟨135505059708410677799562775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180673412944547570399417033 135505059708410677799562775)
  ·
    refine ⟨203257589562616016699344163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135505059708410677799562775 203257589562616016699344163)
    ·
      refine ⟨304886384343924025049016245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203257589562616016699344163 304886384343924025049016245)
      ·
        refine ⟨28583098532242877348345273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 304886384343924025049016245 28583098532242877348345273)
        ·
          refine ⟨21437323899182158011258955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28583098532242877348345273 21437323899182158011258955)
          ·
            refine ⟨32155985848773237016888433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21437323899182158011258955 32155985848773237016888433)
            ·
              refine ⟨24116989386579927762666325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32155985848773237016888433 24116989386579927762666325)
              ·
                refine ⟨141310484686991764234373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24116989386579927762666325 141310484686991764234373)
                ·
                  rfl

theorem cell23_7430432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 9].length) (baseStart_7430432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430432 prefixEnd_7430432 := by exact prefixLift 7430432
  have htrace : WordTrace (prefixWord ++ tailWord_7430432) baseStart_7430432 baseEnd_7430432 := by
    simpa [prefixWord, tailWord_7430432, baseEnd_7430432] using wordTrace_append hprefix tailTrace_7430432
  have hstable : (prefixWord ++ tailWord_7430432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430432).length < 2 ^ (prefixWord ++ tailWord_7430432).sum := by decide
  have hdescent : baseEnd_7430432 < baseStart_7430432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430476 : List Nat := [2, 2, 1, 3, 2, 1, 1, 5, 2, 1, 3]
def baseStart_7430476 : Nat := 118140960795 + 7430476 * 2 ^ 59
def prefixEnd_7430476 : Nat := 4983230072969 + 3 ^ 40 * 7430476 * 2
def baseEnd_7430476 : Nat := 3815405679697575462177869

theorem tailTrace_7430476 : CollatzResearch.WordTrace tailWord_7430476 prefixEnd_7430476 3815405679697575462177869 := by
  unfold tailWord_7430476
  simp only [CollatzResearch.WordTrace]
  refine ⟨135505862114330975556863641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180674482819107967409151521 135505862114330975556863641)
  ·
    refine ⟨101629396585748231667647731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135505862114330975556863641 101629396585748231667647731)
    ·
      refine ⟨152444094878622347501471597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101629396585748231667647731 152444094878622347501471597)
      ·
        refine ⟨57166535579483380313051849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152444094878622347501471597 57166535579483380313051849)
        ·
          refine ⟨42874901684612535234788887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57166535579483380313051849 42874901684612535234788887)
          ·
            refine ⟨64312352526918802852183331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42874901684612535234788887 64312352526918802852183331)
            ·
              refine ⟨96468528790378204278274997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64312352526918802852183331 96468528790378204278274997)
              ·
                refine ⟨9043924574097956651088281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96468528790378204278274997 9043924574097956651088281)
                ·
                  refine ⟨6782943430573467488316211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9043924574097956651088281 6782943430573467488316211)
                  ·
                    refine ⟨10174415145860201232474317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6782943430573467488316211 10174415145860201232474317)
                    ·
                      refine ⟨3815405679697575462177869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10174415145860201232474317 3815405679697575462177869)
                      ·
                        rfl

theorem cell23_7430476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_7430476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430476 prefixEnd_7430476 := by exact prefixLift 7430476
  have htrace : WordTrace (prefixWord ++ tailWord_7430476) baseStart_7430476 baseEnd_7430476 := by
    simpa [prefixWord, tailWord_7430476, baseEnd_7430476] using wordTrace_append hprefix tailTrace_7430476
  have hstable : (prefixWord ++ tailWord_7430476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430476).length < 2 ^ (prefixWord ++ tailWord_7430476).sum := by decide
  have hdescent : baseEnd_7430476 < baseStart_7430476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430503 : List Nat := [1, 1, 5, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_7430503 : Nat := 118140960795 + 7430503 * 2 ^ 59
def prefixEnd_7430503 : Nat := 4983230072969 + 3 ^ 40 * 7430503 * 2
def baseEnd_7430503 : Nat := 3815419543675246856540245

theorem tailTrace_7430503 : CollatzResearch.WordTrace tailWord_7430503 prefixEnd_7430503 3815419543675246856540245 := by
  unfold tailWord_7430503
  simp only [CollatzResearch.WordTrace]
  refine ⟨271012708999564134724960163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180675139333042756483306775 271012708999564134724960163)
  ·
    refine ⟨406519063499346202087440245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271012708999564134724960163 406519063499346202087440245)
    ·
      refine ⟨38111162203063706445697523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 406519063499346202087440245 38111162203063706445697523)
      ·
        refine ⟨57166743304595559668546285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38111162203063706445697523 57166743304595559668546285)
        ·
          refine ⟨21437528739223334875704857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57166743304595559668546285 21437528739223334875704857)
          ·
            refine ⟨16078146554417501156778643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21437528739223334875704857 16078146554417501156778643)
            ·
              refine ⟨24117219831626251735167965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16078146554417501156778643 24117219831626251735167965)
              ·
                refine ⟨9043957436859844400687987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24117219831626251735167965 9043957436859844400687987)
                ·
                  refine ⟨13565936155289766601031981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9043957436859844400687987 13565936155289766601031981)
                  ·
                    refine ⟨5087226058233662475386993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13565936155289766601031981 5087226058233662475386993)
                    ·
                      refine ⟨3815419543675246856540245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087226058233662475386993 3815419543675246856540245)
                      ·
                        rfl

theorem cell23_7430503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_7430503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430503 prefixEnd_7430503 := by exact prefixLift 7430503
  have htrace : WordTrace (prefixWord ++ tailWord_7430503) baseStart_7430503 baseEnd_7430503 := by
    simpa [prefixWord, tailWord_7430503, baseEnd_7430503] using wordTrace_append hprefix tailTrace_7430503
  have hstable : (prefixWord ++ tailWord_7430503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430503).length < 2 ^ (prefixWord ++ tailWord_7430503).sum := by decide
  have hdescent : baseEnd_7430503 < baseStart_7430503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430573 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 7]
def baseStart_7430573 : Nat := 118140960795 + 7430573 * 2 ^ 59
def prefixEnd_7430573 : Nat := 4983230072969 + 3 ^ 40 * 7430573 * 2
def baseEnd_7430573 : Nat := 423939498591229064740547

theorem tailTrace_7430573 : CollatzResearch.WordTrace tailWord_7430573 prefixEnd_7430573 423939498591229064740547 := by
  unfold tailWord_7430573
  simp only [CollatzResearch.WordTrace]
  refine ⟨271015262109310536680008373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180676841406207024453338915 271015262109310536680008373)
  ·
    refine ⟨25407680822747862813750785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271015262109310536680008373 25407680822747862813750785)
    ·
      refine ⟨19055760617060897110313089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25407680822747862813750785 19055760617060897110313089)
      ·
        refine ⟨14291820462795672832734817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19055760617060897110313089 14291820462795672832734817)
        ·
          refine ⟨10718865347096754624551113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14291820462795672832734817 10718865347096754624551113)
          ·
            refine ⟨8039149010322565968413335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10718865347096754624551113 8039149010322565968413335)
            ·
              refine ⟨12058723515483848952620003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8039149010322565968413335 12058723515483848952620003)
              ·
                refine ⟨18088085273225773428930005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12058723515483848952620003 18088085273225773428930005)
                ·
                  refine ⟨423939498591229064740547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18088085273225773428930005 423939498591229064740547)
                  ·
                    rfl

theorem cell23_7430573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_7430573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430573 prefixEnd_7430573 := by exact prefixLift 7430573
  have htrace : WordTrace (prefixWord ++ tailWord_7430573) baseStart_7430573 baseEnd_7430573 := by
    simpa [prefixWord, tailWord_7430573, baseEnd_7430573] using wordTrace_append hprefix tailTrace_7430573
  have hstable : (prefixWord ++ tailWord_7430573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430573).length < 2 ^ (prefixWord ++ tailWord_7430573).sum := by decide
  have hdescent : baseEnd_7430573 < baseStart_7430573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430606 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2]
def baseStart_7430606 : Nat := 118140960795 + 7430606 * 2 ^ 59
def prefixEnd_7430606 : Nat := 4983230072969 + 3 ^ 40 * 7430606 * 2
def baseEnd_7430606 : Nat := 3815472432182659953552271

theorem tailTrace_7430606 : CollatzResearch.WordTrace tailWord_7430606 prefixEnd_7430606 3815472432182659953552271 := by
  unfold tailWord_7430606
  simp only [CollatzResearch.WordTrace]
  refine ⟨33877058214773872914494959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180677643812127322210639781 33877058214773872914494959)
  ·
    refine ⟨50815587322160809371742439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33877058214773872914494959 50815587322160809371742439)
    ·
      refine ⟨76223380983241214057613659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50815587322160809371742439 76223380983241214057613659)
      ·
        refine ⟨114335071474861821086420489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76223380983241214057613659 114335071474861821086420489)
        ·
          refine ⟨85751303606146365814815367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114335071474861821086420489 85751303606146365814815367)
          ·
            refine ⟨128626955409219548722223051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85751303606146365814815367 128626955409219548722223051)
            ·
              refine ⟨192940433113829323083334577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128626955409219548722223051 192940433113829323083334577)
              ·
                refine ⟨144705324835371992312500933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192940433113829323083334577 144705324835371992312500933)
                ·
                  refine ⟨27132248406632248558593925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144705324835371992312500933 27132248406632248558593925)
                  ·
                    refine ⟨5087296576243546604736361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27132248406632248558593925 5087296576243546604736361)
                    ·
                      refine ⟨3815472432182659953552271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087296576243546604736361 3815472432182659953552271)
                      ·
                        rfl

theorem cell23_7430606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_7430606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430606 prefixEnd_7430606 := by exact prefixLift 7430606
  have htrace : WordTrace (prefixWord ++ tailWord_7430606) baseStart_7430606 baseEnd_7430606 := by
    simpa [prefixWord, tailWord_7430606, baseEnd_7430606] using wordTrace_append hprefix tailTrace_7430606
  have hstable : (prefixWord ++ tailWord_7430606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430606).length < 2 ^ (prefixWord ++ tailWord_7430606).sum := by decide
  have hdescent : baseEnd_7430606 < baseStart_7430606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430609 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 1, 4, 3]
def baseStart_7430609 : Nat := 118140960795 + 7430609 * 2 ^ 59
def prefixEnd_7430609 : Nat := 4983230072969 + 3 ^ 40 * 7430609 * 2
def baseEnd_7430609 : Nat := 3815473972624623441814757

theorem tailTrace_7430609 : CollatzResearch.WordTrace tailWord_7430609 prefixEnd_7430609 3815473972624623441814757 := by
  unfold tailWord_7430609
  simp only [CollatzResearch.WordTrace]
  refine ⟨271016575137180114828318881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180677716758120076552212587 271016575137180114828318881)
  ·
    refine ⟨203262431352885086121239161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271016575137180114828318881 203262431352885086121239161)
    ·
      refine ⟨152446823514663814590929371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203262431352885086121239161 152446823514663814590929371)
      ·
        refine ⟨228670235271995721886394057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152446823514663814590929371 228670235271995721886394057)
        ·
          refine ⟨171502676453996791414795543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228670235271995721886394057 171502676453996791414795543)
          ·
            refine ⟨257254014680995187122193315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171502676453996791414795543 257254014680995187122193315)
            ·
              refine ⟨385881022021492780683289973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257254014680995187122193315 385881022021492780683289973)
              ·
                refine ⟨36176345814514948189058435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 385881022021492780683289973 36176345814514948189058435)
                ·
                  refine ⟨54264518721772422283587653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36176345814514948189058435 54264518721772422283587653)
                  ·
                    refine ⟨10174597260332329178172685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54264518721772422283587653 10174597260332329178172685)
                    ·
                      refine ⟨3815473972624623441814757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10174597260332329178172685 3815473972624623441814757)
                      ·
                        rfl

theorem cell23_7430609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_7430609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430609 prefixEnd_7430609 := by exact prefixLift 7430609
  have htrace : WordTrace (prefixWord ++ tailWord_7430609) baseStart_7430609 baseEnd_7430609 := by
    simpa [prefixWord, tailWord_7430609, baseEnd_7430609] using wordTrace_append hprefix tailTrace_7430609
  have hstable : (prefixWord ++ tailWord_7430609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430609).length < 2 ^ (prefixWord ++ tailWord_7430609).sum := by decide
  have hdescent : baseEnd_7430609 < baseStart_7430609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430639 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 3]
def baseStart_7430639 : Nat := 118140960795 + 7430639 * 2 ^ 59
def prefixEnd_7430639 : Nat := 4983230072969 + 3 ^ 40 * 7430639 * 2
def baseEnd_7430639 : Nat := 3815489377044258324439619

theorem tailTrace_7430639 : CollatzResearch.WordTrace tailWord_7430639 prefixEnd_7430639 3815489377044258324439619 := by
  unfold tailWord_7430639
  simp only [CollatzResearch.WordTrace]
  refine ⟨271017669327071429951910971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180678446218047619967940647 271017669327071429951910971)
  ·
    refine ⟨406526503990607144927866457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271017669327071429951910971 406526503990607144927866457)
    ·
      refine ⟨304894877992955358695899843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406526503990607144927866457 304894877992955358695899843)
      ·
        refine ⟨457342316989433038043849765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304894877992955358695899843 457342316989433038043849765)
        ·
          refine ⟨85751684435518694633221831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 457342316989433038043849765 85751684435518694633221831)
          ·
            refine ⟨128627526653278041949832747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85751684435518694633221831 128627526653278041949832747)
            ·
              refine ⟨192941289979917062924749121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128627526653278041949832747 192941289979917062924749121)
              ·
                refine ⟨144705967484937797193561841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192941289979917062924749121 144705967484937797193561841)
                ·
                  refine ⟨108529475613703347895171381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144705967484937797193561841 108529475613703347895171381)
                  ·
                    refine ⟨10174638338784688865172317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108529475613703347895171381 10174638338784688865172317)
                    ·
                      refine ⟨3815489377044258324439619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10174638338784688865172317 3815489377044258324439619)
                      ·
                        rfl

theorem cell23_7430639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 3].length) (baseStart_7430639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430639 prefixEnd_7430639 := by exact prefixLift 7430639
  have htrace : WordTrace (prefixWord ++ tailWord_7430639) baseStart_7430639 baseEnd_7430639 := by
    simpa [prefixWord, tailWord_7430639, baseEnd_7430639] using wordTrace_append hprefix tailTrace_7430639
  have hstable : (prefixWord ++ tailWord_7430639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430639).length < 2 ^ (prefixWord ++ tailWord_7430639).sum := by decide
  have hdescent : baseEnd_7430639 < baseStart_7430639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430646 : List Nat := [5, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_7430646 : Nat := 118140960795 + 7430646 * 2 ^ 59
def prefixEnd_7430646 : Nat := 4983230072969 + 3 ^ 40 * 7430646 * 2
def baseEnd_7430646 : Nat := 423943663489871088561343

theorem tailTrace_7430646 : CollatzResearch.WordTrace tailWord_7430646 prefixEnd_7430646 423943663489871088561343 := by
  unfold tailWord_7430646
  simp only [CollatzResearch.WordTrace]
  refine ⟨16938620289877879384213487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180678616425364046764943861 16938620289877879384213487)
  ·
    refine ⟨25407930434816819076320231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16938620289877879384213487 25407930434816819076320231)
    ·
      refine ⟨38111895652225228614480347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25407930434816819076320231 38111895652225228614480347)
      ·
        refine ⟨57167843478337842921720521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38111895652225228614480347 57167843478337842921720521)
        ·
          refine ⟨42875882608753382191290391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57167843478337842921720521 42875882608753382191290391)
          ·
            refine ⟨64313823913130073286935587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42875882608753382191290391 64313823913130073286935587)
            ·
              refine ⟨96470735869695109930403381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64313823913130073286935587 96470735869695109930403381)
              ·
                refine ⟨9044131487783916555975317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96470735869695109930403381 9044131487783916555975317)
                ·
                  refine ⟨423943663489871088561343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9044131487783916555975317 423943663489871088561343)
                  ·
                    rfl

theorem cell23_7430646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_7430646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430646 prefixEnd_7430646 := by exact prefixLift 7430646
  have htrace : WordTrace (prefixWord ++ tailWord_7430646) baseStart_7430646 baseEnd_7430646 := by
    simpa [prefixWord, tailWord_7430646, baseEnd_7430646] using wordTrace_append hprefix tailTrace_7430646
  have hstable : (prefixWord ++ tailWord_7430646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430646).length < 2 ^ (prefixWord ++ tailWord_7430646).sum := by decide
  have hdescent : baseEnd_7430646 < baseStart_7430646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430659 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 3, 5]
def baseStart_7430659 : Nat := 118140960795 + 7430659 * 2 ^ 59
def prefixEnd_7430659 : Nat := 4983230072969 + 3 ^ 40 * 7430659 * 2
def baseEnd_7430659 : Nat := 1271833215552449415396509

theorem tailTrace_7430659 : CollatzResearch.WordTrace tailWord_7430659 prefixEnd_7430659 1271833215552449415396509 := by
  unfold tailWord_7430659
  simp only [CollatzResearch.WordTrace]
  refine ⟨271018398786998973367639031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180678932524665982245092687 271018398786998973367639031)
  ·
    refine ⟨406527598180498460051458547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271018398786998973367639031 406527598180498460051458547)
    ·
      refine ⟨609791397270747690077187821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406527598180498460051458547 609791397270747690077187821)
      ·
        refine ⟨228671773976530383778945433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 609791397270747690077187821 228671773976530383778945433)
        ·
          refine ⟨171503830482397787834209075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228671773976530383778945433 171503830482397787834209075)
          ·
            refine ⟨257255745723596681751313613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171503830482397787834209075 257255745723596681751313613)
            ·
              refine ⟨96470904646348755656742605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257255745723596681751313613 96470904646348755656742605)
              ·
                refine ⟨36176589242380783371278477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96470904646348755656742605 36176589242380783371278477)
                ·
                  refine ⟨13566220965892793764229429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36176589242380783371278477 13566220965892793764229429)
                  ·
                    refine ⟨1271833215552449415396509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13566220965892793764229429 1271833215552449415396509)
                    ·
                      rfl

theorem cell23_7430659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 5].length) (baseStart_7430659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430659 prefixEnd_7430659 := by exact prefixLift 7430659
  have htrace : WordTrace (prefixWord ++ tailWord_7430659) baseStart_7430659 baseEnd_7430659 := by
    simpa [prefixWord, tailWord_7430659, baseEnd_7430659] using wordTrace_append hprefix tailTrace_7430659
  have hstable : (prefixWord ++ tailWord_7430659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430659).length < 2 ^ (prefixWord ++ tailWord_7430659).sum := by decide
  have hdescent : baseEnd_7430659 < baseStart_7430659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430660 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_7430660 : Nat := 118140960795 + 7430660 * 2 ^ 59
def prefixEnd_7430660 : Nat := 4983230072969 + 3 ^ 40 * 7430660 * 2
def baseEnd_7430660 : Nat := 3815500160138002742277023

theorem tailTrace_7430660 : CollatzResearch.WordTrace tailWord_7430660 prefixEnd_7430660 3815500160138002742277023 := by
  unfold tailWord_7430660
  simp only [CollatzResearch.WordTrace]
  refine ⟨135509217629997675269212717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180678956839996900358950289 135509217629997675269212717)
  ·
    refine ⟨50815956611249128225954769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135509217629997675269212717 50815956611249128225954769)
    ·
      refine ⟨38111967458436846169466077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50815956611249128225954769 38111967458436846169466077)
      ·
        refine ⟨14291987796913817313549779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38111967458436846169466077 14291987796913817313549779)
        ·
          refine ⟨21437981695370725970324669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14291987796913817313549779 21437981695370725970324669)
          ·
            refine ⟨8039243135764022238871751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21437981695370725970324669 8039243135764022238871751)
            ·
              refine ⟨12058864703646033358307627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8039243135764022238871751 12058864703646033358307627)
              ·
                refine ⟨18088297055469050037461441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12058864703646033358307627 18088297055469050037461441)
                ·
                  refine ⟨13566222791601787528096081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18088297055469050037461441 13566222791601787528096081)
                  ·
                    refine ⟨10174667093701340646072061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13566222791601787528096081 10174667093701340646072061)
                    ·
                      refine ⟨3815500160138002742277023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10174667093701340646072061 3815500160138002742277023)
                      ·
                        rfl

theorem cell23_7430660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_7430660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430660 prefixEnd_7430660 := by exact prefixLift 7430660
  have htrace : WordTrace (prefixWord ++ tailWord_7430660) baseStart_7430660 baseEnd_7430660 := by
    simpa [prefixWord, tailWord_7430660, baseEnd_7430660] using wordTrace_append hprefix tailTrace_7430660
  have hstable : (prefixWord ++ tailWord_7430660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430660).length < 2 ^ (prefixWord ++ tailWord_7430660).sum := by decide
  have hdescent : baseEnd_7430660 < baseStart_7430660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430706 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_7430706 : Nat := 118140960795 + 7430706 * 2 ^ 59
def prefixEnd_7430706 : Nat := 4983230072969 + 3 ^ 40 * 7430706 * 2
def baseEnd_7430706 : Nat := 1271841260082703187433937

theorem tailTrace_7430706 : CollatzResearch.WordTrace tailWord_7430706 prefixEnd_7430706 1271841260082703187433937 := by
  unfold tailWord_7430706
  simp only [CollatzResearch.WordTrace]
  refine ⟨67755028254457175098649993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180680075345219133596399981 67755028254457175098649993)
  ·
    refine ⟨50816271190842881323987495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67755028254457175098649993 50816271190842881323987495)
    ·
      refine ⟨76224406786264321985981243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50816271190842881323987495 76224406786264321985981243)
      ·
        refine ⟨114336610179396482978971865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76224406786264321985981243 114336610179396482978971865)
        ·
          refine ⟨85752457634547362234228899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114336610179396482978971865 85752457634547362234228899)
          ·
            refine ⟨128628686451821043351343349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85752457634547362234228899 128628686451821043351343349)
            ·
              refine ⟨12058939354858222814188439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128628686451821043351343349 12058939354858222814188439)
              ·
                refine ⟨18088409032287334221282659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12058939354858222814188439 18088409032287334221282659)
                ·
                  refine ⟨27132613548431001331923989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18088409032287334221282659 27132613548431001331923989)
                  ·
                    refine ⟨1271841260082703187433937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27132613548431001331923989 1271841260082703187433937)
                    ·
                      rfl

theorem cell23_7430706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_7430706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430706 prefixEnd_7430706 := by exact prefixLift 7430706
  have htrace : WordTrace (prefixWord ++ tailWord_7430706) baseStart_7430706 baseEnd_7430706 := by
    simpa [prefixWord, tailWord_7430706, baseEnd_7430706] using wordTrace_append hprefix tailTrace_7430706
  have hstable : (prefixWord ++ tailWord_7430706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430706).length < 2 ^ (prefixWord ++ tailWord_7430706).sum := by decide
  have hdescent : baseEnd_7430706 < baseStart_7430706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430710 : List Nat := [5, 1, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_7430710 : Nat := 118140960795 + 7430710 * 2 ^ 59
def prefixEnd_7430710 : Nat := 4983230072969 + 3 ^ 40 * 7430710 * 2
def baseEnd_7430710 : Nat := 1271841944723575848883931

theorem tailTrace_7430710 : CollatzResearch.WordTrace tailWord_7430710 prefixEnd_7430710 1271841944723575848883931 := by
  unfold tailWord_7430710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16938766181863388067359099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180680172606542806051830389 16938766181863388067359099)
  ·
    refine ⟨25408149272795082101038649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16938766181863388067359099 25408149272795082101038649)
    ·
      refine ⟨19056111954596311575778987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25408149272795082101038649 19056111954596311575778987)
      ·
        refine ⟨28584167931894467363668481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19056111954596311575778987 28584167931894467363668481)
        ·
          refine ⟨21438125948920850522751361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28584167931894467363668481 21438125948920850522751361)
          ·
            refine ⟨16078594461690637892063521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21438125948920850522751361 16078594461690637892063521)
            ·
              refine ⟨12058945846267978419047641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16078594461690637892063521 12058945846267978419047641)
              ·
                refine ⟨9044209384700983814285731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12058945846267978419047641 9044209384700983814285731)
                ·
                  refine ⟨13566314077051475721428597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9044209384700983814285731 13566314077051475721428597)
                  ·
                    refine ⟨1271841944723575848883931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13566314077051475721428597 1271841944723575848883931)
                    ·
                      rfl

theorem cell23_7430710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_7430710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430710 prefixEnd_7430710 := by exact prefixLift 7430710
  have htrace : WordTrace (prefixWord ++ tailWord_7430710) baseStart_7430710 baseEnd_7430710 := by
    simpa [prefixWord, tailWord_7430710, baseEnd_7430710] using wordTrace_append hprefix tailTrace_7430710
  have hstable : (prefixWord ++ tailWord_7430710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430710).length < 2 ^ (prefixWord ++ tailWord_7430710).sum := by decide
  have hdescent : baseEnd_7430710 < baseStart_7430710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430713 : List Nat := [1, 2, 1, 5, 1, 1, 4, 2, 1, 1, 4]
def baseStart_7430713 : Nat := 118140960795 + 7430713 * 2 ^ 59
def prefixEnd_7430713 : Nat := 4983230072969 + 3 ^ 40 * 7430713 * 2
def baseEnd_7430713 : Nat := 3815527374612691034914279

theorem tailTrace_7430713 : CollatzResearch.WordTrace tailWord_7430713 prefixEnd_7430713 3815527374612691034914279 := by
  unfold tailWord_7430713
  simp only [CollatzResearch.WordTrace]
  refine ⟨271020368328803340590104793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180680245552535560393403195 271020368328803340590104793)
  ·
    refine ⟨203265276246602505442578595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271020368328803340590104793 203265276246602505442578595)
    ·
      refine ⟨304897914369903758163867893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203265276246602505442578595 304897914369903758163867893)
      ·
        refine ⟨28584179472178477327862615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 304897914369903758163867893 28584179472178477327862615)
        ·
          refine ⟨42876269208267715991793923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28584179472178477327862615 42876269208267715991793923)
          ·
            refine ⟨64314403812401573987690885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42876269208267715991793923 64314403812401573987690885)
            ·
              refine ⟨12058950714825295122692041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64314403812401573987690885 12058950714825295122692041)
              ·
                refine ⟨9044213036118971342019031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12058950714825295122692041 9044213036118971342019031)
                ·
                  refine ⟨13566319554178457013028547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9044213036118971342019031 13566319554178457013028547)
                  ·
                    refine ⟨20349479331267685519542821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13566319554178457013028547 20349479331267685519542821)
                    ·
                      refine ⟨3815527374612691034914279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20349479331267685519542821 3815527374612691034914279)
                      ·
                        rfl

theorem cell23_7430713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_7430713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430713 prefixEnd_7430713 := by exact prefixLift 7430713
  have htrace : WordTrace (prefixWord ++ tailWord_7430713) baseStart_7430713 baseEnd_7430713 := by
    simpa [prefixWord, tailWord_7430713, baseEnd_7430713] using wordTrace_append hprefix tailTrace_7430713
  have hstable : (prefixWord ++ tailWord_7430713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430713).length < 2 ^ (prefixWord ++ tailWord_7430713).sum := by decide
  have hdescent : baseEnd_7430713 < baseStart_7430713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430719 : List Nat := [1, 1, 2, 2, 3, 2, 3, 9]
def baseStart_7430719 : Nat := 118140960795 + 7430719 * 2 ^ 59
def prefixEnd_7430719 : Nat := 4983230072969 + 3 ^ 40 * 7430719 * 2
def baseEnd_7430719 : Nat := 141315942796171037460713

theorem tailTrace_7430719 : CollatzResearch.WordTrace tailWord_7430719 prefixEnd_7430719 141315942796171037460713 := by
  unfold tailWord_7430719
  simp only [CollatzResearch.WordTrace]
  refine ⟨271020587166781603614823211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180680391444521069076548807 271020587166781603614823211)
  ·
    refine ⟨406530880750172405422234817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271020587166781603614823211 406530880750172405422234817)
    ·
      refine ⟨304898160562629304066676113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406530880750172405422234817 304898160562629304066676113)
      ·
        refine ⟨228673620421971978050007085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304898160562629304066676113 228673620421971978050007085)
        ·
          refine ⟨85752607658239491768752657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228673620421971978050007085 85752607658239491768752657)
          ·
            refine ⟨64314455743679618826564493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85752607658239491768752657 64314455743679618826564493)
            ·
              refine ⟨24117920903879857059961685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64314455743679618826564493 24117920903879857059961685)
              ·
                refine ⟨141315942796171037460713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24117920903879857059961685 141315942796171037460713)
                ·
                  rfl

theorem cell23_7430719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 9].length) (baseStart_7430719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430719 prefixEnd_7430719 := by exact prefixLift 7430719
  have htrace : WordTrace (prefixWord ++ tailWord_7430719) baseStart_7430719 baseEnd_7430719 := by
    simpa [prefixWord, tailWord_7430719, baseEnd_7430719] using wordTrace_append hprefix tailTrace_7430719
  have hstable : (prefixWord ++ tailWord_7430719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430719).length < 2 ^ (prefixWord ++ tailWord_7430719).sum := by decide
  have hdescent : baseEnd_7430719 < baseStart_7430719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430733 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_7430733 : Nat := 118140960795 + 7430733 * 2 ^ 59
def prefixEnd_7430733 : Nat := 4983230072969 + 3 ^ 40 * 7430733 * 2
def baseEnd_7430733 : Nat := 3815537644225780956664187

theorem tailTrace_7430733 : CollatzResearch.WordTrace tailWord_7430733 prefixEnd_7430733 3815537644225780956664187 := by
  unfold tailWord_7430733
  simp only [CollatzResearch.WordTrace]
  refine ⟨271021097788730884005832853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180680731859153922670555235 271021097788730884005832853)
  ·
    refine ⟨12704113958846760187773415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 271021097788730884005832853 12704113958846760187773415)
    ·
      refine ⟨19056170938270140281660123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12704113958846760187773415 19056170938270140281660123)
      ·
        refine ⟨28584256407405210422490185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19056170938270140281660123 28584256407405210422490185)
        ·
          refine ⟨21438192305553907816867639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28584256407405210422490185 21438192305553907816867639)
          ·
            refine ⟨32157288458330861725301459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21438192305553907816867639 32157288458330861725301459)
            ·
              refine ⟨48235932687496292587952189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32157288458330861725301459 48235932687496292587952189)
              ·
                refine ⟨18088474757811109720482071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48235932687496292587952189 18088474757811109720482071)
                ·
                  refine ⟨27132712136716664580723107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18088474757811109720482071 27132712136716664580723107)
                  ·
                    refine ⟨40699068205074996871084661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27132712136716664580723107 40699068205074996871084661)
                    ·
                      refine ⟨3815537644225780956664187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40699068205074996871084661 3815537644225780956664187)
                      ·
                        rfl

theorem cell23_7430733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_7430733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430733 prefixEnd_7430733 := by exact prefixLift 7430733
  have htrace : WordTrace (prefixWord ++ tailWord_7430733) baseStart_7430733 baseEnd_7430733 := by
    simpa [prefixWord, tailWord_7430733, baseEnd_7430733] using wordTrace_append hprefix tailTrace_7430733
  have hstable : (prefixWord ++ tailWord_7430733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430733).length < 2 ^ (prefixWord ++ tailWord_7430733).sum := by decide
  have hdescent : baseEnd_7430733 < baseStart_7430733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430757 : List Nat := [1, 3, 1, 3, 4, 2, 2, 1, 2, 4]
def baseStart_7430757 : Nat := 118140960795 + 7430757 * 2 ^ 59
def prefixEnd_7430757 : Nat := 4983230072969 + 3 ^ 40 * 7430757 * 2
def baseEnd_7430757 : Nat := 1271849989253829620921359

theorem tailTrace_7430757 : CollatzResearch.WordTrace tailWord_7430757 prefixEnd_7430757 1271849989253829620921359 := by
  unfold tailWord_7430757
  simp only [CollatzResearch.WordTrace]
  refine ⟨271021973140643936104706525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180681315427095957403137683 271021973140643936104706525)
  ·
    refine ⟨101633239927741476039264947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271021973140643936104706525 101633239927741476039264947)
    ·
      refine ⟨152449859891612214058897421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101633239927741476039264947 152449859891612214058897421)
      ·
        refine ⟨57168697459354580272086533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152449859891612214058897421 57168697459354580272086533)
        ·
          refine ⟨10719130773628983801016225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57168697459354580272086533 10719130773628983801016225)
          ·
            refine ⟨8039348080221737850762169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10719130773628983801016225 8039348080221737850762169)
            ·
              refine ⟨6029511060166303388071627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8039348080221737850762169 6029511060166303388071627)
              ·
                refine ⟨9044266590249455082107441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6029511060166303388071627 9044266590249455082107441)
                ·
                  refine ⟨6783199942687091311580581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9044266590249455082107441 6783199942687091311580581)
                  ·
                    refine ⟨1271849989253829620921359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6783199942687091311580581 1271849989253829620921359)
                    ·
                      rfl

theorem cell23_7430757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_7430757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430757 prefixEnd_7430757 := by exact prefixLift 7430757
  have htrace : WordTrace (prefixWord ++ tailWord_7430757) baseStart_7430757 baseEnd_7430757 := by
    simpa [prefixWord, tailWord_7430757, baseEnd_7430757] using wordTrace_append hprefix tailTrace_7430757
  have hstable : (prefixWord ++ tailWord_7430757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430757).length < 2 ^ (prefixWord ++ tailWord_7430757).sum := by decide
  have hdescent : baseEnd_7430757 < baseStart_7430757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430769 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_7430769 : Nat := 118140960795 + 7430769 * 2 ^ 59
def prefixEnd_7430769 : Nat := 4983230072969 + 3 ^ 40 * 7430769 * 2
def baseEnd_7430769 : Nat := 3815556129529342815814021

theorem tailTrace_7430769 : CollatzResearch.WordTrace tailWord_7430769 prefixEnd_7430769 3815556129529342815814021 := by
  unfold tailWord_7430769
  simp only [CollatzResearch.WordTrace]
  refine ⟨271022410816600462154143361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180681607211066974769428907 271022410816600462154143361)
  ·
    refine ⟨203266808112450346615607521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271022410816600462154143361 203266808112450346615607521)
    ·
      refine ⟨152450106084337759961705641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203266808112450346615607521 152450106084337759961705641)
      ·
        refine ⟨114337579563253319971279231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152450106084337759961705641 114337579563253319971279231)
        ·
          refine ⟨171506369344879979956918847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114337579563253319971279231 171506369344879979956918847)
          ·
            refine ⟨257259554017319969935378271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171506369344879979956918847 257259554017319969935378271)
            ·
              refine ⟨385889331025979954903067407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257259554017319969935378271 385889331025979954903067407)
              ·
                refine ⟨578833996538969932354601111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385889331025979954903067407 578833996538969932354601111)
                ·
                  refine ⟨868250994808454898531901667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578833996538969932354601111 868250994808454898531901667)
                  ·
                    refine ⟨1302376492212682347797852501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 868250994808454898531901667 1302376492212682347797852501)
                    ·
                      refine ⟨3815556129529342815814021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1302376492212682347797852501 3815556129529342815814021)
                      ·
                        rfl

theorem cell23_7430769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_7430769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430769 prefixEnd_7430769 := by exact prefixLift 7430769
  have htrace : WordTrace (prefixWord ++ tailWord_7430769) baseStart_7430769 baseEnd_7430769 := by
    simpa [prefixWord, tailWord_7430769, baseEnd_7430769] using wordTrace_append hprefix tailTrace_7430769
  have hstable : (prefixWord ++ tailWord_7430769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430769).length < 2 ^ (prefixWord ++ tailWord_7430769).sum := by decide
  have hdescent : baseEnd_7430769 < baseStart_7430769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430779 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 3, 8]
def baseStart_7430779 : Nat := 118140960795 + 7430779 * 2 ^ 59
def prefixEnd_7430779 : Nat := 4983230072969 + 3 ^ 40 * 7430779 * 2
def baseEnd_7430779 : Nat := 1271853754778629258896325

theorem tailTrace_7430779 : CollatzResearch.WordTrace tailWord_7430779 prefixEnd_7430779 1271853754778629258896325 := by
  unfold tailWord_7430779
  simp only [CollatzResearch.WordTrace]
  refine ⟨271022775546564233862007391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180681850364376155908004927 271022775546564233862007391)
  ·
    refine ⟨406534163319846350793011087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271022775546564233862007391 406534163319846350793011087)
    ·
      refine ⟨609801244979769526189516631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406534163319846350793011087 609801244979769526189516631)
      ·
        refine ⟨914701867469654289284274947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609801244979769526189516631 914701867469654289284274947)
        ·
          refine ⟨1372052801204481433926412421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914701867469654289284274947 1372052801204481433926412421)
          ·
            refine ⟨257259900225840268861202329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1372052801204481433926412421 257259900225840268861202329)
            ·
              refine ⟨192944925169380201645901747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257259900225840268861202329 192944925169380201645901747)
              ·
                refine ⟨289417387754070302468852621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192944925169380201645901747 289417387754070302468852621)
                ·
                  refine ⟨108531520407776363425819733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289417387754070302468852621 108531520407776363425819733)
                  ·
                    refine ⟨1271853754778629258896325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108531520407776363425819733 1271853754778629258896325)
                    ·
                      rfl

theorem cell23_7430779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 8].length) (baseStart_7430779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430779 prefixEnd_7430779 := by exact prefixLift 7430779
  have htrace : WordTrace (prefixWord ++ tailWord_7430779) baseStart_7430779 baseEnd_7430779 := by
    simpa [prefixWord, tailWord_7430779, baseEnd_7430779] using wordTrace_append hprefix tailTrace_7430779
  have hstable : (prefixWord ++ tailWord_7430779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430779).length < 2 ^ (prefixWord ++ tailWord_7430779).sum := by decide
  have hdescent : baseEnd_7430779 < baseStart_7430779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430820 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 1, 4, 2]
def baseStart_7430820 : Nat := 118140960795 + 7430820 * 2 ^ 59
def prefixEnd_7430820 : Nat := 4983230072969 + 3 ^ 40 * 7430820 * 2
def baseEnd_7430820 : Nat := 3815582317042722116276287

theorem tailTrace_7430820 : CollatzResearch.WordTrace tailWord_7430820 prefixEnd_7430820 3815582317042722116276287 := by
  unfold tailWord_7430820
  simp only [CollatzResearch.WordTrace]
  refine ⟨135512135469707848932124957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180682847292943798576166609 135512135469707848932124957)
  ·
    refine ⟨50817050801140443349546859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135512135469707848932124957 50817050801140443349546859)
    ·
      refine ⟨76225576201710665024320289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50817050801140443349546859 76225576201710665024320289)
      ·
        refine ⟨57169182151282998768240217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76225576201710665024320289 57169182151282998768240217)
        ·
          refine ⟨42876886613462249076180163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57169182151282998768240217 42876886613462249076180163)
          ·
            refine ⟨64315329920193373614270245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42876886613462249076180163 64315329920193373614270245)
            ·
              refine ⟨12059124360036257552675671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64315329920193373614270245 12059124360036257552675671)
              ·
                refine ⟨18088686540054386329013507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12059124360036257552675671 18088686540054386329013507)
                ·
                  refine ⟨27133029810081579493520261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18088686540054386329013507 27133029810081579493520261)
                  ·
                    refine ⟨5087443089390296155035049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27133029810081579493520261 5087443089390296155035049)
                    ·
                      refine ⟨3815582317042722116276287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087443089390296155035049 3815582317042722116276287)
                      ·
                        rfl

theorem cell23_7430820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_7430820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430820 prefixEnd_7430820 := by exact prefixLift 7430820
  have htrace : WordTrace (prefixWord ++ tailWord_7430820) baseStart_7430820 baseEnd_7430820 := by
    simpa [prefixWord, tailWord_7430820, baseEnd_7430820] using wordTrace_append hprefix tailTrace_7430820
  have hstable : (prefixWord ++ tailWord_7430820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430820).length < 2 ^ (prefixWord ++ tailWord_7430820).sum := by decide
  have hdescent : baseEnd_7430820 < baseStart_7430820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430860 : List Nat := [2, 2, 1, 5, 1, 1, 2, 4, 5]
def baseStart_7430860 : Nat := 118140960795 + 7430860 * 2 ^ 59
def prefixEnd_7430860 : Nat := 4983230072969 + 3 ^ 40 * 7430860 * 2
def baseEnd_7430860 : Nat := 423955872918766884419567

theorem tailTrace_7430860 : CollatzResearch.WordTrace tailWord_7430860 prefixEnd_7430860 423955872918766884419567 := by
  unfold tailWord_7430860
  simp only [CollatzResearch.WordTrace]
  refine ⟨135512864929635392347853017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180683819906180523130470689 135512864929635392347853017)
  ·
    refine ⟨101634648697226544260889763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135512864929635392347853017 101634648697226544260889763)
    ·
      refine ⟨152451973045839816391334645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101634648697226544260889763 152451973045839816391334645)
      ·
        refine ⟨14292372473047482786687623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152451973045839816391334645 14292372473047482786687623)
        ·
          refine ⟨21438558709571224180031435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14292372473047482786687623 21438558709571224180031435)
          ·
            refine ⟨32157838064356836270047153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21438558709571224180031435 32157838064356836270047153)
            ·
              refine ⟨24118378548267627202535365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32157838064356836270047153 24118378548267627202535365)
              ·
                refine ⟨4522195977800180100475381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24118378548267627202535365 4522195977800180100475381)
                ·
                  refine ⟨423955872918766884419567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4522195977800180100475381 423955872918766884419567)
                  ·
                    rfl

theorem cell23_7430860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 5].length) (baseStart_7430860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430860 prefixEnd_7430860 := by exact prefixLift 7430860
  have htrace : WordTrace (prefixWord ++ tailWord_7430860) baseStart_7430860 baseEnd_7430860 := by
    simpa [prefixWord, tailWord_7430860, baseEnd_7430860] using wordTrace_append hprefix tailTrace_7430860
  have hstable : (prefixWord ++ tailWord_7430860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430860).length < 2 ^ (prefixWord ++ tailWord_7430860).sum := by decide
  have hdescent : baseEnd_7430860 < baseStart_7430860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430893 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_7430893 : Nat := 118140960795 + 7430893 * 2 ^ 59
def prefixEnd_7430893 : Nat := 4983230072969 + 3 ^ 40 * 7430893 * 2
def baseEnd_7430893 : Nat := 3815619801130500330663451

theorem tailTrace_7430893 : CollatzResearch.WordTrace tailWord_7430893 prefixEnd_7430893 3815619801130500330663451 := by
  unfold tailWord_7430893
  simp only [CollatzResearch.WordTrace]
  refine ⟨271026933468151231331657333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180684622312100820887771555 271026933468151231331657333)
  ·
    refine ⟨25408775012639177937342875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271026933468151231331657333 25408775012639177937342875)
    ·
      refine ⟨38113162518958766906014313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25408775012639177937342875 38113162518958766906014313)
      ·
        refine ⟨28584871889219075179510735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38113162518958766906014313 28584871889219075179510735)
        ·
          refine ⟨42877307833828612769266103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28584871889219075179510735 42877307833828612769266103)
          ·
            refine ⟨64315961750742919153899155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42877307833828612769266103 64315961750742919153899155)
            ·
              refine ⟨96473942626114378730848733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64315961750742919153899155 96473942626114378730848733)
              ·
                refine ⟨36177728484792892024068275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96473942626114378730848733 36177728484792892024068275)
                ·
                  refine ⟨54266592727189338036102413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36177728484792892024068275 54266592727189338036102413)
                  ·
                    refine ⟨20349972272696001763538405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54266592727189338036102413 20349972272696001763538405)
                    ·
                      refine ⟨3815619801130500330663451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20349972272696001763538405 3815619801130500330663451)
                      ·
                        rfl

theorem cell23_7430893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_7430893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430893 prefixEnd_7430893 := by exact prefixLift 7430893
  have htrace : WordTrace (prefixWord ++ tailWord_7430893) baseStart_7430893 baseEnd_7430893 := by
    simpa [prefixWord, tailWord_7430893, baseEnd_7430893] using wordTrace_append hprefix tailTrace_7430893
  have hstable : (prefixWord ++ tailWord_7430893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430893).length < 2 ^ (prefixWord ++ tailWord_7430893).sum := by decide
  have hdescent : baseEnd_7430893 < baseStart_7430893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430906 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_7430906 : Nat := 118140960795 + 7430906 * 2 ^ 59
def prefixEnd_7430906 : Nat := 4983230072969 + 3 ^ 40 * 7430906 * 2
def baseEnd_7430906 : Nat := 3815626476379008779800891

theorem tailTrace_7430906 : CollatzResearch.WordTrace tailWord_7430906 prefixEnd_7430906 3815626476379008779800891 := by
  unfold tailWord_7430906
  simp only [CollatzResearch.WordTrace]
  refine ⟨67756851904276033637970143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180684938411402756367920381 67756851904276033637970143)
  ·
    refine ⟨101635277856414050456955215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67756851904276033637970143 101635277856414050456955215)
    ·
      refine ⟨152452916784621075685432823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101635277856414050456955215 152452916784621075685432823)
      ·
        refine ⟨228679375176931613528149235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152452916784621075685432823 228679375176931613528149235)
        ·
          refine ⟨343019062765397420292223853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228679375176931613528149235 343019062765397420292223853)
          ·
            refine ⟨128632148537024032609583945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343019062765397420292223853 128632148537024032609583945)
            ·
              refine ⟨96474111402768024457187959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128632148537024032609583945 96474111402768024457187959)
              ·
                refine ⟨144711167104152036685781939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96474111402768024457187959 144711167104152036685781939)
                ·
                  refine ⟨217066750656228055028672909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144711167104152036685781939 217066750656228055028672909)
                  ·
                    refine ⟨81400031496085520635752341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217066750656228055028672909 81400031496085520635752341)
                    ·
                      refine ⟨3815626476379008779800891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81400031496085520635752341 3815626476379008779800891)
                      ·
                        rfl

theorem cell23_7430906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_7430906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430906 prefixEnd_7430906 := by exact prefixLift 7430906
  have htrace : WordTrace (prefixWord ++ tailWord_7430906) baseStart_7430906 baseEnd_7430906 := by
    simpa [prefixWord, tailWord_7430906, baseEnd_7430906] using wordTrace_append hprefix tailTrace_7430906
  have hstable : (prefixWord ++ tailWord_7430906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430906).length < 2 ^ (prefixWord ++ tailWord_7430906).sum := by decide
  have hdescent : baseEnd_7430906 < baseStart_7430906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430910 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_7430910 : Nat := 118140960795 + 7430910 * 2 ^ 59
def prefixEnd_7430910 : Nat := 4983230072969 + 3 ^ 40 * 7430910 * 2
def baseEnd_7430910 : Nat := 3815628530301626764150873

theorem tailTrace_7430910 : CollatzResearch.WordTrace tailWord_7430910 prefixEnd_7430910 3815628530301626764150873 := by
  unfold tailWord_7430910
  simp only [CollatzResearch.WordTrace]
  refine ⟨33878444188636205404378273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180685035672726428823350789 33878444188636205404378273)
  ·
    refine ⟨25408833141477154053283705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33878444188636205404378273 25408833141477154053283705)
    ·
      refine ⟨19056624856107865539962779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25408833141477154053283705 19056624856107865539962779)
      ·
        refine ⟨28584937284161798309944169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19056624856107865539962779 28584937284161798309944169)
        ·
          refine ⟨21438702963121348732458127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28584937284161798309944169 21438702963121348732458127)
          ·
            refine ⟨32158054444682023098687191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21438702963121348732458127 32158054444682023098687191)
            ·
              refine ⟨48237081667023034648030787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32158054444682023098687191 48237081667023034648030787)
              ·
                refine ⟨72355622500534551972046181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48237081667023034648030787 72355622500534551972046181)
                ·
                  refine ⟨13566679218850228494758659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72355622500534551972046181 13566679218850228494758659)
                  ·
                    refine ⟨20350018828275342742137989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13566679218850228494758659 20350018828275342742137989)
                    ·
                      refine ⟨3815628530301626764150873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20350018828275342742137989 3815628530301626764150873)
                      ·
                        rfl

theorem cell23_7430910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_7430910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430910 prefixEnd_7430910 := by exact prefixLift 7430910
  have htrace : WordTrace (prefixWord ++ tailWord_7430910) baseStart_7430910 baseEnd_7430910 := by
    simpa [prefixWord, tailWord_7430910, baseEnd_7430910] using wordTrace_append hprefix tailTrace_7430910
  have hstable : (prefixWord ++ tailWord_7430910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430910).length < 2 ^ (prefixWord ++ tailWord_7430910).sum := by decide
  have hdescent : baseEnd_7430910 < baseStart_7430910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430920 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 3, 4]
def baseStart_7430920 : Nat := 118140960795 + 7430920 * 2 ^ 59
def prefixEnd_7430920 : Nat := 4983230072969 + 3 ^ 40 * 7430920 * 2
def baseEnd_7430920 : Nat := 1271877888369390575008609

theorem tailTrace_7430920 : CollatzResearch.WordTrace tailWord_7430920 prefixEnd_7430920 1271877888369390575008609 := by
  unfold tailWord_7430920
  simp only [CollatzResearch.WordTrace]
  refine ⟨135513959119526707471445107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180685278826035609961926809 135513959119526707471445107)
  ·
    refine ⟨203270938679290061207167661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135513959119526707471445107 203270938679290061207167661)
    ·
      refine ⟨76226602004733772952687873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203270938679290061207167661 76226602004733772952687873)
      ·
        refine ⟨57169951503550329714515905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76226602004733772952687873 57169951503550329714515905)
        ·
          refine ⟨42877463627662747285886929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57169951503550329714515905 42877463627662747285886929)
          ·
            refine ⟨32158097720747060464415197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42877463627662747285886929 32158097720747060464415197)
            ·
              refine ⟨12059286645280147674155699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32158097720747060464415197 12059286645280147674155699)
              ·
                refine ⟨18088929967920221511233549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12059286645280147674155699 18088929967920221511233549)
                ·
                  refine ⟨6783348737970083066712581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18088929967920221511233549 6783348737970083066712581)
                  ·
                    refine ⟨1271877888369390575008609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6783348737970083066712581 1271877888369390575008609)
                    ·
                      rfl

theorem cell23_7430920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_7430920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430920 prefixEnd_7430920 := by exact prefixLift 7430920
  have htrace : WordTrace (prefixWord ++ tailWord_7430920) baseStart_7430920 baseEnd_7430920 := by
    simpa [prefixWord, tailWord_7430920, baseEnd_7430920] using wordTrace_append hprefix tailTrace_7430920
  have hstable : (prefixWord ++ tailWord_7430920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430920).length < 2 ^ (prefixWord ++ tailWord_7430920).sum := by decide
  have hdescent : baseEnd_7430920 < baseStart_7430920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7430933 : List Nat := [1, 3, 2, 1, 2, 2, 3, 3, 6]
def baseStart_7430933 : Nat := 118140960795 + 7430933 * 2 ^ 59
def prefixEnd_7430933 : Nat := 4983230072969 + 3 ^ 40 * 7430933 * 2
def baseEnd_7430933 : Nat := 423960037817408908240363

theorem tailTrace_7430933 : CollatzResearch.WordTrace tailWord_7430933 prefixEnd_7430933 423960037817408908240363 := by
  unfold tailWord_7430933
  simp only [CollatzResearch.WordTrace]
  refine ⟨271028392388006318163113453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180685594925337545442075635 271028392388006318163113453)
  ·
    refine ⟨101635647145502369311167545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271028392388006318163113453 101635647145502369311167545)
    ·
      refine ⟨76226735359126776983375659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101635647145502369311167545 76226735359126776983375659)
      ·
        refine ⟨114340103038690165475063489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76226735359126776983375659 114340103038690165475063489)
        ·
          refine ⟨85755077279017624106297617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114340103038690165475063489 85755077279017624106297617)
          ·
            refine ⟨64316307959263218079723213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85755077279017624106297617 64316307959263218079723213)
            ·
              refine ⟨24118615484723706779896205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64316307959263218079723213 24118615484723706779896205)
              ·
                refine ⟨9044480806771390042461077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24118615484723706779896205 9044480806771390042461077)
                ·
                  refine ⟨423960037817408908240363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9044480806771390042461077 423960037817408908240363)
                  ·
                    rfl

theorem cell23_7430933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 6].length) (baseStart_7430933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7430933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7430933 prefixEnd_7430933 := by exact prefixLift 7430933
  have htrace : WordTrace (prefixWord ++ tailWord_7430933) baseStart_7430933 baseEnd_7430933 := by
    simpa [prefixWord, tailWord_7430933, baseEnd_7430933] using wordTrace_append hprefix tailTrace_7430933
  have hstable : (prefixWord ++ tailWord_7430933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7430933).length < 2 ^ (prefixWord ++ tailWord_7430933).sum := by decide
  have hdescent : baseEnd_7430933 < baseStart_7430933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7430933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431004 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_7431004 : Nat := 118140960795 + 7431004 * 2 ^ 59
def prefixEnd_7431004 : Nat := 4983230072969 + 3 ^ 40 * 7431004 * 2
def baseEnd_7431004 : Nat := 3815676797483149396375441

theorem tailTrace_7431004 : CollatzResearch.WordTrace tailWord_7431004 prefixEnd_7431004 3815676797483149396375441 := by
  unfold tailWord_7431004
  simp only [CollatzResearch.WordTrace]
  refine ⟨135515490985374548644474033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180687321313832731525965377 135515490985374548644474033)
  ·
    refine ⟨101636618239030911483355525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135515490985374548644474033 101636618239030911483355525)
    ·
      refine ⟨19056865919818295903129161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101636618239030911483355525 19056865919818295903129161)
      ·
        refine ⟨14292649439863721927346871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19056865919818295903129161 14292649439863721927346871)
        ·
          refine ⟨21438974159795582891020307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14292649439863721927346871 21438974159795582891020307)
          ·
            refine ⟨32158461239693374336530461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21438974159795582891020307 32158461239693374336530461)
            ·
              refine ⟨12059422964885015376198923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32158461239693374336530461 12059422964885015376198923)
              ·
                refine ⟨18089134447327523064298385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12059422964885015376198923 18089134447327523064298385)
                ·
                  refine ⟨13566850835495642298223789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18089134447327523064298385 13566850835495642298223789)
                  ·
                    refine ⟨5087569063310865861833921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13566850835495642298223789 5087569063310865861833921)
                    ·
                      refine ⟨3815676797483149396375441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087569063310865861833921 3815676797483149396375441)
                      ·
                        rfl

theorem cell23_7431004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_7431004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431004 prefixEnd_7431004 := by exact prefixLift 7431004
  have htrace : WordTrace (prefixWord ++ tailWord_7431004) baseStart_7431004 baseEnd_7431004 := by
    simpa [prefixWord, tailWord_7431004, baseEnd_7431004] using wordTrace_append hprefix tailTrace_7431004
  have hstable : (prefixWord ++ tailWord_7431004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431004).length < 2 ^ (prefixWord ++ tailWord_7431004).sum := by decide
  have hdescent : baseEnd_7431004 < baseStart_7431004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431047 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 1, 2, 4]
def baseStart_7431047 : Nat := 118140960795 + 7431047 * 2 ^ 59
def prefixEnd_7431047 : Nat := 4983230072969 + 3 ^ 40 * 7431047 * 2
def baseEnd_7431047 : Nat := 3815698877151292728137743

theorem tailTrace_7431047 : CollatzResearch.WordTrace tailWord_7431047 prefixEnd_7431047 3815698877151292728137743 := by
  unfold tailWord_7431047
  simp only [CollatzResearch.WordTrace]
  refine ⟨271032550309593315632763395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180688366873062210421842263 271032550309593315632763395)
  ·
    refine ⟨406548825464389973449145093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271032550309593315632763395 406548825464389973449145093)
    ·
      refine ⟨76227904774573120021714705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 406548825464389973449145093 76227904774573120021714705)
      ·
        refine ⟨57170928580929840016286029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76227904774573120021714705 57170928580929840016286029)
        ·
          refine ⟨21439098217848690006107261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57170928580929840016286029 21439098217848690006107261)
          ·
            refine ⟨8039661831693258752290223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21439098217848690006107261 8039661831693258752290223)
            ·
              refine ⟨12059492747539888128435335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8039661831693258752290223 12059492747539888128435335)
              ·
                refine ⟨18089239121309832192653003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12059492747539888128435335 18089239121309832192653003)
                ·
                  refine ⟨27133858681964748288979505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18089239121309832192653003 27133858681964748288979505)
                  ·
                    refine ⟨20350394011473561216734629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27133858681964748288979505 20350394011473561216734629)
                    ·
                      refine ⟨3815698877151292728137743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20350394011473561216734629 3815698877151292728137743)
                      ·
                        rfl

theorem cell23_7431047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_7431047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431047 prefixEnd_7431047 := by exact prefixLift 7431047
  have htrace : WordTrace (prefixWord ++ tailWord_7431047) baseStart_7431047 baseEnd_7431047 := by
    simpa [prefixWord, tailWord_7431047, baseEnd_7431047] using wordTrace_append hprefix tailTrace_7431047
  have hstable : (prefixWord ++ tailWord_7431047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431047).length < 2 ^ (prefixWord ++ tailWord_7431047).sum := by decide
  have hdescent : baseEnd_7431047 < baseStart_7431047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431063 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_7431063 : Nat := 118140960795 + 7431063 * 2 ^ 59
def prefixEnd_7431063 : Nat := 4983230072969 + 3 ^ 40 * 7431063 * 2
def baseEnd_7431063 : Nat := 3815707092841764665537669

theorem tailTrace_7431063 : CollatzResearch.WordTrace tailWord_7431063 prefixEnd_7431063 3815707092841764665537669 := by
  unfold tailWord_7431063
  simp only [CollatzResearch.WordTrace]
  refine ⟨271033133877535350365345843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180688755918356900243563895 271033133877535350365345843)
  ·
    refine ⟨406549700816303025548018765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271033133877535350365345843 406549700816303025548018765)
    ·
      refine ⟨152456137806113634580507037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406549700816303025548018765 152456137806113634580507037)
      ·
        refine ⟨57171051677292612967690139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152456137806113634580507037 57171051677292612967690139)
        ·
          refine ⟨85756577515938919451535209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57171051677292612967690139 85756577515938919451535209)
          ·
            refine ⟨64317433136954189588651407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85756577515938919451535209 64317433136954189588651407)
            ·
              refine ⟨96476149705431284382977111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64317433136954189588651407 96476149705431284382977111)
              ·
                refine ⟨144714224558146926574465667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96476149705431284382977111 144714224558146926574465667)
                ·
                  refine ⟨217071336837220389861698501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144714224558146926574465667 217071336837220389861698501)
                  ·
                    refine ⟨40700875656978823099068469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217071336837220389861698501 40700875656978823099068469)
                    ·
                      refine ⟨3815707092841764665537669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40700875656978823099068469 3815707092841764665537669)
                      ·
                        rfl

theorem cell23_7431063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_7431063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431063 prefixEnd_7431063 := by exact prefixLift 7431063
  have htrace : WordTrace (prefixWord ++ tailWord_7431063) baseStart_7431063 baseEnd_7431063 := by
    simpa [prefixWord, tailWord_7431063, baseEnd_7431063] using wordTrace_append hprefix tailTrace_7431063
  have hstable : (prefixWord ++ tailWord_7431063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431063).length < 2 ^ (prefixWord ++ tailWord_7431063).sum := by decide
  have hdescent : baseEnd_7431063 < baseStart_7431063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431085 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_7431085 : Nat := 118140960795 + 7431085 * 2 ^ 59
def prefixEnd_7431085 : Nat := 4983230072969 + 3 ^ 40 * 7431085 * 2
def baseEnd_7431085 : Nat := 3815718389416163579462569

theorem tailTrace_7431085 : CollatzResearch.WordTrace tailWord_7431085 prefixEnd_7431085 3815718389416163579462569 := by
  unfold tailWord_7431085
  simp only [CollatzResearch.WordTrace]
  refine ⟨271033936283455648122646709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180689290855637098748431139 271033936283455648122646709)
  ·
    refine ⟨25409431526573967011498129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271033936283455648122646709 25409431526573967011498129)
    ·
      refine ⟨19057073644930475258623597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25409431526573967011498129 19057073644930475258623597)
      ·
        refine ⟨7146402616848928221983849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19057073644930475258623597 7146402616848928221983849)
        ·
          refine ⟨5359801962636696166487887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7146402616848928221983849 5359801962636696166487887)
          ·
            refine ⟨8039702943955044249731831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5359801962636696166487887 8039702943955044249731831)
            ·
              refine ⟨12059554415932566374597747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8039702943955044249731831 12059554415932566374597747)
              ·
                refine ⟨18089331623898849561896621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12059554415932566374597747 18089331623898849561896621)
                ·
                  refine ⟨6783499358962068585711233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18089331623898849561896621 6783499358962068585711233)
                  ·
                    refine ⟨5087624519221551439283425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6783499358962068585711233 5087624519221551439283425)
                    ·
                      refine ⟨3815718389416163579462569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087624519221551439283425 3815718389416163579462569)
                      ·
                        rfl

theorem cell23_7431085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_7431085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431085 prefixEnd_7431085 := by exact prefixLift 7431085
  have htrace : WordTrace (prefixWord ++ tailWord_7431085) baseStart_7431085 baseEnd_7431085 := by
    simpa [prefixWord, tailWord_7431085, baseEnd_7431085] using wordTrace_append hprefix tailTrace_7431085
  have hstable : (prefixWord ++ tailWord_7431085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431085).length < 2 ^ (prefixWord ++ tailWord_7431085).sum := by decide
  have hdescent : baseEnd_7431085 < baseStart_7431085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431124 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_7431124 : Nat := 118140960795 + 7431124 * 2 ^ 59
def prefixEnd_7431124 : Nat := 4983230072969 + 3 ^ 40 * 7431124 * 2
def baseEnd_7431124 : Nat := 3815738415161688926874889

theorem tailTrace_7431124 : CollatzResearch.WordTrace tailWord_7431124 prefixEnd_7431124 3815738415161688926874889 := by
  unfold tailWord_7431124
  simp only [CollatzResearch.WordTrace]
  refine ⟨135517679365157178891658213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180690239153542905188877617 135517679365157178891658213)
  ·
    refine ⟨25409564880966971042185915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135517679365157178891658213 25409564880966971042185915)
    ·
      refine ⟨38114347321450456563278873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25409564880966971042185915 38114347321450456563278873)
      ·
        refine ⟨28585760491087842422459155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38114347321450456563278873 28585760491087842422459155)
        ·
          refine ⟨42878640736631763633688733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28585760491087842422459155 42878640736631763633688733)
          ·
            refine ⟨16079490276236911362633275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42878640736631763633688733 16079490276236911362633275)
            ·
              refine ⟨24119235414355367043949913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16079490276236911362633275 24119235414355367043949913)
              ·
                refine ⟨18089426560766525282962435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24119235414355367043949913 18089426560766525282962435)
                ·
                  refine ⟨27134139841149787924443653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18089426560766525282962435 27134139841149787924443653)
                  ·
                    refine ⟨5087651220215585235833185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27134139841149787924443653 5087651220215585235833185)
                    ·
                      refine ⟨3815738415161688926874889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087651220215585235833185 3815738415161688926874889)
                      ·
                        rfl

theorem cell23_7431124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_7431124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431124 prefixEnd_7431124 := by exact prefixLift 7431124
  have htrace : WordTrace (prefixWord ++ tailWord_7431124) baseStart_7431124 baseEnd_7431124 := by
    simpa [prefixWord, tailWord_7431124, baseEnd_7431124] using wordTrace_append hprefix tailTrace_7431124
  have hstable : (prefixWord ++ tailWord_7431124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431124).length < 2 ^ (prefixWord ++ tailWord_7431124).sum := by decide
  have hdescent : baseEnd_7431124 < baseStart_7431124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431154 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 2, 2, 4]
def baseStart_7431154 : Nat := 118140960795 + 7431154 * 2 ^ 59
def prefixEnd_7431154 : Nat := 4983230072969 + 3 ^ 40 * 7431154 * 2
def baseEnd_7431154 : Nat := 3815753819581323809499751

theorem tailTrace_7431154 : CollatzResearch.WordTrace tailWord_7431154 prefixEnd_7431154 3815753819581323809499751 := by
  unfold tailWord_7431154
  simp only [CollatzResearch.WordTrace]
  refine ⟨67759113230051418226727129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180690968613470448604605677 67759113230051418226727129)
  ·
    refine ⟨50819334922538563670045347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67759113230051418226727129 50819334922538563670045347)
    ·
      refine ⟨76229002383807845505068021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50819334922538563670045347 76229002383807845505068021)
      ·
        refine ⟨7146468973481985516100127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76229002383807845505068021 7146468973481985516100127)
        ·
          refine ⟨10719703460222978274150191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7146468973481985516100127 10719703460222978274150191)
          ·
            refine ⟨16079555190334467411225287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10719703460222978274150191 16079555190334467411225287)
            ·
              refine ⟨24119332785501701116837931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16079555190334467411225287 24119332785501701116837931)
              ·
                refine ⟨36178999178252551675256897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24119332785501701116837931 36178999178252551675256897)
                ·
                  refine ⟨27134249383689413756442673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36178999178252551675256897 27134249383689413756442673)
                  ·
                    refine ⟨20350687037767060317332005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27134249383689413756442673 20350687037767060317332005)
                    ·
                      refine ⟨3815753819581323809499751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20350687037767060317332005 3815753819581323809499751)
                      ·
                        rfl

theorem cell23_7431154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_7431154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431154 prefixEnd_7431154 := by exact prefixLift 7431154
  have htrace : WordTrace (prefixWord ++ tailWord_7431154) baseStart_7431154 baseEnd_7431154 := by
    simpa [prefixWord, tailWord_7431154, baseEnd_7431154] using wordTrace_append hprefix tailTrace_7431154
  have hstable : (prefixWord ++ tailWord_7431154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431154).length < 2 ^ (prefixWord ++ tailWord_7431154).sum := by decide
  have hdescent : baseEnd_7431154 < baseStart_7431154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431214 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_7431214 : Nat := 118140960795 + 7431214 * 2 ^ 59
def prefixEnd_7431214 : Nat := 4983230072969 + 3 ^ 40 * 7431214 * 2
def baseEnd_7431214 : Nat := 3815784628420593574749475

theorem tailTrace_7431214 : CollatzResearch.WordTrace tailWord_7431214 prefixEnd_7431214 3815784628420593574749475 := by
  unfold tailWord_7431214
  simp only [CollatzResearch.WordTrace]
  refine ⟨33879830162498537894261587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180692427533325535436061797 33879830162498537894261587)
  ·
    refine ⟨50819745243747806841392381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33879830162498537894261587 50819745243747806841392381)
    ·
      refine ⟨19057404466405427565522143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50819745243747806841392381 19057404466405427565522143)
      ·
        refine ⟨28586106699608141348283215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19057404466405427565522143 28586106699608141348283215)
        ·
          refine ⟨42879160049412212022424823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28586106699608141348283215 42879160049412212022424823)
          ·
            refine ⟨64318740074118318033637235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42879160049412212022424823 64318740074118318033637235)
            ·
              refine ⟨96478110111177477050455853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64318740074118318033637235 96478110111177477050455853)
              ·
                refine ⟨36179291291691553893920945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96478110111177477050455853 36179291291691553893920945)
                ·
                  refine ⟨27134468468768665420440709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36179291291691553893920945 27134468468768665420440709)
                  ·
                    refine ⟨5087712837894124766332633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27134468468768665420440709 5087712837894124766332633)
                    ·
                      refine ⟨3815784628420593574749475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087712837894124766332633 3815784628420593574749475)
                      ·
                        rfl

theorem cell23_7431214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_7431214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431214 prefixEnd_7431214 := by exact prefixLift 7431214
  have htrace : WordTrace (prefixWord ++ tailWord_7431214) baseStart_7431214 baseEnd_7431214 := by
    simpa [prefixWord, tailWord_7431214, baseEnd_7431214] using wordTrace_append hprefix tailTrace_7431214
  have hstable : (prefixWord ++ tailWord_7431214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431214).length < 2 ^ (prefixWord ++ tailWord_7431214).sum := by decide
  have hdescent : baseEnd_7431214 < baseStart_7431214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431257 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 3, 5, 2]
def baseStart_7431257 : Nat := 118140960795 + 7431257 * 2 ^ 59
def prefixEnd_7431257 : Nat := 4983230072969 + 3 ^ 40 * 7431257 * 2
def baseEnd_7431257 : Nat := 3815806708088736906511777

theorem tailTrace_7431257 : CollatzResearch.WordTrace tailWord_7431257 prefixEnd_7431257 3815806708088736906511777 := by
  unfold tailWord_7431257
  simp only [CollatzResearch.WordTrace]
  refine ⟨271040209638832521497908025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180693473092555014331938683 271040209638832521497908025)
  ·
    refine ⟨203280157229124391123431019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271040209638832521497908025 203280157229124391123431019)
    ·
      refine ⟨304920235843686586685146529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203280157229124391123431019 304920235843686586685146529)
      ·
        refine ⟨228690176882764940013859897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304920235843686586685146529 228690176882764940013859897)
        ·
          refine ⟨171517632662073705010394923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228690176882764940013859897 171517632662073705010394923)
          ·
            refine ⟨257276448993110557515592385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171517632662073705010394923 257276448993110557515592385)
            ·
              refine ⟨192957336744832918136694289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257276448993110557515592385 192957336744832918136694289)
              ·
                refine ⟨144718002558624688602520717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192957336744832918136694289 144718002558624688602520717)
                ·
                  refine ⟨54269250959484258225945269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144718002558624688602520717 54269250959484258225945269)
                  ·
                    refine ⟨5087742277451649208682369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54269250959484258225945269 5087742277451649208682369)
                    ·
                      refine ⟨3815806708088736906511777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087742277451649208682369 3815806708088736906511777)
                      ·
                        rfl

theorem cell23_7431257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 5, 2].length) (baseStart_7431257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431257 prefixEnd_7431257 := by exact prefixLift 7431257
  have htrace : WordTrace (prefixWord ++ tailWord_7431257) baseStart_7431257 baseEnd_7431257 := by
    simpa [prefixWord, tailWord_7431257, baseEnd_7431257] using wordTrace_append hprefix tailTrace_7431257
  have hstable : (prefixWord ++ tailWord_7431257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431257).length < 2 ^ (prefixWord ++ tailWord_7431257).sum := by decide
  have hdescent : baseEnd_7431257 < baseStart_7431257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431287 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 4]
def baseStart_7431287 : Nat := 118140960795 + 7431287 * 2 ^ 59
def prefixEnd_7431287 : Nat := 4983230072969 + 3 ^ 40 * 7431287 * 2
def baseEnd_7431287 : Nat := 3815822112508371789136639

theorem tailTrace_7431287 : CollatzResearch.WordTrace tailWord_7431287 prefixEnd_7431287 3815822112508371789136639 := by
  unfold tailWord_7431287
  simp only [CollatzResearch.WordTrace]
  refine ⟨271041303828723836621500115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180694202552482557747666743 271041303828723836621500115)
  ·
    refine ⟨406561955743085754932250173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271041303828723836621500115 406561955743085754932250173)
    ·
      refine ⟨152460733403657158099593815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406561955743085754932250173 152460733403657158099593815)
      ·
        refine ⟨228691100105485737149390723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152460733403657158099593815 228691100105485737149390723)
        ·
          refine ⟨343036650158228605724086085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228691100105485737149390723 343036650158228605724086085)
          ·
            refine ⟨64319371904667863573266141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 343036650158228605724086085 64319371904667863573266141)
            ·
              refine ⟨24119764464250448839974803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64319371904667863573266141 24119764464250448839974803)
              ·
                refine ⟨36179646696375673259962205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24119764464250448839974803 36179646696375673259962205)
                ·
                  refine ⟨13567367511140877472485827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36179646696375673259962205 13567367511140877472485827)
                  ·
                    refine ⟨20351051266711316208728741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13567367511140877472485827 20351051266711316208728741)
                    ·
                      refine ⟨3815822112508371789136639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20351051266711316208728741 3815822112508371789136639)
                      ·
                        rfl

theorem cell23_7431287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_7431287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431287 prefixEnd_7431287 := by exact prefixLift 7431287
  have htrace : WordTrace (prefixWord ++ tailWord_7431287) baseStart_7431287 baseEnd_7431287 := by
    simpa [prefixWord, tailWord_7431287, baseEnd_7431287] using wordTrace_append hprefix tailTrace_7431287
  have hstable : (prefixWord ++ tailWord_7431287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431287).length < 2 ^ (prefixWord ++ tailWord_7431287).sum := by decide
  have hdescent : baseEnd_7431287 < baseStart_7431287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431290 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_7431290 : Nat := 118140960795 + 7431290 * 2 ^ 59
def prefixEnd_7431290 : Nat := 4983230072969 + 3 ^ 40 * 7431290 * 2
def baseEnd_7431290 : Nat := 3815823652950335277399125

theorem tailTrace_7431290 : CollatzResearch.WordTrace tailWord_7431290 prefixEnd_7431290 3815823652950335277399125 := by
  unfold tailWord_7431290
  simp only [CollatzResearch.WordTrace]
  refine ⟨67760353311928242033464831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180694275498475312089239549 67760353311928242033464831)
  ·
    refine ⟨101640529967892363050197247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67760353311928242033464831 101640529967892363050197247)
    ·
      refine ⟨152460794951838544575295871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101640529967892363050197247 152460794951838544575295871)
      ·
        refine ⟨228691192427757816862943807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152460794951838544575295871 228691192427757816862943807)
        ·
          refine ⟨343036788641636725294415711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228691192427757816862943807 343036788641636725294415711)
          ·
            refine ⟨514555182962455087941623567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343036788641636725294415711 514555182962455087941623567)
            ·
              refine ⟨771832774443682631912435351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514555182962455087941623567 771832774443682631912435351)
              ·
                refine ⟨1157749161665523947868653027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771832774443682631912435351 1157749161665523947868653027)
                ·
                  refine ⟨1736623742498285921802979541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157749161665523947868653027 1736623742498285921802979541)
                  ·
                    refine ⟨40702118964803576292257333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1736623742498285921802979541 40702118964803576292257333)
                    ·
                      refine ⟨3815823652950335277399125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40702118964803576292257333 3815823652950335277399125)
                      ·
                        rfl

theorem cell23_7431290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_7431290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431290 prefixEnd_7431290 := by exact prefixLift 7431290
  have htrace : WordTrace (prefixWord ++ tailWord_7431290) baseStart_7431290 baseEnd_7431290 := by
    simpa [prefixWord, tailWord_7431290, baseEnd_7431290] using wordTrace_append hprefix tailTrace_7431290
  have hstable : (prefixWord ++ tailWord_7431290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431290).length < 2 ^ (prefixWord ++ tailWord_7431290).sum := by decide
  have hdescent : baseEnd_7431290 < baseStart_7431290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431297 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 3, 6]
def baseStart_7431297 : Nat := 118140960795 + 7431297 * 2 ^ 59
def prefixEnd_7431297 : Nat := 4983230072969 + 3 ^ 40 * 7431297 * 2
def baseEnd_7431297 : Nat := 1271942415771638916670531

theorem tailTrace_7431297 : CollatzResearch.WordTrace tailWord_7431297 prefixEnd_7431297 1271942415771638916670531 := by
  unfold tailWord_7431297
  simp only [CollatzResearch.WordTrace]
  refine ⟨271041668558687608329364145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180694445705791738886242763 271041668558687608329364145)
  ·
    refine ⟨203281251419015706247023109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271041668558687608329364145 203281251419015706247023109)
    ·
      refine ⟨38115234641065444921316833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203281251419015706247023109 38115234641065444921316833)
      ·
        refine ⟨28586425980799083690987625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38115234641065444921316833 28586425980799083690987625)
        ·
          refine ⟨21439819485599312768240719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28586425980799083690987625 21439819485599312768240719)
          ·
            refine ⟨32159729228398969152361079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21439819485599312768240719 32159729228398969152361079)
            ·
              refine ⟨48239593842598453728541619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32159729228398969152361079 48239593842598453728541619)
              ·
                refine ⟨72359390763897680592812429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48239593842598453728541619 72359390763897680592812429)
                ·
                  refine ⟨27134771536461630222304661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72359390763897680592812429 27134771536461630222304661)
                  ·
                    refine ⟨1271942415771638916670531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27134771536461630222304661 1271942415771638916670531)
                    ·
                      rfl

theorem cell23_7431297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_7431297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431297 prefixEnd_7431297 := by exact prefixLift 7431297
  have htrace : WordTrace (prefixWord ++ tailWord_7431297) baseStart_7431297 baseEnd_7431297 := by
    simpa [prefixWord, tailWord_7431297, baseEnd_7431297] using wordTrace_append hprefix tailTrace_7431297
  have hstable : (prefixWord ++ tailWord_7431297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431297).length < 2 ^ (prefixWord ++ tailWord_7431297).sum := by decide
  have hdescent : baseEnd_7431297 < baseStart_7431297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431301 : List Nat := [1, 3, 1, 1, 6, 1, 3, 1, 1, 5]
def baseStart_7431301 : Nat := 118140960795 + 7431301 * 2 ^ 59
def prefixEnd_7431301 : Nat := 4983230072969 + 3 ^ 40 * 7431301 * 2
def baseEnd_7431301 : Nat := 1271943100412511578120525

theorem tailTrace_7431301 : CollatzResearch.WordTrace tailWord_7431301 prefixEnd_7431301 1271943100412511578120525 := by
  unfold tailWord_7431301
  simp only [CollatzResearch.WordTrace]
  refine ⟨271041814450673117012509757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180694542967115411341673171 271041814450673117012509757)
  ·
    refine ⟨101640680419002418879691159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271041814450673117012509757 101640680419002418879691159)
    ·
      refine ⟨152461020628503628319536739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101640680419002418879691159 152461020628503628319536739)
      ·
        refine ⟨228691530942755442479305109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152461020628503628319536739 228691530942755442479305109)
        ·
          refine ⟨10719915512941661366217427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 228691530942755442479305109 10719915512941661366217427)
          ·
            refine ⟨16079873269412492049326141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10719915512941661366217427 16079873269412492049326141)
            ·
              refine ⟨6029952476029684518497303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16079873269412492049326141 6029952476029684518497303)
              ·
                refine ⟨9044928714044526777745955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6029952476029684518497303 9044928714044526777745955)
                ·
                  refine ⟨13567393071066790166618933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9044928714044526777745955 13567393071066790166618933)
                  ·
                    refine ⟨1271943100412511578120525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13567393071066790166618933 1271943100412511578120525)
                    ·
                      rfl

theorem cell23_7431301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_7431301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431301 prefixEnd_7431301 := by exact prefixLift 7431301
  have htrace : WordTrace (prefixWord ++ tailWord_7431301) baseStart_7431301 baseEnd_7431301 := by
    simpa [prefixWord, tailWord_7431301, baseEnd_7431301] using wordTrace_append hprefix tailTrace_7431301
  have hstable : (prefixWord ++ tailWord_7431301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431301).length < 2 ^ (prefixWord ++ tailWord_7431301).sum := by decide
  have hdescent : baseEnd_7431301 < baseStart_7431301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431324 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_7431324 : Nat := 118140960795 + 7431324 * 2 ^ 59
def prefixEnd_7431324 : Nat := 4983230072969 + 3 ^ 40 * 7431324 * 2
def baseEnd_7431324 : Nat := 3815841111292588144373969

theorem tailTrace_7431324 : CollatzResearch.WordTrace tailWord_7431324 prefixEnd_7431324 3815841111292588144373969 := by
  unfold tailWord_7431324
  simp only [CollatzResearch.WordTrace]
  refine ⟨135521326664794895970298513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180695102219726527960398017 135521326664794895970298513)
  ·
    refine ⟨101640994998596171977723885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135521326664794895970298513 101640994998596171977723885)
    ·
      refine ⟨38115373124473564491646457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101640994998596171977723885 38115373124473564491646457)
      ·
        refine ⟨28586529843355173368734843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38115373124473564491646457 28586529843355173368734843)
        ·
          refine ⟨42879794765032760053102265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28586529843355173368734843 42879794765032760053102265)
          ·
            refine ⟨32159846073774570039826699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42879794765032760053102265 32159846073774570039826699)
            ·
              refine ⟨48239769110661855059740049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32159846073774570039826699 48239769110661855059740049)
              ·
                refine ⟨36179826832996391294805037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48239769110661855059740049 36179826832996391294805037)
                ·
                  refine ⟨13567435062373646735551889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36179826832996391294805037 13567435062373646735551889)
                  ·
                    refine ⟨10175576296780235051663917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13567435062373646735551889 10175576296780235051663917)
                    ·
                      refine ⟨3815841111292588144373969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10175576296780235051663917 3815841111292588144373969)
                      ·
                        rfl

theorem cell23_7431324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_7431324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431324 prefixEnd_7431324 := by exact prefixLift 7431324
  have htrace : WordTrace (prefixWord ++ tailWord_7431324) baseStart_7431324 baseEnd_7431324 := by
    simpa [prefixWord, tailWord_7431324, baseEnd_7431324] using wordTrace_append hprefix tailTrace_7431324
  have hstable : (prefixWord ++ tailWord_7431324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431324).length < 2 ^ (prefixWord ++ tailWord_7431324).sum := by decide
  have hdescent : baseEnd_7431324 < baseStart_7431324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431338 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_7431338 : Nat := 118140960795 + 7431338 * 2 ^ 59
def prefixEnd_7431338 : Nat := 4983230072969 + 3 ^ 40 * 7431338 * 2
def baseEnd_7431338 : Nat := 3815848300021751089598905

theorem tailTrace_7431338 : CollatzResearch.WordTrace tailWord_7431338 prefixEnd_7431338 3815848300021751089598905 := by
  unfold tailWord_7431338
  simp only [CollatzResearch.WordTrace]
  refine ⟨67760790987884768082901667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180695442634359381554404445 67760790987884768082901667)
  ·
    refine ⟨101641186481827152124352501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67760790987884768082901667 101641186481827152124352501)
    ·
      refine ⟨9528861232671295511658047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101641186481827152124352501 9528861232671295511658047)
      ·
        refine ⟨14293291849006943267487071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9528861232671295511658047 14293291849006943267487071)
        ·
          refine ⟨21439937773510414901230607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14293291849006943267487071 21439937773510414901230607)
          ·
            refine ⟨32159906660265622351845911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21439937773510414901230607 32159906660265622351845911)
            ·
              refine ⟨48239859990398433527768867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32159906660265622351845911 48239859990398433527768867)
              ·
                refine ⟨72359789985597650291653301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48239859990398433527768867 72359789985597650291653301)
                ·
                  refine ⟨6783730311149779714842497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72359789985597650291653301 6783730311149779714842497)
                  ·
                    refine ⟨5087797733362334786131873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6783730311149779714842497 5087797733362334786131873)
                    ·
                      refine ⟨3815848300021751089598905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087797733362334786131873 3815848300021751089598905)
                      ·
                        rfl

theorem cell23_7431338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_7431338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431338 prefixEnd_7431338 := by exact prefixLift 7431338
  have htrace : WordTrace (prefixWord ++ tailWord_7431338) baseStart_7431338 baseEnd_7431338 := by
    simpa [prefixWord, tailWord_7431338, baseEnd_7431338] using wordTrace_append hprefix tailTrace_7431338
  have hstable : (prefixWord ++ tailWord_7431338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431338).length < 2 ^ (prefixWord ++ tailWord_7431338).sum := by decide
  have hdescent : baseEnd_7431338 < baseStart_7431338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431354 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3]
def baseStart_7431354 : Nat := 118140960795 + 7431354 * 2 ^ 59
def prefixEnd_7431354 : Nat := 4983230072969 + 3 ^ 40 * 7431354 * 2
def baseEnd_7431354 : Nat := 3815856515712223026998831

theorem tailTrace_7431354 : CollatzResearch.WordTrace tailWord_7431354 prefixEnd_7431354 3815856515712223026998831 := by
  unfold tailWord_7431354
  simp only [CollatzResearch.WordTrace]
  refine ⟨67760936879870276766047279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180695831679654071376126077 67760936879870276766047279)
  ·
    refine ⟨101641405319805415149070919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67760936879870276766047279 101641405319805415149070919)
    ·
      refine ⟨152462107979708122723606379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101641405319805415149070919 152462107979708122723606379)
      ·
        refine ⟨228693161969562184085409569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152462107979708122723606379 228693161969562184085409569)
        ·
          refine ⟨171519871477171638064057177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228693161969562184085409569 171519871477171638064057177)
          ·
            refine ⟨128639903607878728548042883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171519871477171638064057177 128639903607878728548042883)
            ·
              refine ⟨192959855411818092822064325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128639903607878728548042883 192959855411818092822064325)
              ·
                refine ⟨36179972889715892404137061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192959855411818092822064325 36179972889715892404137061)
                ·
                  refine ⟨6783744916821729825775699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36179972889715892404137061 6783744916821729825775699)
                  ·
                    refine ⟨10175617375232594738663549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6783744916821729825775699 10175617375232594738663549)
                    ·
                      refine ⟨3815856515712223026998831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10175617375232594738663549 3815856515712223026998831)
                      ·
                        rfl

theorem cell23_7431354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_7431354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431354 prefixEnd_7431354 := by exact prefixLift 7431354
  have htrace : WordTrace (prefixWord ++ tailWord_7431354) baseStart_7431354 baseEnd_7431354 := by
    simpa [prefixWord, tailWord_7431354, baseEnd_7431354] using wordTrace_append hprefix tailTrace_7431354
  have hstable : (prefixWord ++ tailWord_7431354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431354).length < 2 ^ (prefixWord ++ tailWord_7431354).sum := by decide
  have hdescent : baseEnd_7431354 < baseStart_7431354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431358 : List Nat := [4, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_7431358 : Nat := 118140960795 + 7431358 * 2 ^ 59
def prefixEnd_7431358 : Nat := 4983230072969 + 3 ^ 40 * 7431358 * 2
def baseEnd_7431358 : Nat := 3815858569634841011348813

theorem tailTrace_7431358 : CollatzResearch.WordTrace tailWord_7431358 prefixEnd_7431358 3815858569634841011348813 := by
  unfold tailWord_7431358
  simp only [CollatzResearch.WordTrace]
  refine ⟨33880486676433326968416841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180695928940977743831556485 33880486676433326968416841)
  ·
    refine ⟨25410365007324995226312631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33880486676433326968416841 25410365007324995226312631)
    ·
      refine ⟨38115547510987492839468947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25410365007324995226312631 38115547510987492839468947)
      ·
        refine ⟨57173321266481239259203421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38115547510987492839468947 57173321266481239259203421)
        ·
          refine ⟨21439995474930464722201283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57173321266481239259203421 21439995474930464722201283)
          ·
            refine ⟨32159993212395697083301925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21439995474930464722201283 32159993212395697083301925)
            ·
              refine ⟨6029998727324193203119111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32159993212395697083301925 6029998727324193203119111)
              ·
                refine ⟨9044998090986289804678667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6029998727324193203119111 9044998090986289804678667)
                ·
                  refine ⟨13567497136479434707018001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9044998090986289804678667 13567497136479434707018001)
                  ·
                    refine ⟨10175622852359576030263501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13567497136479434707018001 10175622852359576030263501)
                    ·
                      refine ⟨3815858569634841011348813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10175622852359576030263501 3815858569634841011348813)
                      ·
                        rfl

theorem cell23_7431358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_7431358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431358 prefixEnd_7431358 := by exact prefixLift 7431358
  have htrace : WordTrace (prefixWord ++ tailWord_7431358) baseStart_7431358 baseEnd_7431358 := by
    simpa [prefixWord, tailWord_7431358, baseEnd_7431358] using wordTrace_append hprefix tailTrace_7431358
  have hstable : (prefixWord ++ tailWord_7431358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431358).length < 2 ^ (prefixWord ++ tailWord_7431358).sum := by decide
  have hdescent : baseEnd_7431358 < baseStart_7431358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431411 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 4, 2, 2]
def baseStart_7431411 : Nat := 118140960795 + 7431411 * 2 ^ 59
def prefixEnd_7431411 : Nat := 4983230072969 + 3 ^ 40 * 7431411 * 2
def baseEnd_7431411 : Nat := 3815885784109529303986069

theorem tailTrace_7431411 : CollatzResearch.WordTrace tailWord_7431411 prefixEnd_7431411 3815885784109529303986069 := by
  unfold tailWord_7431411
  simp only [CollatzResearch.WordTrace]
  refine ⟨271045826480274605799014087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180697217653516403866009391 271045826480274605799014087)
  ·
    refine ⟨406568739720411908698521131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271045826480274605799014087 406568739720411908698521131)
    ·
      refine ⟨609853109580617863047781697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406568739720411908698521131 609853109580617863047781697)
      ·
        refine ⟨457389832185463397285836273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609853109580617863047781697 457389832185463397285836273)
        ·
          refine ⟨343042374139097547964377205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457389832185463397285836273 343042374139097547964377205)
          ·
            refine ⟨32160222575540395121660363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 343042374139097547964377205 32160222575540395121660363)
            ·
              refine ⟨48240333863310592682490545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32160222575540395121660363 48240333863310592682490545)
              ·
                refine ⟨36180250397482944511867909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48240333863310592682490545 36180250397482944511867909)
                ·
                  refine ⟨6783796949528052095975233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36180250397482944511867909 6783796949528052095975233)
                  ·
                    refine ⟨5087847712146039071981425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6783796949528052095975233 5087847712146039071981425)
                    ·
                      refine ⟨3815885784109529303986069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087847712146039071981425 3815885784109529303986069)
                      ·
                        rfl

theorem cell23_7431411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 2, 2].length) (baseStart_7431411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431411 prefixEnd_7431411 := by exact prefixLift 7431411
  have htrace : WordTrace (prefixWord ++ tailWord_7431411) baseStart_7431411 baseEnd_7431411 := by
    simpa [prefixWord, tailWord_7431411, baseEnd_7431411] using wordTrace_append hprefix tailTrace_7431411
  have hstable : (prefixWord ++ tailWord_7431411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431411).length < 2 ^ (prefixWord ++ tailWord_7431411).sum := by decide
  have hdescent : baseEnd_7431411 < baseStart_7431411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431414 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_7431414 : Nat := 118140960795 + 7431414 * 2 ^ 59
def prefixEnd_7431414 : Nat := 4983230072969 + 3 ^ 40 * 7431414 * 2
def baseEnd_7431414 : Nat := 3815887324551492792248555

theorem tailTrace_7431414 : CollatzResearch.WordTrace tailWord_7431414 prefixEnd_7431414 3815887324551492792248555 := by
  unfold tailWord_7431414
  simp only [CollatzResearch.WordTrace]
  refine ⟨16940370993703983581960831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180697290599509158207582197 16940370993703983581960831)
  ·
    refine ⟨25410556490555975372941247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16940370993703983581960831 25410556490555975372941247)
    ·
      refine ⟨38115834735833963059411871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25410556490555975372941247 38115834735833963059411871)
      ·
        refine ⟨57173752103750944589117807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38115834735833963059411871 57173752103750944589117807)
        ·
          refine ⟨85760628155626416883676711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57173752103750944589117807 85760628155626416883676711)
          ·
            refine ⟨128640942233439625325515067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85760628155626416883676711 128640942233439625325515067)
            ·
              refine ⟨192961413350159437988272601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128640942233439625325515067 192961413350159437988272601)
              ·
                refine ⟨144721060012619578491204451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192961413350159437988272601 144721060012619578491204451)
                ·
                  refine ⟨217081590018929367736806677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144721060012619578491204451 217081590018929367736806677)
                  ·
                    refine ⟨10175699532137314112662813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 217081590018929367736806677 10175699532137314112662813)
                    ·
                      refine ⟨3815887324551492792248555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10175699532137314112662813 3815887324551492792248555)
                      ·
                        rfl

theorem cell23_7431414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_7431414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431414 prefixEnd_7431414 := by exact prefixLift 7431414
  have htrace : WordTrace (prefixWord ++ tailWord_7431414) baseStart_7431414 baseEnd_7431414 := by
    simpa [prefixWord, tailWord_7431414, baseEnd_7431414] using wordTrace_append hprefix tailTrace_7431414
  have hstable : (prefixWord ++ tailWord_7431414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431414).length < 2 ^ (prefixWord ++ tailWord_7431414).sum := by decide
  have hdescent : baseEnd_7431414 < baseStart_7431414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431428 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_7431428 : Nat := 118140960795 + 7431428 * 2 ^ 59
def prefixEnd_7431428 : Nat := 4983230072969 + 3 ^ 40 * 7431428 * 2
def baseEnd_7431428 : Nat := 3815894513280655737473491

theorem tailTrace_7431428 : CollatzResearch.WordTrace tailWord_7431428 prefixEnd_7431428 3815894513280655737473491 := by
  unfold tailWord_7431428
  simp only [CollatzResearch.WordTrace]
  refine ⟨135523223260606508851191469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180697631014142011801588625 135523223260606508851191469)
  ·
    refine ⟨50821208722727440819196801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135523223260606508851191469 50821208722727440819196801)
    ·
      refine ⟨38115906542045580614397601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50821208722727440819196801 38115906542045580614397601)
      ·
        refine ⟨28586929906534185460798201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38115906542045580614397601 28586929906534185460798201)
        ·
          refine ⟨21440197429900639095598651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28586929906534185460798201 21440197429900639095598651)
          ·
            refine ⟨32160296144850958643397977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21440197429900639095598651 32160296144850958643397977)
            ·
              refine ⟨24120222108638218982548483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32160296144850958643397977 24120222108638218982548483)
              ·
                refine ⟨36180333162957328473822725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24120222108638218982548483 36180333162957328473822725)
                ·
                  refine ⟨6783812468054499088841761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36180333162957328473822725 6783812468054499088841761)
                  ·
                    refine ⟨5087859351040874316631321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6783812468054499088841761 5087859351040874316631321)
                    ·
                      refine ⟨3815894513280655737473491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087859351040874316631321 3815894513280655737473491)
                      ·
                        rfl

theorem cell23_7431428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_7431428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431428 prefixEnd_7431428 := by exact prefixLift 7431428
  have htrace : WordTrace (prefixWord ++ tailWord_7431428) baseStart_7431428 baseEnd_7431428 := by
    simpa [prefixWord, tailWord_7431428, baseEnd_7431428] using wordTrace_append hprefix tailTrace_7431428
  have hstable : (prefixWord ++ tailWord_7431428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431428).length < 2 ^ (prefixWord ++ tailWord_7431428).sum := by decide
  have hdescent : baseEnd_7431428 < baseStart_7431428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431457 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_7431457 : Nat := 118140960795 + 7431457 * 2 ^ 59
def prefixEnd_7431457 : Nat := 4983230072969 + 3 ^ 40 * 7431457 * 2
def baseEnd_7431457 : Nat := 3815909404219636124010857

theorem tailTrace_7431457 : CollatzResearch.WordTrace tailWord_7431457 prefixEnd_7431457 3815909404219636124010857 := by
  unfold tailWord_7431457
  simp only [CollatzResearch.WordTrace]
  refine ⟨271047504238107955655188625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180698336158738637103459083 271047504238107955655188625)
  ·
    refine ⟨203285628178580966741391469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271047504238107955655188625 203285628178580966741391469)
    ·
      refine ⟨76232110566967862528021801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203285628178580966741391469 76232110566967862528021801)
      ·
        refine ⟨57174082925225896896016351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76232110566967862528021801 57174082925225896896016351)
        ·
          refine ⟨85761124387838845344024527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57174082925225896896016351 85761124387838845344024527)
          ·
            refine ⟨128641686581758268016036791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85761124387838845344024527 128641686581758268016036791)
            ·
              refine ⟨192962529872637402024055187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128641686581758268016036791 192962529872637402024055187)
              ·
                refine ⟨289443794808956103036082781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192962529872637402024055187 289443794808956103036082781)
                ·
                  refine ⟨108541423053358538638531043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289443794808956103036082781 108541423053358538638531043)
                  ·
                    refine ⟨162812134580037807957796565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108541423053358538638531043 162812134580037807957796565)
                    ·
                      refine ⟨3815909404219636124010857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162812134580037807957796565 3815909404219636124010857)
                      ·
                        rfl

theorem cell23_7431457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_7431457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431457 prefixEnd_7431457 := by exact prefixLift 7431457
  have htrace : WordTrace (prefixWord ++ tailWord_7431457) baseStart_7431457 baseEnd_7431457 := by
    simpa [prefixWord, tailWord_7431457, baseEnd_7431457] using wordTrace_append hprefix tailTrace_7431457
  have hstable : (prefixWord ++ tailWord_7431457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431457).length < 2 ^ (prefixWord ++ tailWord_7431457).sum := by decide
  have hdescent : baseEnd_7431457 < baseStart_7431457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431474 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_7431474 : Nat := 118140960795 + 7431474 * 2 ^ 59
def prefixEnd_7431474 : Nat := 4983230072969 + 3 ^ 40 * 7431474 * 2
def baseEnd_7431474 : Nat := 3815918133390762557498279

theorem tailTrace_7431474 : CollatzResearch.WordTrace tailWord_7431474 prefixEnd_7431474 3815918133390762557498279 := by
  unfold tailWord_7431474
  simp only [CollatzResearch.WordTrace]
  refine ⟨67762031069761591889639369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180698749519364245039038317 67762031069761591889639369)
  ·
    refine ⟨50821523302321193917229527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67762031069761591889639369 50821523302321193917229527)
    ·
      refine ⟨76232284953481790875844291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50821523302321193917229527 76232284953481790875844291)
      ·
        refine ⟨114348427430222686313766437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76232284953481790875844291 114348427430222686313766437)
        ·
          refine ⟨21440330143166753683831207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114348427430222686313766437 21440330143166753683831207)
          ·
            refine ⟨32160495214750130525746811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21440330143166753683831207 32160495214750130525746811)
            ·
              refine ⟨48240742822125195788620217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32160495214750130525746811 48240742822125195788620217)
              ·
                refine ⟨36180557116593896841465163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48240742822125195788620217 36180557116593896841465163)
                ·
                  refine ⟨54270835674890845262197745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36180557116593896841465163 54270835674890845262197745)
                  ·
                    refine ⟨40703126756168133946648309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54270835674890845262197745 40703126756168133946648309)
                    ·
                      refine ⟨3815918133390762557498279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40703126756168133946648309 3815918133390762557498279)
                      ·
                        rfl

theorem cell23_7431474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_7431474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431474 prefixEnd_7431474 := by exact prefixLift 7431474
  have htrace : WordTrace (prefixWord ++ tailWord_7431474) baseStart_7431474 baseEnd_7431474 := by
    simpa [prefixWord, tailWord_7431474, baseEnd_7431474] using wordTrace_append hprefix tailTrace_7431474
  have hstable : (prefixWord ++ tailWord_7431474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431474).length < 2 ^ (prefixWord ++ tailWord_7431474).sum := by decide
  have hdescent : baseEnd_7431474 < baseStart_7431474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431504 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 3]
def baseStart_7431504 : Nat := 118140960795 + 7431504 * 2 ^ 59
def prefixEnd_7431504 : Nat := 4983230072969 + 3 ^ 40 * 7431504 * 2
def baseEnd_7431504 : Nat := 3815933537810397440123141

theorem tailTrace_7431504 : CollatzResearch.WordTrace tailWord_7431504 prefixEnd_7431504 3815933537810397440123141 := by
  unfold tailWord_7431504
  simp only [CollatzResearch.WordTrace]
  refine ⟨135524609234468841341074783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180699478979291788454766377 135524609234468841341074783)
  ·
    refine ⟨203286913851703262011612175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135524609234468841341074783 203286913851703262011612175)
    ·
      refine ⟨304930370777554893017418263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203286913851703262011612175 304930370777554893017418263)
      ·
        refine ⟨457395556166332339526127395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304930370777554893017418263 457395556166332339526127395)
        ·
          refine ⟨686093334249498509289191093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457395556166332339526127395 686093334249498509289191093)
          ·
            refine ⟨64321250085890485245861665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 686093334249498509289191093 64321250085890485245861665)
            ·
              refine ⟨48240937564417863934396249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64321250085890485245861665 48240937564417863934396249)
              ·
                refine ⟨36180703173313397950797187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48240937564417863934396249 36180703173313397950797187)
                ·
                  refine ⟨54271054759970096926195781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36180703173313397950797187 54271054759970096926195781)
                  ·
                    refine ⟨10175822767494393173661709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54271054759970096926195781 10175822767494393173661709)
                    ·
                      refine ⟨3815933537810397440123141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10175822767494393173661709 3815933537810397440123141)
                      ·
                        rfl

theorem cell23_7431504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 3].length) (baseStart_7431504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431504 prefixEnd_7431504 := by exact prefixLift 7431504
  have htrace : WordTrace (prefixWord ++ tailWord_7431504) baseStart_7431504 baseEnd_7431504 := by
    simpa [prefixWord, tailWord_7431504, baseEnd_7431504] using wordTrace_append hprefix tailTrace_7431504
  have hstable : (prefixWord ++ tailWord_7431504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431504).length < 2 ^ (prefixWord ++ tailWord_7431504).sum := by decide
  have hdescent : baseEnd_7431504 < baseStart_7431504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431511 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 3, 4]
def baseStart_7431511 : Nat := 118140960795 + 7431511 * 2 ^ 59
def prefixEnd_7431511 : Nat := 4983230072969 + 3 ^ 40 * 7431511 * 2
def baseEnd_7431511 : Nat := 1271979044058326304245203

theorem tailTrace_7431511 : CollatzResearch.WordTrace tailWord_7431511 prefixEnd_7431511 1271979044058326304245203 := by
  unfold tailWord_7431511
  simp only [CollatzResearch.WordTrace]
  refine ⟨271049473779912322877654387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180699649186608215251769591 271049473779912322877654387)
  ·
    refine ⟨406574210669868484316481581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271049473779912322877654387 406574210669868484316481581)
    ·
      refine ⟨152465329001200681618680593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406574210669868484316481581 152465329001200681618680593)
      ·
        refine ⟨114348996750900511214010445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152465329001200681618680593 114348996750900511214010445)
        ·
          refine ⟨42880873781587691705253917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114348996750900511214010445 42880873781587691705253917)
          ·
            refine ⟨16080327668095384389470219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42880873781587691705253917 16080327668095384389470219)
            ·
              refine ⟨24120491502143076584205329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16080327668095384389470219 24120491502143076584205329)
              ·
                refine ⟨18090368626607307438153997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24120491502143076584205329 18090368626607307438153997)
                ·
                  refine ⟨6783888234977740289307749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18090368626607307438153997 6783888234977740289307749)
                  ·
                    refine ⟨1271979044058326304245203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6783888234977740289307749 1271979044058326304245203)
                    ·
                      rfl

theorem cell23_7431511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_7431511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431511 prefixEnd_7431511 := by exact prefixLift 7431511
  have htrace : WordTrace (prefixWord ++ tailWord_7431511) baseStart_7431511 baseEnd_7431511 := by
    simpa [prefixWord, tailWord_7431511, baseEnd_7431511] using wordTrace_append hprefix tailTrace_7431511
  have hstable : (prefixWord ++ tailWord_7431511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431511).length < 2 ^ (prefixWord ++ tailWord_7431511).sum := by decide
  have hdescent : baseEnd_7431511 < baseStart_7431511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431541 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 8]
def baseStart_7431541 : Nat := 118140960795 + 7431541 * 2 ^ 59
def prefixEnd_7431541 : Nat := 4983230072969 + 3 ^ 40 * 7431541 * 2
def baseEnd_7431541 : Nat := 423994726288290421706719

theorem tailTrace_7431541 : CollatzResearch.WordTrace tailWord_7431541 prefixEnd_7431541 423994726288290421706719 := by
  unfold tailWord_7431541
  simp only [CollatzResearch.WordTrace]
  refine ⟨271050567969803638001246477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180700378646535758667497651 271050567969803638001246477)
  ·
    refine ⟨101643962988676364250467429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271050567969803638001246477 101643962988676364250467429)
    ·
      refine ⟨19058243060376818296962643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101643962988676364250467429 19058243060376818296962643)
      ·
        refine ⟨28587364590565227445443965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19058243060376818296962643 28587364590565227445443965)
        ·
          refine ⟨10720261721461960292041487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28587364590565227445443965 10720261721461960292041487)
          ·
            refine ⟨16080392582192940438062231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10720261721461960292041487 16080392582192940438062231)
            ·
              refine ⟨24120588873289410657093347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16080392582192940438062231 24120588873289410657093347)
              ·
                refine ⟨36180883309934115985640021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24120588873289410657093347 36180883309934115985640021)
                ·
                  refine ⟨423994726288290421706719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36180883309934115985640021 423994726288290421706719)
                  ·
                    rfl

theorem cell23_7431541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 8].length) (baseStart_7431541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431541 prefixEnd_7431541 := by exact prefixLift 7431541
  have htrace : WordTrace (prefixWord ++ tailWord_7431541) baseStart_7431541 baseEnd_7431541 := by
    simpa [prefixWord, tailWord_7431541, baseEnd_7431541] using wordTrace_append hprefix tailTrace_7431541
  have hstable : (prefixWord ++ tailWord_7431541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431541).length < 2 ^ (prefixWord ++ tailWord_7431541).sum := by decide
  have hdescent : baseEnd_7431541 < baseStart_7431541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431578 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2]
def baseStart_7431578 : Nat := 118140960795 + 7431578 * 2 ^ 59
def prefixEnd_7431578 : Nat := 4983230072969 + 3 ^ 40 * 7431578 * 2
def baseEnd_7431578 : Nat := 3815971535378830150597801

theorem tailTrace_7431578 : CollatzResearch.WordTrace tailWord_7431578 prefixEnd_7431578 3815971535378830150597801 := by
  unfold tailWord_7431578
  simp only [CollatzResearch.WordTrace]
  refine ⟨67762979367667398330085847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180701278313779728880228925 67762979367667398330085847)
  ·
    refine ⟨101644469051501097495128771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67762979367667398330085847 101644469051501097495128771)
    ·
      refine ⟨152466703577251646242693157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101644469051501097495128771 152466703577251646242693157)
      ·
        refine ⟨28587506920734683670504967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152466703577251646242693157 28587506920734683670504967)
        ·
          refine ⟨42881260381102025505757451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28587506920734683670504967 42881260381102025505757451)
          ·
            refine ⟨64321890571653038258636177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42881260381102025505757451 64321890571653038258636177)
            ·
              refine ⟨48241417928739778693977133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64321890571653038258636177 48241417928739778693977133)
              ·
                refine ⟨18090531723277417010241425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48241417928739778693977133 18090531723277417010241425)
                ·
                  refine ⟨13567898792458062757681069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18090531723277417010241425 13567898792458062757681069)
                  ·
                    refine ⟨5087962047171773534130401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13567898792458062757681069 5087962047171773534130401)
                    ·
                      refine ⟨3815971535378830150597801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5087962047171773534130401 3815971535378830150597801)
                      ·
                        rfl

theorem cell23_7431578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_7431578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431578 prefixEnd_7431578 := by exact prefixLift 7431578
  have htrace : WordTrace (prefixWord ++ tailWord_7431578) baseStart_7431578 baseEnd_7431578 := by
    simpa [prefixWord, tailWord_7431578, baseEnd_7431578] using wordTrace_append hprefix tailTrace_7431578
  have hstable : (prefixWord ++ tailWord_7431578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431578).length < 2 ^ (prefixWord ++ tailWord_7431578).sum := by decide
  have hdescent : baseEnd_7431578 < baseStart_7431578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431584 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 3, 6]
def baseStart_7431584 : Nat := 118140960795 + 7431584 * 2 ^ 59
def prefixEnd_7431584 : Nat := 4983230072969 + 3 ^ 40 * 7431584 * 2
def baseEnd_7431584 : Nat := 1271991538754252375707591

theorem tailTrace_7431584 : CollatzResearch.WordTrace tailWord_7431584 prefixEnd_7431584 1271991538754252375707591 := by
  unfold tailWord_7431584
  simp only [CollatzResearch.WordTrace]
  refine ⟨135526068154323928172530903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180701424205765237563374537 135526068154323928172530903)
  ·
    refine ⟨203289102231485892258796355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135526068154323928172530903 203289102231485892258796355)
    ·
      refine ⟨304933653347228838388194533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203289102231485892258796355 304933653347228838388194533)
      ·
        refine ⟨57175060002605407197786475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304933653347228838388194533 57175060002605407197786475)
        ·
          refine ⟨85762590003908110796679713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57175060002605407197786475 85762590003908110796679713)
          ·
            refine ⟨64321942502931083097509785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85762590003908110796679713 64321942502931083097509785)
            ·
              refine ⟨48241456877198312323132339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64321942502931083097509785 48241456877198312323132339)
              ·
                refine ⟨72362185315797468484698509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48241456877198312323132339 72362185315797468484698509)
                ·
                  refine ⟨27135819493424050681761941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72362185315797468484698509 27135819493424050681761941)
                  ·
                    refine ⟨1271991538754252375707591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27135819493424050681761941 1271991538754252375707591)
                    ·
                      rfl

theorem cell23_7431584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3, 6].length) (baseStart_7431584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431584 prefixEnd_7431584 := by exact prefixLift 7431584
  have htrace : WordTrace (prefixWord ++ tailWord_7431584) baseStart_7431584 baseEnd_7431584 := by
    simpa [prefixWord, tailWord_7431584, baseEnd_7431584] using wordTrace_append hprefix tailTrace_7431584
  have hstable : (prefixWord ++ tailWord_7431584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431584).length < 2 ^ (prefixWord ++ tailWord_7431584).sum := by decide
  have hdescent : baseEnd_7431584 < baseStart_7431584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431601 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 4, 4]
def baseStart_7431601 : Nat := 118140960795 + 7431601 * 2 ^ 59
def prefixEnd_7431601 : Nat := 4983230072969 + 3 ^ 40 * 7431601 * 2
def baseEnd_7431601 : Nat := 1271994448477961186870065

theorem tailTrace_7431601 : CollatzResearch.WordTrace tailWord_7431601 prefixEnd_7431601 1271994448477961186870065 := by
  unfold tailWord_7431601
  simp only [CollatzResearch.WordTrace]
  refine ⟨271052756349586268248430657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180701837566390845498953771 271052756349586268248430657)
  ·
    refine ⟨203289567262189701186322993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271052756349586268248430657 203289567262189701186322993)
    ·
      refine ⟨152467175446642275889742245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203289567262189701186322993 152467175446642275889742245)
      ·
        refine ⟨28587595396245426729326671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152467175446642275889742245 28587595396245426729326671)
        ·
          refine ⟨42881393094368140093990007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28587595396245426729326671 42881393094368140093990007)
          ·
            refine ⟨64322089641552210140985011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42881393094368140093990007 64322089641552210140985011)
            ·
              refine ⟨96483134462328315211477517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64322089641552210140985011 96483134462328315211477517)
              ·
                refine ⟨36181175423373118204304069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96483134462328315211477517 36181175423373118204304069)
                ·
                  refine ⟨6783970391882459663307013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36181175423373118204304069 6783970391882459663307013)
                  ·
                    refine ⟨1271994448477961186870065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6783970391882459663307013 1271994448477961186870065)
                    ·
                      rfl

theorem cell23_7431601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_7431601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431601 prefixEnd_7431601 := by exact prefixLift 7431601
  have htrace : WordTrace (prefixWord ++ tailWord_7431601) baseStart_7431601 baseEnd_7431601 := by
    simpa [prefixWord, tailWord_7431601, baseEnd_7431601] using wordTrace_append hprefix tailTrace_7431601
  have hstable : (prefixWord ++ tailWord_7431601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431601).length < 2 ^ (prefixWord ++ tailWord_7431601).sum := by decide
  have hdescent : baseEnd_7431601 < baseStart_7431601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431628 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 3, 2, 3]
def baseStart_7431628 : Nat := 118140960795 + 7431628 * 2 ^ 59
def prefixEnd_7431628 : Nat := 4983230072969 + 3 ^ 40 * 7431628 * 2
def baseEnd_7431628 : Nat := 3815997209411554954972571

theorem tailTrace_7431628 : CollatzResearch.WordTrace tailWord_7431628 prefixEnd_7431628 3815997209411554954972571 := by
  unfold tailWord_7431628
  simp only [CollatzResearch.WordTrace]
  refine ⟨135526870560244225929831769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180702494080325634573109025 135526870560244225929831769)
  ·
    refine ⟨101645152920183169447373827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135526870560244225929831769 101645152920183169447373827)
    ·
      refine ⟨152467729380274754171060741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101645152920183169447373827 152467729380274754171060741)
      ·
        refine ⟨28587699258801516407073889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152467729380274754171060741 28587699258801516407073889)
        ·
          refine ⟨21440774444101137305305417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28587699258801516407073889 21440774444101137305305417)
          ·
            refine ⟨16080580833075852978979063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21440774444101137305305417 16080580833075852978979063)
            ·
              refine ⟨24120871249613779468468595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16080580833075852978979063 24120871249613779468468595)
              ·
                refine ⟨36181306874420669202702893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24120871249613779468468595 36181306874420669202702893)
                ·
                  refine ⟨13567990077907750951013585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36181306874420669202702893 13567990077907750951013585)
                  ·
                    refine ⟨10175992558430813213260189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13567990077907750951013585 10175992558430813213260189)
                    ·
                      refine ⟨3815997209411554954972571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10175992558430813213260189 3815997209411554954972571)
                      ·
                        rfl

theorem cell23_7431628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_7431628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431628 prefixEnd_7431628 := by exact prefixLift 7431628
  have htrace : WordTrace (prefixWord ++ tailWord_7431628) baseStart_7431628 baseEnd_7431628 := by
    simpa [prefixWord, tailWord_7431628, baseEnd_7431628] using wordTrace_append hprefix tailTrace_7431628
  have hstable : (prefixWord ++ tailWord_7431628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431628).length < 2 ^ (prefixWord ++ tailWord_7431628).sum := by decide
  have hdescent : baseEnd_7431628 < baseStart_7431628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431638 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_7431638 : Nat := 118140960795 + 7431638 * 2 ^ 59
def prefixEnd_7431638 : Nat := 4983230072969 + 3 ^ 40 * 7431638 * 2
def baseEnd_7431638 : Nat := 3816002344218099915847525

theorem tailTrace_7431638 : CollatzResearch.WordTrace tailWord_7431638 prefixEnd_7431638 3816002344218099915847525 := by
  unfold tailWord_7431638
  simp only [CollatzResearch.WordTrace]
  refine ⟨16940881615653263972970473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180702737233634815711685045 16940881615653263972970473)
  ·
    refine ⟨12705661211739947979727855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16940881615653263972970473 12705661211739947979727855)
    ·
      refine ⟨19058491817609921969591783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12705661211739947979727855 19058491817609921969591783)
      ·
        refine ⟨28587737726414882954387675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19058491817609921969591783 28587737726414882954387675)
        ·
          refine ⟨42881606589622324431581513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28587737726414882954387675 42881606589622324431581513)
          ·
            refine ⟨32161204942216743323686135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42881606589622324431581513 32161204942216743323686135)
            ·
              refine ⟨48241807413325114985529203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32161204942216743323686135 48241807413325114985529203)
              ·
                refine ⟨72362711119987672478293805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48241807413325114985529203 72362711119987672478293805)
                ·
                  refine ⟨27136016669995377179360177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72362711119987672478293805 27136016669995377179360177)
                  ·
                    refine ⟨20352012502496532884520133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27136016669995377179360177 20352012502496532884520133)
                    ·
                      refine ⟨3816002344218099915847525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20352012502496532884520133 3816002344218099915847525)
                      ·
                        rfl

theorem cell23_7431638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_7431638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431638 prefixEnd_7431638 := by exact prefixLift 7431638
  have htrace : WordTrace (prefixWord ++ tailWord_7431638) baseStart_7431638 baseEnd_7431638 := by
    simpa [prefixWord, tailWord_7431638, baseEnd_7431638] using wordTrace_append hprefix tailTrace_7431638
  have hstable : (prefixWord ++ tailWord_7431638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431638).length < 2 ^ (prefixWord ++ tailWord_7431638).sum := by decide
  have hdescent : baseEnd_7431638 < baseStart_7431638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431641 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 3, 3, 3]
def baseStart_7431641 : Nat := 118140960795 + 7431641 * 2 ^ 59
def prefixEnd_7431641 : Nat := 4983230072969 + 3 ^ 40 * 7431641 * 2
def baseEnd_7431641 : Nat := 3816003884660063404110011

theorem tailTrace_7431641 : CollatzResearch.WordTrace tailWord_7431641 prefixEnd_7431641 3816003884660063404110011 := by
  unfold tailWord_7431641
  simp only [CollatzResearch.WordTrace]
  refine ⟨271054215269441355079886777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180702810179627570053257851 271054215269441355079886777)
  ·
    refine ⟨203290661452081016309915083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271054215269441355079886777 203290661452081016309915083)
    ·
      refine ⟨304935992178121524464872625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203290661452081016309915083 304935992178121524464872625)
      ·
        refine ⟨228701994133591143348654469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304935992178121524464872625 228701994133591143348654469)
        ·
          refine ⟨42881623900048339377872713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228701994133591143348654469 42881623900048339377872713)
          ·
            refine ⟨32161217925036254533404535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42881623900048339377872713 32161217925036254533404535)
            ·
              refine ⟨48241826887554381800106803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32161217925036254533404535 48241826887554381800106803)
              ·
                refine ⟨72362740331331572700160205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48241826887554381800106803 72362740331331572700160205)
                ·
                  refine ⟨27136027624249339762560077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72362740331331572700160205 27136027624249339762560077)
                  ·
                    refine ⟨10176010359093502410960029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27136027624249339762560077 10176010359093502410960029)
                    ·
                      refine ⟨3816003884660063404110011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10176010359093502410960029 3816003884660063404110011)
                      ·
                        rfl

theorem cell23_7431641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_7431641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431641 prefixEnd_7431641 := by exact prefixLift 7431641
  have htrace : WordTrace (prefixWord ++ tailWord_7431641) baseStart_7431641 baseEnd_7431641 := by
    simpa [prefixWord, tailWord_7431641, baseEnd_7431641] using wordTrace_append hprefix tailTrace_7431641
  have hstable : (prefixWord ++ tailWord_7431641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431641).length < 2 ^ (prefixWord ++ tailWord_7431641).sum := by decide
  have hdescent : baseEnd_7431641 < baseStart_7431641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431693 : List Nat := [1, 7, 1, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_7431693 : Nat := 118140960795 + 7431693 * 2 ^ 59
def prefixEnd_7431693 : Nat := 4983230072969 + 3 ^ 40 * 7431693 * 2
def baseEnd_7431693 : Nat := 3816030585654097200659773

theorem tailTrace_7431693 : CollatzResearch.WordTrace tailWord_7431693 prefixEnd_7431693 3816030585654097200659773 := by
  unfold tailWord_7431693
  simp only [CollatzResearch.WordTrace]
  refine ⟨271056111865252967960779733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180704074576835311973853155 271056111865252967960779733)
  ·
    refine ⟨6352877621841866436580775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 271056111865252967960779733 6352877621841866436580775)
    ·
      refine ⟨9529316432762799654871163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6352877621841866436580775 9529316432762799654871163)
      ·
        refine ⟨14293974649144199482306745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9529316432762799654871163 14293974649144199482306745)
        ·
          refine ⟨10720480986858149611730059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14293974649144199482306745 10720480986858149611730059)
          ·
            refine ⟨16080721480287224417595089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10720480986858149611730059 16080721480287224417595089)
            ·
              refine ⟨12060541110215418313196317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16080721480287224417595089 12060541110215418313196317)
              ·
                refine ⟨4522702916330781867448619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12060541110215418313196317 4522702916330781867448619)
                ·
                  refine ⟨6784054374496172801172929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4522702916330781867448619 6784054374496172801172929)
                  ·
                    refine ⟨5088040780872129600879697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6784054374496172801172929 5088040780872129600879697)
                    ·
                      refine ⟨3816030585654097200659773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088040780872129600879697 3816030585654097200659773)
                      ·
                        rfl

theorem cell23_7431693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_7431693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431693 prefixEnd_7431693 := by exact prefixLift 7431693
  have htrace : WordTrace (prefixWord ++ tailWord_7431693) baseStart_7431693 baseEnd_7431693 := by
    simpa [prefixWord, tailWord_7431693, baseEnd_7431693] using wordTrace_append hprefix tailTrace_7431693
  have hstable : (prefixWord ++ tailWord_7431693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431693).length < 2 ^ (prefixWord ++ tailWord_7431693).sum := by decide
  have hdescent : baseEnd_7431693 < baseStart_7431693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431711 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 4]
def baseStart_7431711 : Nat := 118140960795 + 7431711 * 2 ^ 59
def prefixEnd_7431711 : Nat := 4983230072969 + 3 ^ 40 * 7431711 * 2
def baseEnd_7431711 : Nat := 3816039828305878130234689

theorem tailTrace_7431711 : CollatzResearch.WordTrace tailWord_7431711 prefixEnd_7431711 3816039828305878130234689 := by
  unfold tailWord_7431711
  simp only [CollatzResearch.WordTrace]
  refine ⟨271056768379187757034934987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180704512252791838023289991 271056768379187757034934987)
  ·
    refine ⟨406585152568781635552402481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271056768379187757034934987 406585152568781635552402481)
    ·
      refine ⟨304938864426586226664301861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406585152568781635552402481 304938864426586226664301861)
      ·
        refine ⟨57176037079984917499556599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304938864426586226664301861 57176037079984917499556599)
        ·
          refine ⟨85764055619977376249334899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57176037079984917499556599 85764055619977376249334899)
          ·
            refine ⟨128646083429966064374002349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85764055619977376249334899 128646083429966064374002349)
            ·
              refine ⟨48242281286237274140250881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128646083429966064374002349 48242281286237274140250881)
              ·
                refine ⟨36181710964677955605188161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48242281286237274140250881 36181710964677955605188161)
                ·
                  refine ⟨27136283223508466703891121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36181710964677955605188161 27136283223508466703891121)
                  ·
                    refine ⟨20352212417631350027918341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27136283223508466703891121 20352212417631350027918341)
                    ·
                      refine ⟨3816039828305878130234689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20352212417631350027918341 3816039828305878130234689)
                      ·
                        rfl

theorem cell23_7431711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_7431711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431711 prefixEnd_7431711 := by exact prefixLift 7431711
  have htrace : WordTrace (prefixWord ++ tailWord_7431711) baseStart_7431711 baseEnd_7431711 := by
    simpa [prefixWord, tailWord_7431711, baseEnd_7431711] using wordTrace_append hprefix tailTrace_7431711
  have hstable : (prefixWord ++ tailWord_7431711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431711).length < 2 ^ (prefixWord ++ tailWord_7431711).sum := by decide
  have hdescent : baseEnd_7431711 < baseStart_7431711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431758 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2]
def baseStart_7431758 : Nat := 118140960795 + 7431758 * 2 ^ 59
def prefixEnd_7431758 : Nat := 4983230072969 + 3 ^ 40 * 7431758 * 2
def baseEnd_7431758 : Nat := 3816063961896639446346973

theorem tailTrace_7431758 : CollatzResearch.WordTrace tailWord_7431758 prefixEnd_7431758 3816063961896639446346973 := by
  unfold tailWord_7431758
  simp only [CollatzResearch.WordTrace]
  refine ⟨33882310326252185507736991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180705655073344989374597285 33882310326252185507736991)
  ·
    refine ⟨50823465489378278261605487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33882310326252185507736991 50823465489378278261605487)
    ·
      refine ⟨76235198234067417392408231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50823465489378278261605487 76235198234067417392408231)
      ·
        refine ⟨114352797351101126088612347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76235198234067417392408231 114352797351101126088612347)
        ·
          refine ⟨171529196026651689132918521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114352797351101126088612347 171529196026651689132918521)
          ·
            refine ⟨128646897019988766849688891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171529196026651689132918521 128646897019988766849688891)
            ·
              refine ⟨192970345529983150274533337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128646897019988766849688891 192970345529983150274533337)
              ·
                refine ⟨144727759147487362705900003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192970345529983150274533337 144727759147487362705900003)
                ·
                  refine ⟨217091638721231044058850005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144727759147487362705900003 217091638721231044058850005)
                  ·
                    refine ⟨5088085282528852595129297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 217091638721231044058850005 5088085282528852595129297)
                    ·
                      refine ⟨3816063961896639446346973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088085282528852595129297 3816063961896639446346973)
                      ·
                        rfl

theorem cell23_7431758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_7431758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431758 prefixEnd_7431758 := by exact prefixLift 7431758
  have htrace : WordTrace (prefixWord ++ tailWord_7431758) baseStart_7431758 baseEnd_7431758 := by
    simpa [prefixWord, tailWord_7431758, baseEnd_7431758] using wordTrace_append hprefix tailTrace_7431758
  have hstable : (prefixWord ++ tailWord_7431758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431758).length < 2 ^ (prefixWord ++ tailWord_7431758).sum := by decide
  have hdescent : baseEnd_7431758 < baseStart_7431758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431761 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_7431761 : Nat := 118140960795 + 7431761 * 2 ^ 59
def prefixEnd_7431761 : Nat := 4983230072969 + 3 ^ 40 * 7431761 * 2
def baseEnd_7431761 : Nat := 3816065502338602934609459

theorem tailTrace_7431761 : CollatzResearch.WordTrace tailWord_7431761 prefixEnd_7431761 3816065502338602934609459 := by
  unfold tailWord_7431761
  simp only [CollatzResearch.WordTrace]
  refine ⟨271058592029006615574255137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180705728019337743716170091 271058592029006615574255137)
  ·
    refine ⟨203293944021754961680691353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271058592029006615574255137 203293944021754961680691353)
    ·
      refine ⟨152470458016316221260518515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203293944021754961680691353 152470458016316221260518515)
      ·
        refine ⟨228705687024474331890777773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152470458016316221260518515 228705687024474331890777773)
        ·
          refine ⟨85764632634177874459041665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228705687024474331890777773 85764632634177874459041665)
          ·
            refine ⟨64323474475633405844281249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85764632634177874459041665 64323474475633405844281249)
            ·
              refine ⟨48242605856725054383210937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64323474475633405844281249 48242605856725054383210937)
              ·
                refine ⟨36181954392543790787408203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48242605856725054383210937 36181954392543790787408203)
                ·
                  refine ⟨54272931588815686181112305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36181954392543790787408203 54272931588815686181112305)
                  ·
                    refine ⟨40704698691611764635834229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54272931588815686181112305 40704698691611764635834229)
                    ·
                      refine ⟨3816065502338602934609459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40704698691611764635834229 3816065502338602934609459)
                      ·
                        rfl

theorem cell23_7431761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_7431761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431761 prefixEnd_7431761 := by exact prefixLift 7431761
  have htrace : WordTrace (prefixWord ++ tailWord_7431761) baseStart_7431761 baseEnd_7431761 := by
    simpa [prefixWord, tailWord_7431761, baseEnd_7431761] using wordTrace_append hprefix tailTrace_7431761
  have hstable : (prefixWord ++ tailWord_7431761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431761).length < 2 ^ (prefixWord ++ tailWord_7431761).sum := by decide
  have hdescent : baseEnd_7431761 < baseStart_7431761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431772 : List Nat := [2, 2, 4, 1, 2, 2, 3, 2, 5]
def baseStart_7431772 : Nat := 118140960795 + 7431772 * 2 ^ 59
def prefixEnd_7431772 : Nat := 4983230072969 + 3 ^ 40 * 7431772 * 2
def baseEnd_7431772 : Nat := 424007905625089154619101

theorem tailTrace_7431772 : CollatzResearch.WordTrace tailWord_7431772 prefixEnd_7431772 424007905625089154619101 := by
  unfold tailWord_7431772
  simp only [CollatzResearch.WordTrace]
  refine ⟨135529496615983382226452785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180705995487977842968603713 135529496615983382226452785)
  ·
    refine ⟨101647122461987536669839589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135529496615983382226452785 101647122461987536669839589)
    ·
      refine ⟨19058835461622663125594923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101647122461987536669839589 19058835461622663125594923)
      ·
        refine ⟨28588253192433994688392385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19058835461622663125594923 28588253192433994688392385)
        ·
          refine ⟨21441189894325496016294289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28588253192433994688392385 21441189894325496016294289)
          ·
            refine ⟨16080892420744122012220717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21441189894325496016294289 16080892420744122012220717)
            ·
              refine ⟨6030334657779045754582769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16080892420744122012220717 6030334657779045754582769)
              ·
                refine ⟨4522750993334284315937077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6030334657779045754582769 4522750993334284315937077)
                ·
                  refine ⟨424007905625089154619101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4522750993334284315937077 424007905625089154619101)
                  ·
                    rfl

theorem cell23_7431772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 5].length) (baseStart_7431772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431772 prefixEnd_7431772 := by exact prefixLift 7431772
  have htrace : WordTrace (prefixWord ++ tailWord_7431772) baseStart_7431772 baseEnd_7431772 := by
    simpa [prefixWord, tailWord_7431772, baseEnd_7431772] using wordTrace_append hprefix tailTrace_7431772
  have hstable : (prefixWord ++ tailWord_7431772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431772).length < 2 ^ (prefixWord ++ tailWord_7431772).sum := by decide
  have hdescent : baseEnd_7431772 < baseStart_7431772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431788 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 1, 6, 2]
def baseStart_7431788 : Nat := 118140960795 + 7431788 * 2 ^ 59
def prefixEnd_7431788 : Nat := 4983230072969 + 3 ^ 40 * 7431788 * 2
def baseEnd_7431788 : Nat := 3816079366316274328971835

theorem tailTrace_7431788 : CollatzResearch.WordTrace tailWord_7431788 prefixEnd_7431788 3816079366316274328971835 := by
  unfold tailWord_7431788
  simp only [CollatzResearch.WordTrace]
  refine ⟨135529788399954399592744009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180706384533272532790325345 135529788399954399592744009)
  ·
    refine ⟨101647341299965799694558007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135529788399954399592744009 101647341299965799694558007)
    ·
      refine ⟨152471011949948699541837011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101647341299965799694558007 152471011949948699541837011)
      ·
        refine ⟨228706517924923049312755517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152471011949948699541837011 228706517924923049312755517)
        ·
          refine ⟨85764944221846143492283319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228706517924923049312755517 85764944221846143492283319)
          ·
            refine ⟨128647416332769215238424979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85764944221846143492283319 128647416332769215238424979)
            ·
              refine ⟨192971124499153822857637469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128647416332769215238424979 192971124499153822857637469)
              ·
                refine ⟨72364171687182683571614051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192971124499153822857637469 72364171687182683571614051)
                ·
                  refine ⟨108546257530774025357421077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72364171687182683571614051 108546257530774025357421077)
                  ·
                    refine ⟨5088105821755032438629113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108546257530774025357421077 5088105821755032438629113)
                    ·
                      refine ⟨3816079366316274328971835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088105821755032438629113 3816079366316274328971835)
                      ·
                        rfl

theorem cell23_7431788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 6, 2].length) (baseStart_7431788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431788 prefixEnd_7431788 := by exact prefixLift 7431788
  have htrace : WordTrace (prefixWord ++ tailWord_7431788) baseStart_7431788 baseEnd_7431788 := by
    simpa [prefixWord, tailWord_7431788, baseEnd_7431788] using wordTrace_append hprefix tailTrace_7431788
  have hstable : (prefixWord ++ tailWord_7431788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431788).length < 2 ^ (prefixWord ++ tailWord_7431788).sum := by decide
  have hdescent : baseEnd_7431788 < baseStart_7431788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431805 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_7431805 : Nat := 118140960795 + 7431805 * 2 ^ 59
def prefixEnd_7431805 : Nat := 4983230072969 + 3 ^ 40 * 7431805 * 2
def baseEnd_7431805 : Nat := 3816088095487400762459257

theorem tailTrace_7431805 : CollatzResearch.WordTrace tailWord_7431805 prefixEnd_7431805 3816088095487400762459257 := by
  unfold tailWord_7431805
  simp only [CollatzResearch.WordTrace]
  refine ⟨271060196840847211088856869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180706797893898140725904579 271060196840847211088856869)
  ·
    refine ⟨50823786907658852079160663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271060196840847211088856869 50823786907658852079160663)
    ·
      refine ⟨76235680361488278118740995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50823786907658852079160663 76235680361488278118740995)
      ·
        refine ⟨114353520542232417178111493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76235680361488278118740995 114353520542232417178111493)
        ·
          refine ⟨21441285101668578220895905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114353520542232417178111493 21441285101668578220895905)
          ·
            refine ⟨16080963826251433665671929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21441285101668578220895905 16080963826251433665671929)
            ·
              refine ⟨12060722869688575249253947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16080963826251433665671929 12060722869688575249253947)
              ·
                refine ⟨18091084304532862873880921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12060722869688575249253947 18091084304532862873880921)
                ·
                  refine ⟨13568313228399647155410691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18091084304532862873880921 13568313228399647155410691)
                  ·
                    refine ⟨20352469842599470733116037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13568313228399647155410691 20352469842599470733116037)
                    ·
                      refine ⟨3816088095487400762459257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20352469842599470733116037 3816088095487400762459257)
                      ·
                        rfl

theorem cell23_7431805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_7431805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431805 prefixEnd_7431805 := by exact prefixLift 7431805
  have htrace : WordTrace (prefixWord ++ tailWord_7431805) baseStart_7431805 baseEnd_7431805 := by
    simpa [prefixWord, tailWord_7431805, baseEnd_7431805] using wordTrace_append hprefix tailTrace_7431805
  have hstable : (prefixWord ++ tailWord_7431805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431805).length < 2 ^ (prefixWord ++ tailWord_7431805).sum := by decide
  have hdescent : baseEnd_7431805 < baseStart_7431805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431832 : List Nat := [2, 1, 2, 4, 1, 3, 1, 4, 1, 4]
def baseStart_7431832 : Nat := 118140960795 + 7431832 * 2 ^ 59
def prefixEnd_7431832 : Nat := 4983230072969 + 3 ^ 40 * 7431832 * 2
def baseEnd_7431832 : Nat := 1272033986488357385607211

theorem tailTrace_7431832 : CollatzResearch.WordTrace tailWord_7431832 prefixEnd_7431832 1272033986488357385607211 := by
  unfold tailWord_7431832
  simp only [CollatzResearch.WordTrace]
  refine ⟨135530590805874697350044875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180707454407832929800059833 135530590805874697350044875)
  ·
    refine ⟨203295886208812046025067313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135530590805874697350044875 203295886208812046025067313)
    ·
      refine ⟨152471914656609034518800485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203295886208812046025067313 152471914656609034518800485)
      ·
        refine ⟨28588483998114193972275091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152471914656609034518800485 28588483998114193972275091)
        ·
          refine ⟨42882725997171290958412637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28588483998114193972275091 42882725997171290958412637)
          ·
            refine ⟨16081022248939234109404739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42882725997171290958412637 16081022248939234109404739)
            ·
              refine ⟨24121533373408851164107109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16081022248939234109404739 24121533373408851164107109)
              ·
                refine ⟨4522787507514159593270083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24121533373408851164107109 4522787507514159593270083)
                ·
                  refine ⟨6784181261271239389905125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4522787507514159593270083 6784181261271239389905125)
                  ·
                    refine ⟨1272033986488357385607211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6784181261271239389905125 1272033986488357385607211)
                    ·
                      rfl

theorem cell23_7431832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_7431832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431832 prefixEnd_7431832 := by exact prefixLift 7431832
  have htrace : WordTrace (prefixWord ++ tailWord_7431832) baseStart_7431832 baseEnd_7431832 := by
    simpa [prefixWord, tailWord_7431832, baseEnd_7431832] using wordTrace_append hprefix tailTrace_7431832
  have hstable : (prefixWord ++ tailWord_7431832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431832).length < 2 ^ (prefixWord ++ tailWord_7431832).sum := by decide
  have hdescent : baseEnd_7431832 < baseStart_7431832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431855 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 3, 1, 3]
def baseStart_7431855 : Nat := 118140960795 + 7431855 * 2 ^ 59
def prefixEnd_7431855 : Nat := 4983230072969 + 3 ^ 40 * 7431855 * 2
def baseEnd_7431855 : Nat := 3816113769520125566834027

theorem tailTrace_7431855 : CollatzResearch.WordTrace tailWord_7431855 prefixEnd_7431855 3816113769520125566834027 := by
  unfold tailWord_7431855
  simp only [CollatzResearch.WordTrace]
  refine ⟨271062020490666069628177019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180708013660444046418784679 271062020490666069628177019)
  ·
    refine ⟨406593030735999104442265529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271062020490666069628177019 406593030735999104442265529)
    ·
      refine ⟨304944773051999328331699147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406593030735999104442265529 304944773051999328331699147)
      ·
        refine ⟨457417159577998992497548721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304944773051999328331699147 457417159577998992497548721)
        ·
          refine ⟨343062869683499244373161541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457417159577998992497548721 343062869683499244373161541)
          ·
            refine ⟨64324288065656108319967789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 343062869683499244373161541 64324288065656108319967789)
            ·
              refine ⟨24121608024621040619987921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64324288065656108319967789 24121608024621040619987921)
              ·
                refine ⟨18091206018465780464990941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24121608024621040619987921 18091206018465780464990941)
                ·
                  refine ⟨6784202256924667674371603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18091206018465780464990941 6784202256924667674371603)
                  ·
                    refine ⟨10176303385387001511557405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6784202256924667674371603 10176303385387001511557405)
                    ·
                      refine ⟨3816113769520125566834027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10176303385387001511557405 3816113769520125566834027)
                      ·
                        rfl

theorem cell23_7431855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 1, 3].length) (baseStart_7431855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431855 prefixEnd_7431855 := by exact prefixLift 7431855
  have htrace : WordTrace (prefixWord ++ tailWord_7431855) baseStart_7431855 baseEnd_7431855 := by
    simpa [prefixWord, tailWord_7431855, baseEnd_7431855] using wordTrace_append hprefix tailTrace_7431855
  have hstable : (prefixWord ++ tailWord_7431855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431855).length < 2 ^ (prefixWord ++ tailWord_7431855).sum := by decide
  have hdescent : baseEnd_7431855 < baseStart_7431855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431858 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_7431858 : Nat := 118140960795 + 7431858 * 2 ^ 59
def prefixEnd_7431858 : Nat := 4983230072969 + 3 ^ 40 * 7431858 * 2
def baseEnd_7431858 : Nat := 1272038436654029685032171

theorem tailTrace_7431858 : CollatzResearch.WordTrace tailWord_7431858 prefixEnd_7431858 1272038436654029685032171 := by
  unfold tailWord_7431858
  simp only [CollatzResearch.WordTrace]
  refine ⟨67765532477413800285134057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180708086606436800760357485 67765532477413800285134057)
  ·
    refine ⟨50824149358060350213850543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67765532477413800285134057 50824149358060350213850543)
    ·
      refine ⟨76236224037090525320775815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50824149358060350213850543 76236224037090525320775815)
      ·
        refine ⟨114354336055635787981163723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76236224037090525320775815 114354336055635787981163723)
        ·
          refine ⟨171531504083453681971745585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114354336055635787981163723 171531504083453681971745585)
          ·
            refine ⟨128648628062590261478809189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171531504083453681971745585 128648628062590261478809189)
            ·
              refine ⟨24121617761735674027276723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128648628062590261478809189 24121617761735674027276723)
              ·
                refine ⟨36182426642603511040915085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24121617761735674027276723 36182426642603511040915085)
                ·
                  refine ⟨13568409990976316640343157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36182426642603511040915085 13568409990976316640343157)
                  ·
                    refine ⟨1272038436654029685032171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13568409990976316640343157 1272038436654029685032171)
                    ·
                      rfl

theorem cell23_7431858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_7431858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431858 prefixEnd_7431858 := by exact prefixLift 7431858
  have htrace : WordTrace (prefixWord ++ tailWord_7431858) baseStart_7431858 baseEnd_7431858 := by
    simpa [prefixWord, tailWord_7431858, baseEnd_7431858] using wordTrace_append hprefix tailTrace_7431858
  have hstable : (prefixWord ++ tailWord_7431858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431858).length < 2 ^ (prefixWord ++ tailWord_7431858).sum := by decide
  have hdescent : baseEnd_7431858 < baseStart_7431858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431891 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 6]
def baseStart_7431891 : Nat := 118140960795 + 7431891 * 2 ^ 59
def prefixEnd_7431891 : Nat := 4983230072969 + 3 ^ 40 * 7431891 * 2
def baseEnd_7431891 : Nat := 3816132254823687425983861

theorem tailTrace_7431891 : CollatzResearch.WordTrace tailWord_7431891 prefixEnd_7431891 3816132254823687425983861 := by
  unfold tailWord_7431891
  simp only [CollatzResearch.WordTrace]
  refine ⟨271063333518535647776487527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180708889012357098517658351 271063333518535647776487527)
  ·
    refine ⟨406595000277803471664731291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271063333518535647776487527 406595000277803471664731291)
    ·
      refine ⟨609892500416705207497096937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406595000277803471664731291 609892500416705207497096937)
      ·
        refine ⟨457419375312528905622822703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609892500416705207497096937 457419375312528905622822703)
        ·
          refine ⟨686129062968793358434234055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457419375312528905622822703 686129062968793358434234055)
          ·
            refine ⟨1029193594453190037651351083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686129062968793358434234055 1029193594453190037651351083)
            ·
              refine ⟨1543790391679785056477026625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029193594453190037651351083 1543790391679785056477026625)
              ·
                refine ⟨1157842793759838792357769969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543790391679785056477026625 1157842793759838792357769969)
                ·
                  refine ⟨868382095319879094268327477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1157842793759838792357769969 868382095319879094268327477)
                  ·
                    refine ⟨81410821436238665087655701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 868382095319879094268327477 81410821436238665087655701)
                    ·
                      refine ⟨3816132254823687425983861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81410821436238665087655701 3816132254823687425983861)
                      ·
                        rfl

theorem cell23_7431891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_7431891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431891 prefixEnd_7431891 := by exact prefixLift 7431891
  have htrace : WordTrace (prefixWord ++ tailWord_7431891) baseStart_7431891 baseEnd_7431891 := by
    simpa [prefixWord, tailWord_7431891, baseEnd_7431891] using wordTrace_append hprefix tailTrace_7431891
  have hstable : (prefixWord ++ tailWord_7431891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431891).length < 2 ^ (prefixWord ++ tailWord_7431891).sum := by decide
  have hdescent : baseEnd_7431891 < baseStart_7431891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431898 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_7431898 : Nat := 118140960795 + 7431898 * 2 ^ 59
def prefixEnd_7431898 : Nat := 4983230072969 + 3 ^ 40 * 7431898 * 2
def baseEnd_7431898 : Nat := 3816135849188268898596329

theorem tailTrace_7431898 : CollatzResearch.WordTrace tailWord_7431898 prefixEnd_7431898 3816135849188268898596329 := by
  unfold tailWord_7431898
  simp only [CollatzResearch.WordTrace]
  refine ⟨67765897207377571992998087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180709059219673525314661565 67765897207377571992998087)
  ·
    refine ⟨101648845811066357989497131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67765897207377571992998087 101648845811066357989497131)
    ·
      refine ⟨152473268716599536984245697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101648845811066357989497131 152473268716599536984245697)
      ·
        refine ⟨114354951537449652738184273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152473268716599536984245697 114354951537449652738184273)
        ·
          refine ⟨85766213653087239553638205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114354951537449652738184273 85766213653087239553638205)
          ·
            refine ⟨32162330119907714832614327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85766213653087239553638205 32162330119907714832614327)
            ·
              refine ⟨48243495179861572248921491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32162330119907714832614327 48243495179861572248921491)
              ·
                refine ⟨72365242769792358373382237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48243495179861572248921491 72365242769792358373382237)
                ·
                  refine ⟨27136966038672134390018339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72365242769792358373382237 27136966038672134390018339)
                  ·
                    refine ⟨40705449058008201585027509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27136966038672134390018339 40705449058008201585027509)
                    ·
                      refine ⟨3816135849188268898596329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40705449058008201585027509 3816135849188268898596329)
                      ·
                        rfl

theorem cell23_7431898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_7431898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431898 prefixEnd_7431898 := by exact prefixLift 7431898
  have htrace : WordTrace (prefixWord ++ tailWord_7431898) baseStart_7431898 baseEnd_7431898 := by
    simpa [prefixWord, tailWord_7431898, baseEnd_7431898] using wordTrace_append hprefix tailTrace_7431898
  have hstable : (prefixWord ++ tailWord_7431898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431898).length < 2 ^ (prefixWord ++ tailWord_7431898).sum := by decide
  have hdescent : baseEnd_7431898 < baseStart_7431898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431908 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_7431908 : Nat := 118140960795 + 7431908 * 2 ^ 59
def prefixEnd_7431908 : Nat := 4983230072969 + 3 ^ 40 * 7431908 * 2
def baseEnd_7431908 : Nat := 3816140983994813859471283

theorem tailTrace_7431908 : CollatzResearch.WordTrace tailWord_7431908 prefixEnd_7431908 3816140983994813859471283 := by
  unfold tailWord_7431908
  simp only [CollatzResearch.WordTrace]
  refine ⟨135531976779737029839928189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180709302372982706453237585 135531976779737029839928189)
  ·
    refine ⟨50824491292401386189973071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135531976779737029839928189 50824491292401386189973071)
    ·
      refine ⟨76236736938602079284959607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50824491292401386189973071 76236736938602079284959607)
      ·
        refine ⟨114355105407903118927439411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76236736938602079284959607 114355105407903118927439411)
        ·
          refine ⟨171532658111854678391159117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114355105407903118927439411 171532658111854678391159117)
          ·
            refine ⟨64324746791945504396684669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171532658111854678391159117 64324746791945504396684669)
            ·
              refine ⟨24121780046979564148756751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64324746791945504396684669 24121780046979564148756751)
              ·
                refine ⟨36182670070469346223135127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24121780046979564148756751 36182670070469346223135127)
                ·
                  refine ⟨54274005105704019334702691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36182670070469346223135127 54274005105704019334702691)
                  ·
                    refine ⟨81411007658556029002054037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54274005105704019334702691 81411007658556029002054037)
                    ·
                      refine ⟨3816140983994813859471283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81411007658556029002054037 3816140983994813859471283)
                      ·
                        rfl

theorem cell23_7431908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_7431908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431908 prefixEnd_7431908 := by exact prefixLift 7431908
  have htrace : WordTrace (prefixWord ++ tailWord_7431908) baseStart_7431908 baseEnd_7431908 := by
    simpa [prefixWord, tailWord_7431908, baseEnd_7431908] using wordTrace_append hprefix tailTrace_7431908
  have hstable : (prefixWord ++ tailWord_7431908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431908).length < 2 ^ (prefixWord ++ tailWord_7431908).sum := by decide
  have hdescent : baseEnd_7431908 < baseStart_7431908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431912 : List Nat := [2, 1, 4, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_7431912 : Nat := 118140960795 + 7431912 * 2 ^ 59
def prefixEnd_7431912 : Nat := 4983230072969 + 3 ^ 40 * 7431912 * 2
def baseEnd_7431912 : Nat := 3816143037917431843821265

theorem tailTrace_7431912 : CollatzResearch.WordTrace tailWord_7431912 prefixEnd_7431912 3816143037917431843821265 := by
  unfold tailWord_7431912
  simp only [CollatzResearch.WordTrace]
  refine ⟨135532049725729784181500995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180709399634306378908667993 135532049725729784181500995)
  ·
    refine ⟨203298074588594676272251493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135532049725729784181500995 203298074588594676272251493)
    ·
      refine ⟨38118388985361501801047155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203298074588594676272251493 38118388985361501801047155)
      ·
        refine ⟨57177583478042252701570733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38118388985361501801047155 57177583478042252701570733)
        ·
          refine ⟨21441593804265844763089025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57177583478042252701570733 21441593804265844763089025)
          ·
            refine ⟨16081195353199383572316769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21441593804265844763089025 16081195353199383572316769)
            ·
              refine ⟨12060896514899537679237577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16081195353199383572316769 12060896514899537679237577)
              ·
                refine ⟨9045672386174653259428183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12060896514899537679237577 9045672386174653259428183)
                ·
                  refine ⟨13568508579261979889142275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9045672386174653259428183 13568508579261979889142275)
                  ·
                    refine ⟨20352762868892969833713413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13568508579261979889142275 20352762868892969833713413)
                    ·
                      refine ⟨3816143037917431843821265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20352762868892969833713413 3816143037917431843821265)
                      ·
                        rfl

theorem cell23_7431912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_7431912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431912 prefixEnd_7431912 := by exact prefixLift 7431912
  have htrace : WordTrace (prefixWord ++ tailWord_7431912) baseStart_7431912 baseEnd_7431912 := by
    simpa [prefixWord, tailWord_7431912, baseEnd_7431912] using wordTrace_append hprefix tailTrace_7431912
  have hstable : (prefixWord ++ tailWord_7431912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431912).length < 2 ^ (prefixWord ++ tailWord_7431912).sum := by decide
  have hdescent : baseEnd_7431912 < baseStart_7431912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431915 : List Nat := [1, 1, 1, 1, 2, 4, 3, 4, 1, 2, 3]
def baseStart_7431915 : Nat := 118140960795 + 7431915 * 2 ^ 59
def prefixEnd_7431915 : Nat := 4983230072969 + 3 ^ 40 * 7431915 * 2
def baseEnd_7431915 : Nat := 3816144578359395332083751

theorem tailTrace_7431915 : CollatzResearch.WordTrace tailWord_7431915 prefixEnd_7431915 3816144578359395332083751 := by
  unfold tailWord_7431915
  simp only [CollatzResearch.WordTrace]
  refine ⟨271064208870448699875361199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180709472580299133250240799 271064208870448699875361199)
  ·
    refine ⟨406596313305673049813041799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271064208870448699875361199 406596313305673049813041799)
    ·
      refine ⟨609894469958509574719562699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406596313305673049813041799 609894469958509574719562699)
      ·
        refine ⟨914841704937764362079344049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609894469958509574719562699 914841704937764362079344049)
        ·
          refine ⟨686131278703323271559508037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 914841704937764362079344049 686131278703323271559508037)
          ·
            refine ⟨128649614756873113417407757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 686131278703323271559508037 128649614756873113417407757)
            ·
              refine ⟨48243605533827417531527909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128649614756873113417407757 48243605533827417531527909)
              ·
                refine ⟨9045676037592640787161483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48243605533827417531527909 9045676037592640787161483)
                ·
                  refine ⟨13568514056388961180742225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9045676037592640787161483 13568514056388961180742225)
                  ·
                    refine ⟨10176385542291720885556669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13568514056388961180742225 10176385542291720885556669)
                    ·
                      refine ⟨3816144578359395332083751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10176385542291720885556669 3816144578359395332083751)
                      ·
                        rfl

theorem cell23_7431915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 2, 3].length) (baseStart_7431915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431915 prefixEnd_7431915 := by exact prefixLift 7431915
  have htrace : WordTrace (prefixWord ++ tailWord_7431915) baseStart_7431915 baseEnd_7431915 := by
    simpa [prefixWord, tailWord_7431915, baseEnd_7431915] using wordTrace_append hprefix tailTrace_7431915
  have hstable : (prefixWord ++ tailWord_7431915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431915).length < 2 ^ (prefixWord ++ tailWord_7431915).sum := by decide
  have hdescent : baseEnd_7431915 < baseStart_7431915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431918 : List Nat := [4, 1, 2, 1, 1, 2, 3, 9]
def baseStart_7431918 : Nat := 118140960795 + 7431918 * 2 ^ 59
def prefixEnd_7431918 : Nat := 4983230072969 + 3 ^ 40 * 7431918 * 2
def baseEnd_7431918 : Nat := 141338745140791067420231

theorem tailTrace_7431918 : CollatzResearch.WordTrace tailWord_7431918 prefixEnd_7431918 141338745140791067420231 := by
  unfold tailWord_7431918
  simp only [CollatzResearch.WordTrace]
  refine ⟨33883039786179728923465051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180709545526291887591813605 33883039786179728923465051)
  ·
    refine ⟨50824559679269593385197577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33883039786179728923465051 50824559679269593385197577)
    ·
      refine ⟨38118419759452195038898183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50824559679269593385197577 38118419759452195038898183)
      ·
        refine ⟨57177629639178292558347275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38118419759452195038898183 57177629639178292558347275)
        ·
          refine ⟨85766444458767438837520913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57177629639178292558347275 85766444458767438837520913)
          ·
            refine ⟨64324833344075579128140685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85766444458767438837520913 64324833344075579128140685)
            ·
              refine ⟨24121812504028342173052757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64324833344075579128140685 24121812504028342173052757)
              ·
                refine ⟨141338745140791067420231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24121812504028342173052757 141338745140791067420231)
                ·
                  rfl

theorem cell23_7431918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_7431918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431918 prefixEnd_7431918 := by exact prefixLift 7431918
  have htrace : WordTrace (prefixWord ++ tailWord_7431918) baseStart_7431918 baseEnd_7431918 := by
    simpa [prefixWord, tailWord_7431918, baseEnd_7431918] using wordTrace_append hprefix tailTrace_7431918
  have hstable : (prefixWord ++ tailWord_7431918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431918).length < 2 ^ (prefixWord ++ tailWord_7431918).sum := by decide
  have hdescent : baseEnd_7431918 < baseStart_7431918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7431966 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_7431966 : Nat := 118140960795 + 7431966 * 2 ^ 59
def prefixEnd_7431966 : Nat := 4983230072969 + 3 ^ 40 * 7431966 * 2
def baseEnd_7431966 : Nat := 3816170765872774632546017

theorem tailTrace_7431966 : CollatzResearch.WordTrace tailWord_7431966 prefixEnd_7431966 3816170765872774632546017 := by
  unfold tailWord_7431966
  simp only [CollatzResearch.WordTrace]
  refine ⟨33883258624157991948183469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180710712662175957056978501 33883258624157991948183469)
  ·
    refine ⟨12706221984059246980568801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33883258624157991948183469 12706221984059246980568801)
    ·
      refine ⟨9529666488044435235426601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12706221984059246980568801 9529666488044435235426601)
      ·
        refine ⟨7147249866033326426569951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9529666488044435235426601 7147249866033326426569951)
        ·
          refine ⟨10720874799049989639854927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7147249866033326426569951 10720874799049989639854927)
          ·
            refine ⟨16081312198574984459782391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10720874799049989639854927 16081312198574984459782391)
            ·
              refine ⟨24121968297862476689673587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16081312198574984459782391 24121968297862476689673587)
              ·
                refine ⟨36182952446793715034510381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24121968297862476689673587 36182952446793715034510381)
                ·
                  refine ⟨13568607167547643137941393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36182952446793715034510381 13568607167547643137941393)
                  ·
                    refine ⟨10176455375660732353456045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13568607167547643137941393 10176455375660732353456045)
                    ·
                      refine ⟨3816170765872774632546017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10176455375660732353456045 3816170765872774632546017)
                      ·
                        rfl

theorem cell23_7431966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_7431966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7431966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7431966 prefixEnd_7431966 := by exact prefixLift 7431966
  have htrace : WordTrace (prefixWord ++ tailWord_7431966) baseStart_7431966 baseEnd_7431966 := by
    simpa [prefixWord, tailWord_7431966, baseEnd_7431966] using wordTrace_append hprefix tailTrace_7431966
  have hstable : (prefixWord ++ tailWord_7431966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7431966).length < 2 ^ (prefixWord ++ tailWord_7431966).sum := by decide
  have hdescent : baseEnd_7431966 < baseStart_7431966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7431966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432006 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_7432006 : Nat := 118140960795 + 7432006 * 2 ^ 59
def prefixEnd_7432006 : Nat := 4983230072969 + 3 ^ 40 * 7432006 * 2
def baseEnd_7432006 : Nat := 3816191305098954476045833

theorem tailTrace_7432006 : CollatzResearch.WordTrace tailWord_7432006 prefixEnd_7432006 3816191305098954476045833 := by
  unfold tailWord_7432006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8470860247284969450528871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 180711685275412681611282581 8470860247284969450528871)
  ·
    refine ⟨12706290370927454175793307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8470860247284969450528871 12706290370927454175793307)
    ·
      refine ⟨19059435556391181263689961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12706290370927454175793307 19059435556391181263689961)
      ·
        refine ⟨14294576667293385947767471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19059435556391181263689961 14294576667293385947767471)
        ·
          refine ⟨21441865000940078921651207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14294576667293385947767471 21441865000940078921651207)
          ·
            refine ⟨32162797501410118382476811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21441865000940078921651207 32162797501410118382476811)
            ·
              refine ⟨48244196252115177573715217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32162797501410118382476811 48244196252115177573715217)
              ·
                refine ⟨36183147189086383180286413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48244196252115177573715217 36183147189086383180286413)
                ·
                  refine ⟨13568680195907393692607405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36183147189086383180286413 13568680195907393692607405)
                  ·
                    refine ⟨5088255073465272634727777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13568680195907393692607405 5088255073465272634727777)
                    ·
                      refine ⟨3816191305098954476045833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088255073465272634727777 3816191305098954476045833)
                      ·
                        rfl

theorem cell23_7432006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_7432006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432006 prefixEnd_7432006 := by exact prefixLift 7432006
  have htrace : WordTrace (prefixWord ++ tailWord_7432006) baseStart_7432006 baseEnd_7432006 := by
    simpa [prefixWord, tailWord_7432006, baseEnd_7432006] using wordTrace_append hprefix tailTrace_7432006
  have hstable : (prefixWord ++ tailWord_7432006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432006).length < 2 ^ (prefixWord ++ tailWord_7432006).sum := by decide
  have hdescent : baseEnd_7432006 < baseStart_7432006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432092 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7432092 : Nat := 118140960795 + 7432092 * 2 ^ 59
def prefixEnd_7432092 : Nat := 4983230072969 + 3 ^ 40 * 7432092 * 2
def baseEnd_7432092 : Nat := 3816235464435241139570437

theorem tailTrace_7432092 : CollatzResearch.WordTrace tailWord_7432092 prefixEnd_7432092 3816235464435241139570437 := by
  unfold tailWord_7432092
  simp only [CollatzResearch.WordTrace]
  refine ⟨135535332295403729552277265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180713776393871639403036353 135535332295403729552277265)
  ·
    refine ⟨101651499221552797164207949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135535332295403729552277265 101651499221552797164207949)
    ·
      refine ⟨38119312208082298936577981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101651499221552797164207949 38119312208082298936577981)
      ·
        refine ⟨14294742078030862101216743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38119312208082298936577981 14294742078030862101216743)
        ·
          refine ⟨21442113117046293151825115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14294742078030862101216743 21442113117046293151825115)
          ·
            refine ⟨32163169675569439727737673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21442113117046293151825115 32163169675569439727737673)
            ·
              refine ⟨24122377256677079795803255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32163169675569439727737673 24122377256677079795803255)
              ·
                refine ⟨36183565885015619693704883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24122377256677079795803255 36183565885015619693704883)
                ·
                  refine ⟨54275348827523429540557325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36183565885015619693704883 54275348827523429540557325)
                  ·
                    refine ⟨20353255810321286077708997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54275348827523429540557325 20353255810321286077708997)
                    ·
                      refine ⟨3816235464435241139570437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20353255810321286077708997 3816235464435241139570437)
                      ·
                        rfl

theorem cell23_7432092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7432092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432092 prefixEnd_7432092 := by exact prefixLift 7432092
  have htrace : WordTrace (prefixWord ++ tailWord_7432092) baseStart_7432092 baseEnd_7432092 := by
    simpa [prefixWord, tailWord_7432092, baseEnd_7432092] using wordTrace_append hprefix tailTrace_7432092
  have hstable : (prefixWord ++ tailWord_7432092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432092).length < 2 ^ (prefixWord ++ tailWord_7432092).sum := by decide
  have hdescent : baseEnd_7432092 < baseStart_7432092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432110 : List Nat := [4, 1, 5, 1, 1, 1, 3, 2, 5]
def baseStart_7432110 : Nat := 118140960795 + 7432110 * 2 ^ 59
def prefixEnd_7432110 : Nat := 4983230072969 + 3 ^ 40 * 7432110 * 2
def baseEnd_7432110 : Nat := 424027189676335785460595

theorem tailTrace_7432110 : CollatzResearch.WordTrace tailWord_7432110 prefixEnd_7432110 424027189676335785460595 := by
  unfold tailWord_7432110
  simp only [CollatzResearch.WordTrace]
  refine ⟨33883915138092781022338723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180714214069828165452473189 33883915138092781022338723)
  ·
    refine ⟨50825872707139171533508085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33883915138092781022338723 50825872707139171533508085)
    ·
      refine ⟨4764925566294297331266383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50825872707139171533508085 4764925566294297331266383)
      ·
        refine ⟨7147388349441445996899575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4764925566294297331266383 7147388349441445996899575)
        ·
          refine ⟨10721082524162168995349363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7147388349441445996899575 10721082524162168995349363)
          ·
            refine ⟨16081623786243253493024045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10721082524162168995349363 16081623786243253493024045)
            ·
              refine ⟨6030608919841220059884017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16081623786243253493024045 6030608919841220059884017)
              ·
                refine ⟨4522956689880915044913013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6030608919841220059884017 4522956689880915044913013)
                ·
                  refine ⟨424027189676335785460595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4522956689880915044913013 424027189676335785460595)
                  ·
                    rfl

theorem cell23_7432110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_7432110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432110 prefixEnd_7432110 := by exact prefixLift 7432110
  have htrace : WordTrace (prefixWord ++ tailWord_7432110) baseStart_7432110 baseEnd_7432110 := by
    simpa [prefixWord, tailWord_7432110, baseEnd_7432110] using wordTrace_append hprefix tailTrace_7432110
  have hstable : (prefixWord ++ tailWord_7432110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432110).length < 2 ^ (prefixWord ++ tailWord_7432110).sum := by decide
  have hdescent : baseEnd_7432110 < baseStart_7432110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432115 : List Nat := [1, 1, 1, 2, 3, 1, 4, 4, 6]
def baseStart_7432115 : Nat := 118140960795 + 7432115 * 2 ^ 59
def prefixEnd_7432115 : Nat := 4983230072969 + 3 ^ 40 * 7432115 * 2
def baseEnd_7432115 : Nat := 424027474943366061064759

theorem tailTrace_7432115 : CollatzResearch.WordTrace tailWord_7432115 prefixEnd_7432115 424027474943366061064759 := by
  unfold tailWord_7432115
  simp only [CollatzResearch.WordTrace]
  refine ⟨271071503469724134032641799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180714335646482756021761199 271071503469724134032641799)
  ·
    refine ⟨406607255204586201048962699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271071503469724134032641799 406607255204586201048962699)
    ·
      refine ⟨609910882806879301573444049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406607255204586201048962699 609910882806879301573444049)
      ·
        refine ⟨457433162105159476180083037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609910882806879301573444049 457433162105159476180083037)
        ·
          refine ⟨171537435789434803567531139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457433162105159476180083037 171537435789434803567531139)
          ·
            refine ⟨257306153684152205351296709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171537435789434803567531139 257306153684152205351296709)
            ·
              refine ⟨48244903815778538503368133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257306153684152205351296709 48244903815778538503368133)
              ·
                refine ⟨9045919465458475969381525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48244903815778538503368133 9045919465458475969381525)
                ·
                  refine ⟨424027474943366061064759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9045919465458475969381525 424027474943366061064759)
                  ·
                    rfl

theorem cell23_7432115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 6].length) (baseStart_7432115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432115 prefixEnd_7432115 := by exact prefixLift 7432115
  have htrace : WordTrace (prefixWord ++ tailWord_7432115) baseStart_7432115 baseEnd_7432115 := by
    simpa [prefixWord, tailWord_7432115, baseEnd_7432115] using wordTrace_append hprefix tailTrace_7432115
  have hstable : (prefixWord ++ tailWord_7432115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432115).length < 2 ^ (prefixWord ++ tailWord_7432115).sum := by decide
  have hdescent : baseEnd_7432115 < baseStart_7432115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432146 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_7432146 : Nat := 118140960795 + 7432146 * 2 ^ 59
def prefixEnd_7432146 : Nat := 4983230072969 + 3 ^ 40 * 7432146 * 2
def baseEnd_7432146 : Nat := 3816263192390583928295189

theorem tailTrace_7432146 : CollatzResearch.WordTrace tailWord_7432146 prefixEnd_7432146 3816263192390583928295189 := by
  unfold tailWord_7432146
  simp only [CollatzResearch.WordTrace]
  refine ⟨67768158533152956581755073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180715089421741217551346861 67768158533152956581755073)
  ·
    refine ⟨50826118899864717436316305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67768158533152956581755073 50826118899864717436316305)
    ·
      refine ⟨38119589174898538077237229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50826118899864717436316305 38119589174898538077237229)
      ·
        refine ⟨14294845940586951778963961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38119589174898538077237229 14294845940586951778963961)
        ·
          refine ⟨10721134455440213834222971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14294845940586951778963961 10721134455440213834222971)
          ·
            refine ⟨16081701683160320751334457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10721134455440213834222971 16081701683160320751334457)
            ·
              refine ⟨12061276262370240563500843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16081701683160320751334457 12061276262370240563500843)
              ·
                refine ⟨18091914393555360845251265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12061276262370240563500843 18091914393555360845251265)
                ·
                  refine ⟨13568935795166520633938449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18091914393555360845251265 13568935795166520633938449)
                  ·
                    refine ⟨10176701846374890475453837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13568935795166520633938449 10176701846374890475453837)
                    ·
                      refine ⟨3816263192390583928295189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10176701846374890475453837 3816263192390583928295189)
                      ·
                        rfl

theorem cell23_7432146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_7432146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432146 prefixEnd_7432146 := by exact prefixLift 7432146
  have htrace : WordTrace (prefixWord ++ tailWord_7432146) baseStart_7432146 baseEnd_7432146 := by
    simpa [prefixWord, tailWord_7432146, baseEnd_7432146] using wordTrace_append hprefix tailTrace_7432146
  have hstable : (prefixWord ++ tailWord_7432146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432146).length < 2 ^ (prefixWord ++ tailWord_7432146).sum := by decide
  have hdescent : baseEnd_7432146 < baseStart_7432146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432175 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 3, 6]
def baseStart_7432175 : Nat := 118140960795 + 7432175 * 2 ^ 59
def prefixEnd_7432175 : Nat := 4983230072969 + 3 ^ 40 * 7432175 * 2
def baseEnd_7432175 : Nat := 1272092694443188104944185

theorem tailTrace_7432175 : CollatzResearch.WordTrace tailWord_7432175 prefixEnd_7432175 1272092694443188104944185 := by
  unfold tailWord_7432175
  simp only [CollatzResearch.WordTrace]
  refine ⟨271073691849506764279825979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180715794566337842853217319 271073691849506764279825979)
  ·
    refine ⟨406610537774260146419738969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271073691849506764279825979 406610537774260146419738969)
    ·
      refine ⟨304957903330695109814804227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406610537774260146419738969 304957903330695109814804227)
      ·
        refine ⟨457436854996042664722206341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304957903330695109814804227 457436854996042664722206341)
        ·
          refine ⟨85769410311757999635413689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 457436854996042664722206341 85769410311757999635413689)
          ·
            refine ⟨64327057733818499726560267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85769410311757999635413689 64327057733818499726560267)
            ·
              refine ⟨96490586600727749589840401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64327057733818499726560267 96490586600727749589840401)
              ·
                refine ⟨72367939950545812192380301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96490586600727749589840401 72367939950545812192380301)
                ·
                  refine ⟨27137977481454679572142613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72367939950545812192380301 27137977481454679572142613)
                  ·
                    refine ⟨1272092694443188104944185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27137977481454679572142613 1272092694443188104944185)
                    ·
                      rfl

theorem cell23_7432175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 6].length) (baseStart_7432175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432175 prefixEnd_7432175 := by exact prefixLift 7432175
  have htrace : WordTrace (prefixWord ++ tailWord_7432175) baseStart_7432175 baseEnd_7432175 := by
    simpa [prefixWord, tailWord_7432175, baseEnd_7432175] using wordTrace_append hprefix tailTrace_7432175
  have hstable : (prefixWord ++ tailWord_7432175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432175).length < 2 ^ (prefixWord ++ tailWord_7432175).sum := by decide
  have hdescent : baseEnd_7432175 < baseStart_7432175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432195 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 6]
def baseStart_7432195 : Nat := 118140960795 + 7432195 * 2 ^ 59
def prefixEnd_7432195 : Nat := 4983230072969 + 3 ^ 40 * 7432195 * 2
def baseEnd_7432195 : Nat := 3816288352942654236582463

theorem tailTrace_7432195 : CollatzResearch.WordTrace tailWord_7432195 prefixEnd_7432195 3816288352942654236582463 := by
  unfold tailWord_7432195
  simp only [CollatzResearch.WordTrace]
  refine ⟨271074421309434307695554039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180716280872956205130369359 271074421309434307695554039)
  ·
    refine ⟨406611631964151461543331059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271074421309434307695554039 406611631964151461543331059)
    ·
      refine ⟨609917447946227192314996589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406611631964151461543331059 609917447946227192314996589)
      ·
        refine ⟨228719042979835197118123721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 609917447946227192314996589 228719042979835197118123721)
        ·
          refine ⟨171539282234876397838592791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228719042979835197118123721 171539282234876397838592791)
          ·
            refine ⟨257308923352314596757889187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171539282234876397838592791 257308923352314596757889187)
            ·
              refine ⟨385963385028471895136833781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257308923352314596757889187 385963385028471895136833781)
              ·
                refine ⟨36184067346419240169078167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 385963385028471895136833781 36184067346419240169078167)
                ·
                  refine ⟨54276101019628860253617251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36184067346419240169078167 54276101019628860253617251)
                  ·
                    refine ⟨81414151529443290380425877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54276101019628860253617251 81414151529443290380425877)
                    ·
                      refine ⟨3816288352942654236582463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81414151529443290380425877 3816288352942654236582463)
                      ·
                        rfl

theorem cell23_7432195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_7432195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432195 prefixEnd_7432195 := by exact prefixLift 7432195
  have htrace : WordTrace (prefixWord ++ tailWord_7432195) baseStart_7432195 baseEnd_7432195 := by
    simpa [prefixWord, tailWord_7432195, baseEnd_7432195] using wordTrace_append hprefix tailTrace_7432195
  have hstable : (prefixWord ++ tailWord_7432195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432195).length < 2 ^ (prefixWord ++ tailWord_7432195).sum := by decide
  have hdescent : baseEnd_7432195 < baseStart_7432195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432213 : List Nat := [1, 3, 2, 1, 6, 1, 2, 1, 1, 5]
def baseStart_7432213 : Nat := 118140960795 + 7432213 * 2 ^ 59
def prefixEnd_7432213 : Nat := 4983230072969 + 3 ^ 40 * 7432213 * 2
def baseEnd_7432213 : Nat := 1272099198531478388719127

theorem tailTrace_7432213 : CollatzResearch.WordTrace tailWord_7432213 prefixEnd_7432213 1272099198531478388719127 := by
  unfold tailWord_7432213
  simp only [CollatzResearch.WordTrace]
  refine ⟨271075077823369096769709293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180716718548912731179806195 271075077823369096769709293)
  ·
    refine ⟨101653154183763411288640985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271075077823369096769709293 101653154183763411288640985)
    ·
      refine ⟨76239865637822558466480739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101653154183763411288640985 76239865637822558466480739)
      ·
        refine ⟨114359798456733837699721109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76239865637822558466480739 114359798456733837699721109)
        ·
          refine ⟨5360615552659398642174427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114359798456733837699721109 5360615552659398642174427)
          ·
            refine ⟨8040923328989097963261641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5360615552659398642174427 8040923328989097963261641)
            ·
              refine ⟨6030692496741823472446231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8040923328989097963261641 6030692496741823472446231)
              ·
                refine ⟨9046038745112735208669347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6030692496741823472446231 9046038745112735208669347)
                ·
                  refine ⟨13569058117669102813004021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9046038745112735208669347 13569058117669102813004021)
                  ·
                    refine ⟨1272099198531478388719127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13569058117669102813004021 1272099198531478388719127)
                    ·
                      rfl

theorem cell23_7432213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_7432213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432213 prefixEnd_7432213 := by exact prefixLift 7432213
  have htrace : WordTrace (prefixWord ++ tailWord_7432213) baseStart_7432213 baseEnd_7432213 := by
    simpa [prefixWord, tailWord_7432213, baseEnd_7432213] using wordTrace_append hprefix tailTrace_7432213
  have hstable : (prefixWord ++ tailWord_7432213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432213).length < 2 ^ (prefixWord ++ tailWord_7432213).sum := by decide
  have hdescent : baseEnd_7432213 < baseStart_7432213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432235 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 2, 7]
def baseStart_7432235 : Nat := 118140960795 + 7432235 * 2 ^ 59
def prefixEnd_7432235 : Nat := 4983230072969 + 3 ^ 40 * 7432235 * 2
def baseEnd_7432235 : Nat := 1272102964056278026694093

theorem tailTrace_7432235 : CollatzResearch.WordTrace tailWord_7432235 prefixEnd_7432235 1272102964056278026694093 := by
  unfold tailWord_7432235
  simp only [CollatzResearch.WordTrace]
  refine ⟨271075880229289394527010159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180717253486192929684673439 271075880229289394527010159)
  ·
    refine ⟨406613820343934091790515239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271075880229289394527010159 406613820343934091790515239)
    ·
      refine ⟨609920730515901137685772859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406613820343934091790515239 609920730515901137685772859)
      ·
        refine ⟨914881095773851706528659289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609920730515901137685772859 914881095773851706528659289)
        ·
          refine ⟨686160821830388779896494467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 914881095773851706528659289 686160821830388779896494467)
          ·
            refine ⟨1029241232745583169844741701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686160821830388779896494467 1029241232745583169844741701)
            ·
              refine ⟨192982731139796844345889069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1029241232745583169844741701 192982731139796844345889069)
              ·
                refine ⟨72368524177423816629708401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192982731139796844345889069 72368524177423816629708401)
                ·
                  refine ⟨54276393133067862472281301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72368524177423816629708401 54276393133067862472281301)
                  ·
                    refine ⟨1272102964056278026694093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54276393133067862472281301 1272102964056278026694093)
                    ·
                      rfl

theorem cell23_7432235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 7].length) (baseStart_7432235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432235 prefixEnd_7432235 := by exact prefixLift 7432235
  have htrace : WordTrace (prefixWord ++ tailWord_7432235) baseStart_7432235 baseEnd_7432235 := by
    simpa [prefixWord, tailWord_7432235, baseEnd_7432235] using wordTrace_append hprefix tailTrace_7432235
  have hstable : (prefixWord ++ tailWord_7432235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432235).length < 2 ^ (prefixWord ++ tailWord_7432235).sum := by decide
  have hdescent : baseEnd_7432235 < baseStart_7432235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432310 : List Nat := [5, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_7432310 : Nat := 118140960795 + 7432310 * 2 ^ 59
def prefixEnd_7432310 : Nat := 4983230072969 + 3 ^ 40 * 7432310 * 2
def baseEnd_7432310 : Nat := 3816347403217921286644435

theorem tailTrace_7432310 : CollatzResearch.WordTrace tailWord_7432310 prefixEnd_7432310 3816347403217921286644435 := by
  unfold tailWord_7432310
  simp only [CollatzResearch.WordTrace]
  refine ⟨16942413481501105145999399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180719077136011788223993589 16942413481501105145999399)
  ·
    refine ⟨25413620222251657718999099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16942413481501105145999399 25413620222251657718999099)
    ·
      refine ⟨38120430333377486578498649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25413620222251657718999099 38120430333377486578498649)
      ·
        refine ⟨28590322750033114933873987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38120430333377486578498649 28590322750033114933873987)
        ·
          refine ⟨42885484125049672400810981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28590322750033114933873987 42885484125049672400810981)
          ·
            refine ⟨8041028273446813575152059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42885484125049672400810981 8041028273446813575152059)
            ·
              refine ⟨12061542410170220362728089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8041028273446813575152059 12061542410170220362728089)
              ·
                refine ⟨9046156807627665272046067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12061542410170220362728089 9046156807627665272046067)
                ·
                  refine ⟨13569235211441497908069101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9046156807627665272046067 13569235211441497908069101)
                  ·
                    refine ⟨5088463204290561715525913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13569235211441497908069101 5088463204290561715525913)
                    ·
                      refine ⟨3816347403217921286644435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088463204290561715525913 3816347403217921286644435)
                      ·
                        rfl

theorem cell23_7432310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_7432310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432310 prefixEnd_7432310 := by exact prefixLift 7432310
  have htrace : WordTrace (prefixWord ++ tailWord_7432310) baseStart_7432310 baseEnd_7432310 := by
    simpa [prefixWord, tailWord_7432310, baseEnd_7432310] using wordTrace_append hprefix tailTrace_7432310
  have hstable : (prefixWord ++ tailWord_7432310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432310).length < 2 ^ (prefixWord ++ tailWord_7432310).sum := by decide
  have hdescent : baseEnd_7432310 < baseStart_7432310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432329 : List Nat := [1, 2, 1, 1, 4, 2, 2, 5, 5]
def baseStart_7432329 : Nat := 118140960795 + 7432329 * 2 ^ 59
def prefixEnd_7432329 : Nat := 4983230072969 + 3 ^ 40 * 7432329 * 2
def baseEnd_7432329 : Nat := 424039684372261856922983

theorem tailTrace_7432329 : CollatzResearch.WordTrace tailWord_7432329 prefixEnd_7432329 424039684372261856922983 := by
  unfold tailWord_7432329
  simp only [CollatzResearch.WordTrace]
  refine ⟨271079308690948848580932041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180719539127299232387288027 271079308690948848580932041)
  ·
    refine ⟨203309481518211636435699031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271079308690948848580932041 203309481518211636435699031)
    ·
      refine ⟨304964222277317454653548547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203309481518211636435699031 304964222277317454653548547)
      ·
        refine ⟨457446333415976181980322821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304964222277317454653548547 457446333415976181980322821)
        ·
          refine ⟨85771187515495534121310529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 457446333415976181980322821 85771187515495534121310529)
          ·
            refine ⟨64328390636621650590982897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85771187515495534121310529 64328390636621650590982897)
            ·
              refine ⟨48246292977466237943237173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64328390636621650590982897 48246292977466237943237173)
              ·
                refine ⟨4523089966637459807178485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48246292977466237943237173 4523089966637459807178485)
                ·
                  refine ⟨424039684372261856922983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4523089966637459807178485 424039684372261856922983)
                  ·
                    rfl

theorem cell23_7432329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 5].length) (baseStart_7432329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432329 prefixEnd_7432329 := by exact prefixLift 7432329
  have htrace : WordTrace (prefixWord ++ tailWord_7432329) baseStart_7432329 baseEnd_7432329 := by
    simpa [prefixWord, tailWord_7432329, baseEnd_7432329] using wordTrace_append hprefix tailTrace_7432329
  have hstable : (prefixWord ++ tailWord_7432329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432329).length < 2 ^ (prefixWord ++ tailWord_7432329).sum := by decide
  have hdescent : baseEnd_7432329 < baseStart_7432329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432356 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_7432356 : Nat := 118140960795 + 7432356 * 2 ^ 59
def prefixEnd_7432356 : Nat := 4983230072969 + 3 ^ 40 * 7432356 * 2
def baseEnd_7432356 : Nat := 3816371023328028106669223

theorem tailTrace_7432356 : CollatzResearch.WordTrace tailWord_7432356 prefixEnd_7432356 3816371023328028106669223 := by
  unfold tailWord_7432356
  simp only [CollatzResearch.WordTrace]
  refine ⟨135540146730925516096082461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180720195641234021461443281 135540146730925516096082461)
  ·
    refine ⟨50827555024097068536030923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135540146730925516096082461 50827555024097068536030923)
    ·
      refine ⟨76241332536145602804046385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50827555024097068536030923 76241332536145602804046385)
      ·
        refine ⟨57180999402109202103034789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76241332536145602804046385 57180999402109202103034789)
        ·
          refine ⟨10721437387895475394319023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57180999402109202103034789 10721437387895475394319023)
          ·
            refine ⟨16082156081843213091478535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10721437387895475394319023 16082156081843213091478535)
            ·
              refine ⟨24123234122764819637217803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16082156081843213091478535 24123234122764819637217803)
              ·
                refine ⟨36184851184147229455826705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24123234122764819637217803 36184851184147229455826705)
                ·
                  refine ⟨27138638388110422091870029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36184851184147229455826705 27138638388110422091870029)
                  ·
                    refine ⟨10176989395541408284451261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27138638388110422091870029 10176989395541408284451261)
                    ·
                      refine ⟨3816371023328028106669223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10176989395541408284451261 3816371023328028106669223)
                      ·
                        rfl

theorem cell23_7432356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_7432356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432356 prefixEnd_7432356 := by exact prefixLift 7432356
  have htrace : WordTrace (prefixWord ++ tailWord_7432356) baseStart_7432356 baseEnd_7432356 := by
    simpa [prefixWord, tailWord_7432356, baseEnd_7432356] using wordTrace_append hprefix tailTrace_7432356
  have hstable : (prefixWord ++ tailWord_7432356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432356).length < 2 ^ (prefixWord ++ tailWord_7432356).sum := by decide
  have hdescent : baseEnd_7432356 < baseStart_7432356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432379 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 1, 6, 2]
def baseStart_7432379 : Nat := 118140960795 + 7432379 * 2 ^ 59
def prefixEnd_7432379 : Nat := 4983230072969 + 3 ^ 40 * 7432379 * 2
def baseEnd_7432379 : Nat := 3816382833383081516681617

theorem tailTrace_7432379 : CollatzResearch.WordTrace tailWord_7432379 prefixEnd_7432379 3816382833383081516681617 := by
  unfold tailWord_7432379
  simp only [CollatzResearch.WordTrace]
  refine ⟨271081132340767707120252191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180720754893845138080168127 271081132340767707120252191)
  ·
    refine ⟨406621698511151560680378287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271081132340767707120252191 406621698511151560680378287)
    ·
      refine ⟨609932547766727341020567431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406621698511151560680378287 609932547766727341020567431)
      ·
        refine ⟨914898821650091011530851147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609932547766727341020567431 914898821650091011530851147)
        ·
          refine ⟨1372348232475136517296276721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914898821650091011530851147 1372348232475136517296276721)
          ·
            refine ⟨1029261174356352387972207541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1372348232475136517296276721 1029261174356352387972207541)
            ·
              refine ⟨96493235095908036372394457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1029261174356352387972207541 96493235095908036372394457)
              ·
                refine ⟨72369926321931027279295843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96493235095908036372394457 72369926321931027279295843)
                ·
                  refine ⟨108554889482896540918943765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72369926321931027279295843 108554889482896540918943765)
                  ·
                    refine ⟨5088510444510775355575489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108554889482896540918943765 5088510444510775355575489)
                    ·
                      refine ⟨3816382833383081516681617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088510444510775355575489 3816382833383081516681617)
                      ·
                        rfl

theorem cell23_7432379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 6, 2].length) (baseStart_7432379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432379 prefixEnd_7432379 := by exact prefixLift 7432379
  have htrace : WordTrace (prefixWord ++ tailWord_7432379) baseStart_7432379 baseEnd_7432379 := by
    simpa [prefixWord, tailWord_7432379, baseEnd_7432379] using wordTrace_append hprefix tailTrace_7432379
  have hstable : (prefixWord ++ tailWord_7432379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432379).length < 2 ^ (prefixWord ++ tailWord_7432379).sum := by decide
  have hdescent : baseEnd_7432379 < baseStart_7432379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432399 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 3]
def baseStart_7432399 : Nat := 118140960795 + 7432399 * 2 ^ 59
def prefixEnd_7432399 : Nat := 4983230072969 + 3 ^ 40 * 7432399 * 2
def baseEnd_7432399 : Nat := 3816393102996171438431525

theorem tailTrace_7432399 : CollatzResearch.WordTrace tailWord_7432399 prefixEnd_7432399 3816393102996171438431525 := by
  unfold tailWord_7432399
  simp only [CollatzResearch.WordTrace]
  refine ⟨271081861800695250535980251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180721241200463500357320167 271081861800695250535980251)
  ·
    refine ⟨406622792701042875803970377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271081861800695250535980251 406622792701042875803970377)
    ·
      refine ⟨304967094525782156852977783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406622792701042875803970377 304967094525782156852977783)
      ·
        refine ⟨457450641788673235279466675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304967094525782156852977783 457450641788673235279466675)
        ·
          refine ⟨686175962683009852919200013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457450641788673235279466675 686175962683009852919200013)
          ·
            refine ⟨257315986006128694844700005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 686175962683009852919200013 257315986006128694844700005)
            ·
              refine ⟨48246747376149130283381251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257315986006128694844700005 48246747376149130283381251)
              ·
                refine ⟨72370121064223695425071877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48246747376149130283381251 72370121064223695425071877)
                ·
                  refine ⟨13569397699541942892200977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72370121064223695425071877 13569397699541942892200977)
                  ·
                    refine ⟨10177048274656457169150733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13569397699541942892200977 10177048274656457169150733)
                    ·
                      refine ⟨3816393102996171438431525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10177048274656457169150733 3816393102996171438431525)
                      ·
                        rfl

theorem cell23_7432399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 3].length) (baseStart_7432399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432399 prefixEnd_7432399 := by exact prefixLift 7432399
  have htrace : WordTrace (prefixWord ++ tailWord_7432399) baseStart_7432399 baseEnd_7432399 := by
    simpa [prefixWord, tailWord_7432399, baseEnd_7432399] using wordTrace_append hprefix tailTrace_7432399
  have hstable : (prefixWord ++ tailWord_7432399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432399).length < 2 ^ (prefixWord ++ tailWord_7432399).sum := by decide
  have hdescent : baseEnd_7432399 < baseStart_7432399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432413 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_7432413 : Nat := 118140960795 + 7432413 * 2 ^ 59
def prefixEnd_7432413 : Nat := 4983230072969 + 3 ^ 40 * 7432413 * 2
def baseEnd_7432413 : Nat := 3816400291725334383656461

theorem tailTrace_7432413 : CollatzResearch.WordTrace tailWord_7432413 prefixEnd_7432413 3816400291725334383656461 := by
  unfold tailWord_7432413
  simp only [CollatzResearch.WordTrace]
  refine ⟨271082372422644530926989893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180721581615096353951326595 271082372422644530926989893)
  ·
    refine ⟨50827944829245849548810605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271082372422644530926989893 50827944829245849548810605)
    ·
      refine ⟨19060479310967193580803977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50827944829245849548810605 19060479310967193580803977)
      ·
        refine ⟨14295359483225395185602983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19060479310967193580803977 14295359483225395185602983)
        ·
          refine ⟨21443039224838092778404475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14295359483225395185602983 21443039224838092778404475)
          ·
            refine ⟨32164558837257139167606713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21443039224838092778404475 32164558837257139167606713)
            ·
              refine ⟨24123419127942854375705035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32164558837257139167606713 24123419127942854375705035)
              ·
                refine ⟨36185128691914281563557553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24123419127942854375705035 36185128691914281563557553)
                ·
                  refine ⟨27138846518935711172668165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36185128691914281563557553 27138846518935711172668165)
                  ·
                    refine ⟨5088533722300445844875281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27138846518935711172668165 5088533722300445844875281)
                    ·
                      refine ⟨3816400291725334383656461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088533722300445844875281 3816400291725334383656461)
                      ·
                        rfl

theorem cell23_7432413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_7432413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432413 prefixEnd_7432413 := by exact prefixLift 7432413
  have htrace : WordTrace (prefixWord ++ tailWord_7432413) baseStart_7432413 baseEnd_7432413 := by
    simpa [prefixWord, tailWord_7432413, baseEnd_7432413] using wordTrace_append hprefix tailTrace_7432413
  have hstable : (prefixWord ++ tailWord_7432413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432413).length < 2 ^ (prefixWord ++ tailWord_7432413).sum := by decide
  have hdescent : baseEnd_7432413 < baseStart_7432413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432432 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 2, 9]
def baseStart_7432432 : Nat := 118140960795 + 7432432 * 2 ^ 59
def prefixEnd_7432432 : Nat := 4983230072969 + 3 ^ 40 * 7432432 * 2
def baseEnd_7432432 : Nat := 1272136682619256603106291

theorem tailTrace_7432432 : CollatzResearch.WordTrace tailWord_7432432 prefixEnd_7432432 1272136682619256603106291 := by
  unfold tailWord_7432432
  simp only [CollatzResearch.WordTrace]
  refine ⟨135541532704787848585965775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180722043606383798114621033 135541532704787848585965775)
  ·
    refine ⟨203312299057181772878948663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135541532704787848585965775 203312299057181772878948663)
    ·
      refine ⟨304968448585772659318422995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203312299057181772878948663 304968448585772659318422995)
      ·
        refine ⟨457452672878658988977634493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304968448585772659318422995 457452672878658988977634493)
        ·
          refine ⟨171544752329497120866612935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457452672878658988977634493 171544752329497120866612935)
          ·
            refine ⟨257317128494245681299919403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171544752329497120866612935 257317128494245681299919403)
            ·
              refine ⟨385975692741368521949879105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257317128494245681299919403 385975692741368521949879105)
              ·
                refine ⟨289481769556026391462409329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385975692741368521949879105 289481769556026391462409329)
                ·
                  refine ⟨217111327167019793596806997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289481769556026391462409329 217111327167019793596806997)
                  ·
                    refine ⟨1272136682619256603106291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 217111327167019793596806997 1272136682619256603106291)
                    ·
                      rfl

theorem cell23_7432432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_7432432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432432 prefixEnd_7432432 := by exact prefixLift 7432432
  have htrace : WordTrace (prefixWord ++ tailWord_7432432) baseStart_7432432 baseEnd_7432432 := by
    simpa [prefixWord, tailWord_7432432, baseEnd_7432432] using wordTrace_append hprefix tailTrace_7432432
  have hstable : (prefixWord ++ tailWord_7432432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432432).length < 2 ^ (prefixWord ++ tailWord_7432432).sum := by decide
  have hdescent : baseEnd_7432432 < baseStart_7432432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432463 : List Nat := [1, 1, 2, 1, 1, 1, 3, 8, 1, 1, 3]
def baseStart_7432463 : Nat := 118140960795 + 7432463 * 2 ^ 59
def prefixEnd_7432463 : Nat := 4983230072969 + 3 ^ 40 * 7432463 * 2
def baseEnd_7432463 : Nat := 3816425965758059188031231

theorem tailTrace_7432463 : CollatzResearch.WordTrace tailWord_7432463 prefixEnd_7432463 3816425965758059188031231 := by
  unfold tailWord_7432463
  simp only [CollatzResearch.WordTrace]
  refine ⟨271084196072463389466310043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180722797381642259644206695 271084196072463389466310043)
  ·
    refine ⟨406626294108695084199465065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271084196072463389466310043 406626294108695084199465065)
    ·
      refine ⟨304969720581521313149598799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406626294108695084199465065 304969720581521313149598799)
      ·
        refine ⟨457454580872281969724398199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304969720581521313149598799 457454580872281969724398199)
        ·
          refine ⟨686181871308422954586597299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457454580872281969724398199 686181871308422954586597299)
          ·
            refine ⟨1029272806962634431879895949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686181871308422954586597299 1029272806962634431879895949)
            ·
              refine ⟨385977302610987911954960981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1029272806962634431879895949 385977302610987911954960981)
              ·
                refine ⟨4523171514972514593222199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 385977302610987911954960981 4523171514972514593222199)
                ·
                  refine ⟨6784757272458771889833299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4523171514972514593222199 6784757272458771889833299)
                  ·
                    refine ⟨10177135908688157834749949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6784757272458771889833299 10177135908688157834749949)
                    ·
                      refine ⟨3816425965758059188031231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10177135908688157834749949 3816425965758059188031231)
                      ·
                        rfl

theorem cell23_7432463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 1, 1, 3].length) (baseStart_7432463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432463 prefixEnd_7432463 := by exact prefixLift 7432463
  have htrace : WordTrace (prefixWord ++ tailWord_7432463) baseStart_7432463 baseEnd_7432463 := by
    simpa [prefixWord, tailWord_7432463, baseEnd_7432463] using wordTrace_append hprefix tailTrace_7432463
  have hstable : (prefixWord ++ tailWord_7432463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432463).length < 2 ^ (prefixWord ++ tailWord_7432463).sum := by decide
  have hdescent : baseEnd_7432463 < baseStart_7432463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432500 : List Nat := [2, 5, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_7432500 : Nat := 118140960795 + 7432500 * 2 ^ 59
def prefixEnd_7432500 : Nat := 4983230072969 + 3 ^ 40 * 7432500 * 2
def baseEnd_7432500 : Nat := 1272148321514091847756187

theorem tailTrace_7432500 : CollatzResearch.WordTrace tailWord_7432500 prefixEnd_7432500 1272148321514091847756187 := by
  unfold tailWord_7432500
  simp only [CollatzResearch.WordTrace]
  refine ⟨135542772786664672392703477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180723697048886229856937969 135542772786664672392703477)
  ·
    refine ⟨12707134948749813036815951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135542772786664672392703477 12707134948749813036815951)
    ·
      refine ⟨19060702423124719555223927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12707134948749813036815951 19060702423124719555223927)
      ·
        refine ⟨28591053634687079332835891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19060702423124719555223927 28591053634687079332835891)
        ·
          refine ⟨42886580452030618999253837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28591053634687079332835891 42886580452030618999253837)
          ·
            refine ⟨16082467669511482124720189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42886580452030618999253837 16082467669511482124720189)
            ·
              refine ⟨6030925376066805796770071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16082467669511482124720189 6030925376066805796770071)
              ·
                refine ⟨9046388064100208695155107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6030925376066805796770071 9046388064100208695155107)
                ·
                  refine ⟨13569582096150313042732661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9046388064100208695155107 13569582096150313042732661)
                  ·
                    refine ⟨1272148321514091847756187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13569582096150313042732661 1272148321514091847756187)
                    ·
                      rfl

theorem cell23_7432500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_7432500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432500 prefixEnd_7432500 := by exact prefixLift 7432500
  have htrace : WordTrace (prefixWord ++ tailWord_7432500) baseStart_7432500 baseEnd_7432500 := by
    simpa [prefixWord, tailWord_7432500, baseEnd_7432500] using wordTrace_append hprefix tailTrace_7432500
  have hstable : (prefixWord ++ tailWord_7432500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432500).length < 2 ^ (prefixWord ++ tailWord_7432500).sum := by decide
  have hdescent : baseEnd_7432500 < baseStart_7432500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432506 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5]
def baseStart_7432506 : Nat := 118140960795 + 7432506 * 2 ^ 59
def prefixEnd_7432506 : Nat := 4983230072969 + 3 ^ 40 * 7432506 * 2
def baseEnd_7432506 : Nat := 3816448045426202519793533

theorem tailTrace_7432506 : CollatzResearch.WordTrace tailWord_7432506 prefixEnd_7432506 3816448045426202519793533 := by
  unfold tailWord_7432506
  simp only [CollatzResearch.WordTrace]
  refine ⟨67771441102826901952531343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180723842940871738540083581 67771441102826901952531343)
  ·
    refine ⟨101657161654240352928797015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67771441102826901952531343 101657161654240352928797015)
    ·
      refine ⟨152485742481360529393195523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101657161654240352928797015 152485742481360529393195523)
      ·
        refine ⟨228728613722040794089793285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152485742481360529393195523 228728613722040794089793285)
        ·
          refine ⟨42886615072882648891836241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228728613722040794089793285 42886615072882648891836241)
          ·
            refine ⟨32164961304661986668877181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42886615072882648891836241 32164961304661986668877181)
            ·
              refine ⟨12061860489248245000828943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32164961304661986668877181 12061860489248245000828943)
              ·
                refine ⟨18092790733872367501243415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12061860489248245000828943 18092790733872367501243415)
                ·
                  refine ⟨27139186100808551251865123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18092790733872367501243415 27139186100808551251865123)
                  ·
                    refine ⟨40708779151212826877797685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27139186100808551251865123 40708779151212826877797685)
                    ·
                      refine ⟨3816448045426202519793533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40708779151212826877797685 3816448045426202519793533)
                      ·
                        rfl

theorem cell23_7432506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_7432506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432506 prefixEnd_7432506 := by exact prefixLift 7432506
  have htrace : WordTrace (prefixWord ++ tailWord_7432506) baseStart_7432506 baseEnd_7432506 := by
    simpa [prefixWord, tailWord_7432506, baseEnd_7432506] using wordTrace_append hprefix tailTrace_7432506
  have hstable : (prefixWord ++ tailWord_7432506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432506).length < 2 ^ (prefixWord ++ tailWord_7432506).sum := by decide
  have hdescent : baseEnd_7432506 < baseStart_7432506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432533 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_7432533 : Nat := 118140960795 + 7432533 * 2 ^ 59
def prefixEnd_7432533 : Nat := 4983230072969 + 3 ^ 40 * 7432533 * 2
def baseEnd_7432533 : Nat := 3816461909403873914155909

theorem tailTrace_7432533 : CollatzResearch.WordTrace tailWord_7432533 prefixEnd_7432533 3816461909403873914155909 := by
  unfold tailWord_7432533
  simp only [CollatzResearch.WordTrace]
  refine ⟨271086749182209791421358253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180724499454806527614238835 271086749182209791421358253)
  ·
    refine ⟨101657530943328671783009345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271086749182209791421358253 101657530943328671783009345)
    ·
      refine ⟨76243148207496503837257009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101657530943328671783009345 76243148207496503837257009)
      ·
        refine ⟨57182361155622377877942757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76243148207496503837257009 57182361155622377877942757)
        ·
          refine ⟨10721692716679195852114267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57182361155622377877942757 10721692716679195852114267)
          ·
            refine ⟨16082539075018793778171401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10721692716679195852114267 16082539075018793778171401)
            ·
              refine ⟨12061904306264095333628551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16082539075018793778171401 12061904306264095333628551)
              ·
                refine ⟨18092856459396143000442827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12061904306264095333628551 18092856459396143000442827)
                ·
                  refine ⟨27139284689094214500664241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18092856459396143000442827 27139284689094214500664241)
                  ·
                    refine ⟨20354463516820660875498181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27139284689094214500664241 20354463516820660875498181)
                    ·
                      refine ⟨3816461909403873914155909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20354463516820660875498181 3816461909403873914155909)
                      ·
                        rfl

theorem cell23_7432533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_7432533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432533 prefixEnd_7432533 := by exact prefixLift 7432533
  have htrace : WordTrace (prefixWord ++ tailWord_7432533) baseStart_7432533 baseEnd_7432533 := by
    simpa [prefixWord, tailWord_7432533, baseEnd_7432533] using wordTrace_append hprefix tailTrace_7432533
  have hstable : (prefixWord ++ tailWord_7432533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432533).length < 2 ^ (prefixWord ++ tailWord_7432533).sum := by decide
  have hdescent : baseEnd_7432533 < baseStart_7432533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432554 : List Nat := [3, 1, 3, 3, 1, 2, 2, 3, 1, 2, 2]
def baseStart_7432554 : Nat := 118140960795 + 7432554 * 2 ^ 59
def prefixEnd_7432554 : Nat := 4983230072969 + 3 ^ 40 * 7432554 * 2
def baseEnd_7432554 : Nat := 3816472692497618331993313

theorem tailTrace_7432554 : CollatzResearch.WordTrace tailWord_7432554 prefixEnd_7432554 3816472692497618331993313 := by
  unfold tailWord_7432554
  simp only [CollatzResearch.WordTrace]
  refine ⟨67771878778783428001968179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180725010076755808005248477 67771878778783428001968179)
  ·
    refine ⟨101657818168175142002952269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67771878778783428001968179 101657818168175142002952269)
    ·
      refine ⟨38121681813065678251107101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101657818168175142002952269 38121681813065678251107101)
      ·
        refine ⟨14295630679899629344165163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38121681813065678251107101 14295630679899629344165163)
        ·
          refine ⟨21443446019849444016247745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14295630679899629344165163 21443446019849444016247745)
          ·
            refine ⟨16082584514887083012185809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21443446019849444016247745 16082584514887083012185809)
            ·
              refine ⟨12061938386165312259139357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16082584514887083012185809 12061938386165312259139357)
              ·
                refine ⟨4523226894811992097177259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12061938386165312259139357 4523226894811992097177259)
                ·
                  refine ⟨6784840342217988145765889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4523226894811992097177259 6784840342217988145765889)
                  ·
                    refine ⟨5088630256663491109324417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6784840342217988145765889 5088630256663491109324417)
                    ·
                      refine ⟨3816472692497618331993313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088630256663491109324417 3816472692497618331993313)
                      ·
                        rfl

theorem cell23_7432554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_7432554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432554 prefixEnd_7432554 := by exact prefixLift 7432554
  have htrace : WordTrace (prefixWord ++ tailWord_7432554) baseStart_7432554 baseEnd_7432554 := by
    simpa [prefixWord, tailWord_7432554, baseEnd_7432554] using wordTrace_append hprefix tailTrace_7432554
  have hstable : (prefixWord ++ tailWord_7432554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432554).length < 2 ^ (prefixWord ++ tailWord_7432554).sum := by decide
  have hdescent : baseEnd_7432554 < baseStart_7432554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432559 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 4]
def baseStart_7432559 : Nat := 118140960795 + 7432559 * 2 ^ 59
def prefixEnd_7432559 : Nat := 4983230072969 + 3 ^ 40 * 7432559 * 2
def baseEnd_7432559 : Nat := 3816475259900890812430789

theorem tailTrace_7432559 : CollatzResearch.WordTrace tailWord_7432559 prefixEnd_7432559 3816475259900890812430789 := by
  unfold tailWord_7432559
  simp only [CollatzResearch.WordTrace]
  refine ⟨271087697480115597861804731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180725131653410398574536487 271087697480115597861804731)
  ·
    refine ⟨406631546220173396792707097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271087697480115597861804731 406631546220173396792707097)
    ·
      refine ⟨304973659665130047594530323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406631546220173396792707097 304973659665130047594530323)
      ·
        refine ⟨457460489497695071391795485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304973659665130047594530323 457460489497695071391795485)
        ·
          refine ⟨171547683561635651771923307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457460489497695071391795485 171547683561635651771923307)
          ·
            refine ⟨257321525342453477657884961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171547683561635651771923307 257321525342453477657884961)
            ·
              refine ⟨192991144006840108243413721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257321525342453477657884961 192991144006840108243413721)
              ·
                refine ⟨144743358005130081182560291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192991144006840108243413721 144743358005130081182560291)
                ·
                  refine ⟨217115037007695121773840437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144743358005130081182560291 217115037007695121773840437)
                  ·
                    refine ⟨20354534719471417666297541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 217115037007695121773840437 20354534719471417666297541)
                    ·
                      refine ⟨3816475259900890812430789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20354534719471417666297541 3816475259900890812430789)
                      ·
                        rfl

theorem cell23_7432559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_7432559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432559 prefixEnd_7432559 := by exact prefixLift 7432559
  have htrace : WordTrace (prefixWord ++ tailWord_7432559) baseStart_7432559 baseEnd_7432559 := by
    simpa [prefixWord, tailWord_7432559, baseEnd_7432559] using wordTrace_append hprefix tailTrace_7432559
  have hstable : (prefixWord ++ tailWord_7432559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432559).length < 2 ^ (prefixWord ++ tailWord_7432559).sum := by decide
  have hdescent : baseEnd_7432559 < baseStart_7432559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432563 : List Nat := [1, 1, 1, 2, 2, 1, 2, 7, 1, 3, 2]
def baseStart_7432563 : Nat := 118140960795 + 7432563 * 2 ^ 59
def prefixEnd_7432563 : Nat := 4983230072969 + 3 ^ 40 * 7432563 * 2
def baseEnd_7432563 : Nat := 3816477313823508796780771

theorem tailTrace_7432563 : CollatzResearch.WordTrace tailWord_7432563 prefixEnd_7432563 3816477313823508796780771 := by
  unfold tailWord_7432563
  simp only [CollatzResearch.WordTrace]
  refine ⟨271087843372101106544950343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180725228914734071029966895 271087843372101106544950343)
  ·
    refine ⟨406631765058151659817425515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271087843372101106544950343 406631765058151659817425515)
    ·
      refine ⟨609947647587227489726138273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406631765058151659817425515 609947647587227489726138273)
      ·
        refine ⟨457460735690420617294603705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609947647587227489726138273 457460735690420617294603705)
        ·
          refine ⟨343095551767815462970952779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457460735690420617294603705 343095551767815462970952779)
          ·
            refine ⟨514643327651723194456429169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343095551767815462970952779 514643327651723194456429169)
            ·
              refine ⟨385982495738792395842321877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514643327651723194456429169 385982495738792395842321877)
              ·
                refine ⟨9046464743877946777554419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 385982495738792395842321877 9046464743877946777554419)
                ·
                  refine ⟨13569697115816920166331629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9046464743877946777554419 13569697115816920166331629)
                  ·
                    refine ⟨5088636418431345062374361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13569697115816920166331629 5088636418431345062374361)
                    ·
                      refine ⟨3816477313823508796780771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088636418431345062374361 3816477313823508796780771)
                      ·
                        rfl

theorem cell23_7432563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 3, 2].length) (baseStart_7432563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432563 prefixEnd_7432563 := by exact prefixLift 7432563
  have htrace : WordTrace (prefixWord ++ tailWord_7432563) baseStart_7432563 baseEnd_7432563 := by
    simpa [prefixWord, tailWord_7432563, baseEnd_7432563] using wordTrace_append hprefix tailTrace_7432563
  have hstable : (prefixWord ++ tailWord_7432563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432563).length < 2 ^ (prefixWord ++ tailWord_7432563).sum := by decide
  have hdescent : baseEnd_7432563 < baseStart_7432563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432576 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 2, 8, 2]
def baseStart_7432576 : Nat := 118140960795 + 7432576 * 2 ^ 59
def prefixEnd_7432576 : Nat := 4983230072969 + 3 ^ 40 * 7432576 * 2
def baseEnd_7432576 : Nat := 3816483989072017245918211

theorem tailTrace_7432576 : CollatzResearch.WordTrace tailWord_7432576 prefixEnd_7432576 3816483989072017245918211 := by
  unfold tailWord_7432576
  simp only [CollatzResearch.WordTrace]
  refine ⟨135544158760527004882586791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180725545014036006510115721 135544158760527004882586791)
  ·
    refine ⟨203316238140790507323880187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135544158760527004882586791 203316238140790507323880187)
    ·
      refine ⟨304974357211185760985820281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203316238140790507323880187 304974357211185760985820281)
      ·
        refine ⟨228730767908389320739365211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304974357211185760985820281 228730767908389320739365211)
        ·
          refine ⟨343096151862583981109047817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228730767908389320739365211 343096151862583981109047817)
          ·
            refine ⟨257322113896937985831785863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343096151862583981109047817 257322113896937985831785863)
            ·
              refine ⟨385983170845406978747678795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257322113896937985831785863 385983170845406978747678795)
              ·
                refine ⟨578974756268110468121518193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385983170845406978747678795 578974756268110468121518193)
                ·
                  refine ⟨434231067201082851091138645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578974756268110468121518193 434231067201082851091138645)
                  ·
                    refine ⟨5088645318762689661224281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 434231067201082851091138645 5088645318762689661224281)
                    ·
                      refine ⟨3816483989072017245918211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088645318762689661224281 3816483989072017245918211)
                      ·
                        rfl

theorem cell23_7432576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 8, 2].length) (baseStart_7432576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432576 prefixEnd_7432576 := by exact prefixLift 7432576
  have htrace : WordTrace (prefixWord ++ tailWord_7432576) baseStart_7432576 baseEnd_7432576 := by
    simpa [prefixWord, tailWord_7432576, baseEnd_7432576] using wordTrace_append hprefix tailTrace_7432576
  have hstable : (prefixWord ++ tailWord_7432576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432576).length < 2 ^ (prefixWord ++ tailWord_7432576).sum := by decide
  have hdescent : baseEnd_7432576 < baseStart_7432576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432593 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 8, 2, 2]
def baseStart_7432593 : Nat := 118140960795 + 7432593 * 2 ^ 59
def prefixEnd_7432593 : Nat := 4983230072969 + 3 ^ 40 * 7432593 * 2
def baseEnd_7432593 : Nat := 3816492718243143679405633

theorem tailTrace_7432593 : CollatzResearch.WordTrace tailWord_7432593 prefixEnd_7432593 3816492718243143679405633 := by
  unfold tailWord_7432593
  simp only [CollatzResearch.WordTrace]
  refine ⟨271088937561992421668542433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180725958374661614445694955 271088937561992421668542433)
  ·
    refine ⟨203316703171494316251406825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271088937561992421668542433 203316703171494316251406825)
    ·
      refine ⟨152487527378620737188555119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203316703171494316251406825 152487527378620737188555119)
      ·
        refine ⟨228731291067931105782832679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152487527378620737188555119 228731291067931105782832679)
        ·
          refine ⟨343096936601896658674249019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228731291067931105782832679 343096936601896658674249019)
          ·
            refine ⟨514645404902844988011373529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343096936601896658674249019 514645404902844988011373529)
            ·
              refine ⟨385984053677133741008530147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514645404902844988011373529 385984053677133741008530147)
              ·
                refine ⟨578976080515700611512795221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385984053677133741008530147 578976080515700611512795221)
                ·
                  refine ⟨6784875943543366541165569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 578976080515700611512795221 6784875943543366541165569)
                  ·
                    refine ⟨5088656957657524905874177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6784875943543366541165569 5088656957657524905874177)
                    ·
                      refine ⟨3816492718243143679405633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088656957657524905874177 3816492718243143679405633)
                      ·
                        rfl

theorem cell23_7432593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 2, 2].length) (baseStart_7432593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432593 prefixEnd_7432593 := by exact prefixLift 7432593
  have htrace : WordTrace (prefixWord ++ tailWord_7432593) baseStart_7432593 baseEnd_7432593 := by
    simpa [prefixWord, tailWord_7432593, baseEnd_7432593] using wordTrace_append hprefix tailTrace_7432593
  have hstable : (prefixWord ++ tailWord_7432593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432593).length < 2 ^ (prefixWord ++ tailWord_7432593).sum := by decide
  have hdescent : baseEnd_7432593 < baseStart_7432593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432610 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_7432610 : Nat := 118140960795 + 7432610 * 2 ^ 59
def prefixEnd_7432610 : Nat := 4983230072969 + 3 ^ 40 * 7432610 * 2
def baseEnd_7432610 : Nat := 3816501447414270112893055

theorem tailTrace_7432610 : CollatzResearch.WordTrace tailWord_7432610 prefixEnd_7432610 3816501447414270112893055 := by
  unfold tailWord_7432610
  simp only [CollatzResearch.WordTrace]
  refine ⟨67772389400732708392977821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180726371735287222381274189 67772389400732708392977821)
  ·
    refine ⟨25414646025274765647366683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67772389400732708392977821 25414646025274765647366683)
    ·
      refine ⟨38121969037912148471050025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25414646025274765647366683 38121969037912148471050025)
      ·
        refine ⟨28591476778434111353287519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38121969037912148471050025 28591476778434111353287519)
        ·
          refine ⟨42887215167651167029931279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28591476778434111353287519 42887215167651167029931279)
          ·
            refine ⟨64330822751476750544896919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42887215167651167029931279 64330822751476750544896919)
            ·
              refine ⟨96496234127215125817345379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64330822751476750544896919 96496234127215125817345379)
              ·
                refine ⟨144744351190822688726018069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96496234127215125817345379 144744351190822688726018069)
                ·
                  refine ⟨6784891462069813534032097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144744351190822688726018069 6784891462069813534032097)
                  ·
                    refine ⟨5088668596552360150524073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6784891462069813534032097 5088668596552360150524073)
                    ·
                      refine ⟨3816501447414270112893055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088668596552360150524073 3816501447414270112893055)
                      ·
                        rfl

theorem cell23_7432610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_7432610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432610 prefixEnd_7432610 := by exact prefixLift 7432610
  have htrace : WordTrace (prefixWord ++ tailWord_7432610) baseStart_7432610 baseEnd_7432610 := by
    simpa [prefixWord, tailWord_7432610, baseEnd_7432610] using wordTrace_append hprefix tailTrace_7432610
  have hstable : (prefixWord ++ tailWord_7432610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432610).length < 2 ^ (prefixWord ++ tailWord_7432610).sum := by decide
  have hdescent : baseEnd_7432610 < baseStart_7432610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432633 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 7]
def baseStart_7432633 : Nat := 118140960795 + 7432633 * 2 ^ 59
def prefixEnd_7432633 : Nat := 4983230072969 + 3 ^ 40 * 7432633 * 2
def baseEnd_7432633 : Nat := 424057028607702613656161

theorem tailTrace_7432633 : CollatzResearch.WordTrace tailWord_7432633 prefixEnd_7432633 424057028607702613656161 := by
  unfold tailWord_7432633
  simp only [CollatzResearch.WordTrace]
  refine ⟨271090396481847508499998553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180726930987898338999999035 271090396481847508499998553)
  ·
    refine ⟨203317797361385631374998915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271090396481847508499998553 203317797361385631374998915)
    ·
      refine ⟨304976696042078447062498373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203317797361385631374998915 304976696042078447062498373)
      ·
        refine ⟨57183130507889708824218445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304976696042078447062498373 57183130507889708824218445)
        ·
          refine ⟨21443673940458640809081917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57183130507889708824218445 21443673940458640809081917)
          ·
            refine ⟨8041377727671990303405719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21443673940458640809081917 8041377727671990303405719)
            ·
              refine ⟨12062066591507985455108579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8041377727671990303405719 12062066591507985455108579)
              ·
                refine ⟨18093099887261978182662869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12062066591507985455108579 18093099887261978182662869)
                ·
                  refine ⟨424057028607702613656161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18093099887261978182662869 424057028607702613656161)
                  ·
                    rfl

theorem cell23_7432633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 7].length) (baseStart_7432633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432633 prefixEnd_7432633 := by exact prefixLift 7432633
  have htrace : WordTrace (prefixWord ++ tailWord_7432633) baseStart_7432633 baseEnd_7432633 := by
    simpa [prefixWord, tailWord_7432633, baseEnd_7432633] using wordTrace_append hprefix tailTrace_7432633
  have hstable : (prefixWord ++ tailWord_7432633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432633).length < 2 ^ (prefixWord ++ tailWord_7432633).sum := by decide
  have hdescent : baseEnd_7432633 < baseStart_7432633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432644 : List Nat := [2, 3, 3, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_7432644 : Nat := 118140960795 + 7432644 * 2 ^ 59
def prefixEnd_7432644 : Nat := 4983230072969 + 3 ^ 40 * 7432644 * 2
def baseEnd_7432644 : Nat := 3816518905756522979867899

theorem tailTrace_7432644 : CollatzResearch.WordTrace tailWord_7432644 prefixEnd_7432644 3816518905756522979867899 := by
  unfold tailWord_7432644
  simp only [CollatzResearch.WordTrace]
  refine ⟨135545398842403828689324493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180727198456538438252432657 135545398842403828689324493)
  ·
    refine ⟨50829524565901435758496685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135545398842403828689324493 50829524565901435758496685)
    ·
      refine ⟨19061071712213038409436257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50829524565901435758496685 19061071712213038409436257)
      ·
        refine ⟨14295803784159778807077193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19061071712213038409436257 14295803784159778807077193)
        ·
          refine ⟨10721852838119834105307895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14295803784159778807077193 10721852838119834105307895)
          ·
            refine ⟨16082779257179751157961843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10721852838119834105307895 16082779257179751157961843)
            ·
              refine ⟨24124168885769626736942765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16082779257179751157961843 24124168885769626736942765)
              ·
                refine ⟨9046563332163610026353537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24124168885769626736942765 9046563332163610026353537)
                ·
                  refine ⟨6784922499122707519765153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9046563332163610026353537 6784922499122707519765153)
                  ·
                    refine ⟨5088691874342030639823865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6784922499122707519765153 5088691874342030639823865)
                    ·
                      refine ⟨3816518905756522979867899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088691874342030639823865 3816518905756522979867899)
                      ·
                        rfl

theorem cell23_7432644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_7432644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432644 prefixEnd_7432644 := by exact prefixLift 7432644
  have htrace : WordTrace (prefixWord ++ tailWord_7432644) baseStart_7432644 baseEnd_7432644 := by
    simpa [prefixWord, tailWord_7432644, baseEnd_7432644] using wordTrace_append hprefix tailTrace_7432644
  have hstable : (prefixWord ++ tailWord_7432644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432644).length < 2 ^ (prefixWord ++ tailWord_7432644).sum := by decide
  have hdescent : baseEnd_7432644 < baseStart_7432644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432683 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 2, 4, 2]
def baseStart_7432683 : Nat := 118140960795 + 7432683 * 2 ^ 59
def prefixEnd_7432683 : Nat := 4983230072969 + 3 ^ 40 * 7432683 * 2
def baseEnd_7432683 : Nat := 3816538931502048327280219

theorem tailTrace_7432683 : CollatzResearch.WordTrace tailWord_7432683 prefixEnd_7432683 3816538931502048327280219 := by
  unfold tailWord_7432683
  simp only [CollatzResearch.WordTrace]
  refine ⟨271092220131666367039318703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180728146754444244692879135 271092220131666367039318703)
  ·
    refine ⟨406638330197499550558978055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271092220131666367039318703 406638330197499550558978055)
    ·
      refine ⟨609957495296249325838467083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406638330197499550558978055 609957495296249325838467083)
      ·
        refine ⟨914936242944373988757700625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609957495296249325838467083 914936242944373988757700625)
        ·
          refine ⟨686202182208280491568275469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 914936242944373988757700625 686202182208280491568275469)
          ·
            refine ⟨257325818328105184338103301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 686202182208280491568275469 257325818328105184338103301)
            ·
              refine ⟨48248590936519722063394369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257325818328105184338103301 48248590936519722063394369)
              ·
                refine ⟨36186443202389791547545777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48248590936519722063394369 36186443202389791547545777)
                ·
                  refine ⟨27139832401792343660659333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36186443202389791547545777 27139832401792343660659333)
                  ·
                    refine ⟨5088718575336064436373625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27139832401792343660659333 5088718575336064436373625)
                    ·
                      refine ⟨3816538931502048327280219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088718575336064436373625 3816538931502048327280219)
                      ·
                        rfl

theorem cell23_7432683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 4, 2].length) (baseStart_7432683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432683 prefixEnd_7432683 := by exact prefixLift 7432683
  have htrace : WordTrace (prefixWord ++ tailWord_7432683) baseStart_7432683 baseEnd_7432683 := by
    simpa [prefixWord, tailWord_7432683, baseEnd_7432683] using wordTrace_append hprefix tailTrace_7432683
  have hstable : (prefixWord ++ tailWord_7432683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432683).length < 2 ^ (prefixWord ++ tailWord_7432683).sum := by decide
  have hdescent : baseEnd_7432683 < baseStart_7432683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432717 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_7432717 : Nat := 118140960795 + 7432717 * 2 ^ 59
def prefixEnd_7432717 : Nat := 4983230072969 + 3 ^ 40 * 7432717 * 2
def baseEnd_7432717 : Nat := 3816556389844301194255063

theorem tailTrace_7432717 : CollatzResearch.WordTrace tailWord_7432717 prefixEnd_7432717 3816556389844301194255063 := by
  unfold tailWord_7432717
  simp only [CollatzResearch.WordTrace]
  refine ⟨271093460213543190846056405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180728973475695460564037603 271093460213543190846056405)
  ·
    refine ⟨6353752973754918535454447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 271093460213543190846056405 6353752973754918535454447)
    ·
      refine ⟨9530629460632377803181671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6353752973754918535454447 9530629460632377803181671)
      ·
        refine ⟨14295944190948566704772507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9530629460632377803181671 14295944190948566704772507)
        ·
          refine ⟨21443916286422850057158761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14295944190948566704772507 21443916286422850057158761)
          ·
            refine ⟨16082937214817137542869071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21443916286422850057158761 16082937214817137542869071)
            ·
              refine ⟨24124405822225706314303607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16082937214817137542869071 24124405822225706314303607)
              ·
                refine ⟨36186608733338559471455411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24124405822225706314303607 36186608733338559471455411)
                ·
                  refine ⟨54279913100007839207183117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36186608733338559471455411 54279913100007839207183117)
                  ·
                    refine ⟨20354967412502939702693669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54279913100007839207183117 20354967412502939702693669)
                    ·
                      refine ⟨3816556389844301194255063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20354967412502939702693669 3816556389844301194255063)
                      ·
                        rfl

theorem cell23_7432717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_7432717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432717 prefixEnd_7432717 := by exact prefixLift 7432717
  have htrace : WordTrace (prefixWord ++ tailWord_7432717) baseStart_7432717 baseEnd_7432717 := by
    simpa [prefixWord, tailWord_7432717, baseEnd_7432717] using wordTrace_append hprefix tailTrace_7432717
  have hstable : (prefixWord ++ tailWord_7432717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432717).length < 2 ^ (prefixWord ++ tailWord_7432717).sum := by decide
  have hdescent : baseEnd_7432717 < baseStart_7432717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432740 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 8]
def baseStart_7432740 : Nat := 118140960795 + 7432740 * 2 ^ 59
def prefixEnd_7432740 : Nat := 4983230072969 + 3 ^ 40 * 7432740 * 2
def baseEnd_7432740 : Nat := 424063133322150511585273

theorem tailTrace_7432740 : CollatzResearch.WordTrace tailWord_7432740 prefixEnd_7432740 424063133322150511585273 := by
  unfold tailWord_7432740
  simp only [CollatzResearch.WordTrace]
  refine ⟨135547149546229932887071837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180729532728306577182762449 135547149546229932887071837)
  ·
    refine ⟨50830181079836224832651939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135547149546229932887071837 50830181079836224832651939)
    ·
      refine ⟨76245271619754337248977909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50830181079836224832651939 76245271619754337248977909)
      ·
        refine ⟨7147994214351969117091679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76245271619754337248977909 7147994214351969117091679)
        ·
          refine ⟨10721991321527953675637519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7147994214351969117091679 10721991321527953675637519)
          ·
            refine ⟨16082986982291930513456279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10721991321527953675637519 16082986982291930513456279)
            ·
              refine ⟨24124480473437895770184419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16082986982291930513456279 24124480473437895770184419)
              ·
                refine ⟨36186720710156843655276629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24124480473437895770184419 36186720710156843655276629)
                ·
                  refine ⟨424063133322150511585273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36186720710156843655276629 424063133322150511585273)
                  ·
                    rfl

theorem cell23_7432740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_7432740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432740 prefixEnd_7432740 := by exact prefixLift 7432740
  have htrace : WordTrace (prefixWord ++ tailWord_7432740) baseStart_7432740 baseEnd_7432740 := by
    simpa [prefixWord, tailWord_7432740, baseEnd_7432740] using wordTrace_append hprefix tailTrace_7432740
  have hstable : (prefixWord ++ tailWord_7432740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432740).length < 2 ^ (prefixWord ++ tailWord_7432740).sum := by decide
  have hdescent : baseEnd_7432740 < baseStart_7432740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432783 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 4, 4]
def baseStart_7432783 : Nat := 118140960795 + 7432783 * 2 ^ 59
def prefixEnd_7432783 : Nat := 4983230072969 + 3 ^ 40 * 7432783 * 2
def baseEnd_7432783 : Nat := 1272196759855832645343253

theorem tailTrace_7432783 : CollatzResearch.WordTrace tailWord_7432783 prefixEnd_7432783 1272196759855832645343253 := by
  unfold tailWord_7432783
  simp only [CollatzResearch.WordTrace]
  refine ⟨271095867431304084117959003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180730578287536056078639335 271095867431304084117959003)
  ·
    refine ⟨406643801146956126176938505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271095867431304084117959003 406643801146956126176938505)
    ·
      refine ⟨304982850860217094632703879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406643801146956126176938505 304982850860217094632703879)
      ·
        refine ⟨457474276290325641949055819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304982850860217094632703879 457474276290325641949055819)
        ·
          refine ⟨686211414435488462923583729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457474276290325641949055819 686211414435488462923583729)
          ·
            refine ⟨514658560826616347192687797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686211414435488462923583729 514658560826616347192687797)
            ·
              refine ⟨48249240077495282549314481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 514658560826616347192687797 48249240077495282549314481)
              ·
                refine ⟨36186930058121461911985861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48249240077495282549314481 36186930058121461911985861)
                ·
                  refine ⟨6785049385897774108497349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36186930058121461911985861 6785049385897774108497349)
                  ·
                    refine ⟨1272196759855832645343253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6785049385897774108497349 1272196759855832645343253)
                    ·
                      rfl

theorem cell23_7432783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 4].length) (baseStart_7432783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432783 prefixEnd_7432783 := by exact prefixLift 7432783
  have htrace : WordTrace (prefixWord ++ tailWord_7432783) baseStart_7432783 baseEnd_7432783 := by
    simpa [prefixWord, tailWord_7432783, baseEnd_7432783] using wordTrace_append hprefix tailTrace_7432783
  have hstable : (prefixWord ++ tailWord_7432783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432783).length < 2 ^ (prefixWord ++ tailWord_7432783).sum := by decide
  have hdescent : baseEnd_7432783 < baseStart_7432783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432793 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 7, 2, 3]
def baseStart_7432793 : Nat := 118140960795 + 7432793 * 2 ^ 59
def prefixEnd_7432793 : Nat := 4983230072969 + 3 ^ 40 * 7432793 * 2
def baseEnd_7432793 : Nat := 3816595414374042896904713

theorem tailTrace_7432793 : CollatzResearch.WordTrace tailWord_7432793 prefixEnd_7432793 3816595414374042896904713 := by
  unfold tailWord_7432793
  simp only [CollatzResearch.WordTrace]
  refine ⟨271096232161267855825823033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180730821440845237217215355 271096232161267855825823033)
  ·
    refine ⟨203322174120950891869367275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271096232161267855825823033 203322174120950891869367275)
    ·
      refine ⟨304983261181426337804050913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203322174120950891869367275 304983261181426337804050913)
      ·
        refine ⟨228737445886069753353038185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304983261181426337804050913 228737445886069753353038185)
        ·
          refine ⟨171553084414552315014778639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228737445886069753353038185 171553084414552315014778639)
          ·
            refine ⟨257329626621828472522167959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171553084414552315014778639 257329626621828472522167959)
            ·
              refine ⟨385994439932742708783251939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257329626621828472522167959 385994439932742708783251939)
              ·
                refine ⟨578991659899114063174877909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385994439932742708783251939 578991659899114063174877909)
                ·
                  refine ⟨13570117028885485855661201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 578991659899114063174877909 13570117028885485855661201)
                  ·
                    refine ⟨10177587771664114391745901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13570117028885485855661201 10177587771664114391745901)
                    ·
                      refine ⟨3816595414374042896904713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10177587771664114391745901 3816595414374042896904713)
                      ·
                        rfl

theorem cell23_7432793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_7432793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432793 prefixEnd_7432793 := by exact prefixLift 7432793
  have htrace : WordTrace (prefixWord ++ tailWord_7432793) baseStart_7432793 baseEnd_7432793 := by
    simpa [prefixWord, tailWord_7432793, baseEnd_7432793] using wordTrace_append hprefix tailTrace_7432793
  have hstable : (prefixWord ++ tailWord_7432793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432793).length < 2 ^ (prefixWord ++ tailWord_7432793).sum := by decide
  have hdescent : baseEnd_7432793 < baseStart_7432793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432810 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_7432810 : Nat := 118140960795 + 7432810 * 2 ^ 59
def prefixEnd_7432810 : Nat := 4983230072969 + 3 ^ 40 * 7432810 * 2
def baseEnd_7432810 : Nat := 3816604143545169330392135

theorem tailTrace_7432810 : CollatzResearch.WordTrace tailWord_7432810 prefixEnd_7432810 3816604143545169330392135 := by
  unfold tailWord_7432810
  simp only [CollatzResearch.WordTrace]
  refine ⟨67774213050551566932297971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180731234801470845152794589 67774213050551566932297971)
  ·
    refine ⟨101661319575827350398446957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67774213050551566932297971 101661319575827350398446957)
    ·
      refine ⟨38122994840935256399417609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101661319575827350398446957 38122994840935256399417609)
      ·
        refine ⟨28592246130701442299563207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38122994840935256399417609 28592246130701442299563207)
        ·
          refine ⟨42888369196052163449344811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28592246130701442299563207 42888369196052163449344811)
          ·
            refine ⟨64332553794078245174017217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42888369196052163449344811 64332553794078245174017217)
            ·
              refine ⟨48249415345558683880512913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64332553794078245174017217 48249415345558683880512913)
              ·
                refine ⟨36187061509169012910384685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48249415345558683880512913 36187061509169012910384685)
                ·
                  refine ⟨13570148065938379841394257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36187061509169012910384685 13570148065938379841394257)
                  ·
                    refine ⟨10177611049453784881045693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13570148065938379841394257 10177611049453784881045693)
                    ·
                      refine ⟨3816604143545169330392135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10177611049453784881045693 3816604143545169330392135)
                      ·
                        rfl

theorem cell23_7432810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_7432810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432810 prefixEnd_7432810 := by exact prefixLift 7432810
  have htrace : WordTrace (prefixWord ++ tailWord_7432810) baseStart_7432810 baseEnd_7432810 := by
    simpa [prefixWord, tailWord_7432810, baseEnd_7432810] using wordTrace_append hprefix tailTrace_7432810
  have hstable : (prefixWord ++ tailWord_7432810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432810).length < 2 ^ (prefixWord ++ tailWord_7432810).sum := by decide
  have hdescent : baseEnd_7432810 < baseStart_7432810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432813 : List Nat := [1, 5, 1, 1, 3, 1, 1, 10]
def baseStart_7432813 : Nat := 118140960795 + 7432813 * 2 ^ 59
def prefixEnd_7432813 : Nat := 4983230072969 + 3 ^ 40 * 7432813 * 2
def baseEnd_7432813 : Nat := 141355766073597511802023

theorem tailTrace_7432813 : CollatzResearch.WordTrace tailWord_7432813 prefixEnd_7432813 141355766073597511802023 := by
  unfold tailWord_7432813
  simp only [CollatzResearch.WordTrace]
  refine ⟨271096961621195399241551093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180731307747463599494367395 271096961621195399241551093)
  ·
    refine ⟨25415340151987068678895415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271096961621195399241551093 25415340151987068678895415)
    ·
      refine ⟨38123010227980603018343123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25415340151987068678895415 38123010227980603018343123)
      ·
        refine ⟨57184515341970904527514685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38123010227980603018343123 57184515341970904527514685)
        ·
          refine ⟨21444193253239089197818007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57184515341970904527514685 21444193253239089197818007)
          ·
            refine ⟨32166289879858633796727011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21444193253239089197818007 32166289879858633796727011)
            ·
              refine ⟨48249434819787950695090517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32166289879858633796727011 48249434819787950695090517)
              ·
                refine ⟨141355766073597511802023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48249434819787950695090517 141355766073597511802023)
                ·
                  rfl

theorem cell23_7432813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 10].length) (baseStart_7432813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432813 prefixEnd_7432813 := by exact prefixLift 7432813
  have htrace : WordTrace (prefixWord ++ tailWord_7432813) baseStart_7432813 baseEnd_7432813 := by
    simpa [prefixWord, tailWord_7432813, baseEnd_7432813] using wordTrace_append hprefix tailTrace_7432813
  have hstable : (prefixWord ++ tailWord_7432813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432813).length < 2 ^ (prefixWord ++ tailWord_7432813).sum := by decide
  have hdescent : baseEnd_7432813 < baseStart_7432813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432857 : List Nat := [1, 2, 1, 2, 1, 2, 6, 2, 2, 1, 3]
def baseStart_7432857 : Nat := 118140960795 + 7432857 * 2 ^ 59
def prefixEnd_7432857 : Nat := 4983230072969 + 3 ^ 40 * 7432857 * 2
def baseEnd_7432857 : Nat := 3816628277135930646504419

theorem tailTrace_7432857 : CollatzResearch.WordTrace tailWord_7432857 prefixEnd_7432857 3816628277135930646504419 := by
  unfold tailWord_7432857
  simp only [CollatzResearch.WordTrace]
  refine ⟨271098566433035994756152825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180732377622023996504101883 271098566433035994756152825)
  ·
    refine ⟨203323924824776996067114619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271098566433035994756152825 203323924824776996067114619)
    ·
      refine ⟨304985887237165494100671929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203323924824776996067114619 304985887237165494100671929)
      ·
        refine ⟨228739415427874120575503947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304985887237165494100671929 228739415427874120575503947)
        ·
          refine ⟨343109123141811180863255921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228739415427874120575503947 343109123141811180863255921)
          ·
            refine ⟨257331842356358385647441941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343109123141811180863255921 257331842356358385647441941)
            ·
              refine ⟨12062430110454299327223841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 257331842356358385647441941 12062430110454299327223841)
              ·
                refine ⟨9046822582840724495417881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12062430110454299327223841 9046822582840724495417881)
                ·
                  refine ⟨6785116937130543371563411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9046822582840724495417881 6785116937130543371563411)
                  ·
                    refine ⟨10177675405695815057345117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6785116937130543371563411 10177675405695815057345117)
                    ·
                      refine ⟨3816628277135930646504419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10177675405695815057345117 3816628277135930646504419)
                      ·
                        rfl

theorem cell23_7432857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_7432857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432857 prefixEnd_7432857 := by exact prefixLift 7432857
  have htrace : WordTrace (prefixWord ++ tailWord_7432857) baseStart_7432857 baseEnd_7432857 := by
    simpa [prefixWord, tailWord_7432857, baseEnd_7432857] using wordTrace_append hprefix tailTrace_7432857
  have hstable : (prefixWord ++ tailWord_7432857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432857).length < 2 ^ (prefixWord ++ tailWord_7432857).sum := by decide
  have hdescent : baseEnd_7432857 < baseStart_7432857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432858 : List Nat := [3, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2]
def baseStart_7432858 : Nat := 118140960795 + 7432858 * 2 ^ 59
def prefixEnd_7432858 : Nat := 4983230072969 + 3 ^ 40 * 7432858 * 2
def baseEnd_7432858 : Nat := 3816628790616585142591915

theorem tailTrace_7432858 : CollatzResearch.WordTrace tailWord_7432858 prefixEnd_7432858 3816628790616585142591915 := by
  unfold tailWord_7432858
  simp only [CollatzResearch.WordTrace]
  refine ⟨67774650726508092981734807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180732401937354914617959485 67774650726508092981734807)
  ·
    refine ⟨101661976089762139472602211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67774650726508092981734807 101661976089762139472602211)
    ·
      refine ⟨152492964134643209208903317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101661976089762139472602211 152492964134643209208903317)
      ·
        refine ⟨7148107693811400431667343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152492964134643209208903317 7148107693811400431667343)
        ·
          refine ⟨10722161540717100647501015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7148107693811400431667343 10722161540717100647501015)
          ·
            refine ⟨16083242311075650971251523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10722161540717100647501015 16083242311075650971251523)
            ·
              refine ⟨24124863466613476456877285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16083242311075650971251523 24124863466613476456877285)
              ·
                refine ⟨4523411899990026835664491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24124863466613476456877285 4523411899990026835664491)
                ·
                  refine ⟨6785117849985040253496737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4523411899990026835664491 6785117849985040253496737)
                  ·
                    refine ⟨5088838387488780190122553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6785117849985040253496737 5088838387488780190122553)
                    ·
                      refine ⟨3816628790616585142591915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088838387488780190122553 3816628790616585142591915)
                      ·
                        rfl

theorem cell23_7432858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_7432858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432858 prefixEnd_7432858 := by exact prefixLift 7432858
  have htrace : WordTrace (prefixWord ++ tailWord_7432858) baseStart_7432858 baseEnd_7432858 := by
    simpa [prefixWord, tailWord_7432858, baseEnd_7432858] using wordTrace_append hprefix tailTrace_7432858
  have hstable : (prefixWord ++ tailWord_7432858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432858).length < 2 ^ (prefixWord ++ tailWord_7432858).sum := by decide
  have hdescent : baseEnd_7432858 < baseStart_7432858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432910 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_7432910 : Nat := 118140960795 + 7432910 * 2 ^ 59
def prefixEnd_7432910 : Nat := 4983230072969 + 3 ^ 40 * 7432910 * 2
def baseEnd_7432910 : Nat := 3816655491610618939141675

theorem tailTrace_7432910 : CollatzResearch.WordTrace tailWord_7432910 prefixEnd_7432910 3816655491610618939141675 := by
  unfold tailWord_7432910
  simp only [CollatzResearch.WordTrace]
  refine ⟨33887562437730498100979023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180733666334562656538554789 33887562437730498100979023)
  ·
    refine ⟨50831343656595747151468535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33887562437730498100979023 50831343656595747151468535)
    ·
      refine ⟨76247015484893620727202803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50831343656595747151468535 76247015484893620727202803)
      ·
        refine ⟨114370523227340431090804205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76247015484893620727202803 114370523227340431090804205)
        ·
          refine ⟨42888946210252661659051577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114370523227340431090804205 42888946210252661659051577)
          ·
            refine ⟨32166709657689496244288683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42888946210252661659051577 32166709657689496244288683)
            ·
              refine ⟨48250064486534244366433025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32166709657689496244288683 48250064486534244366433025)
              ·
                refine ⟨36187548364900683274824769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48250064486534244366433025 36187548364900683274824769)
                ·
                  refine ⟨27140661273675512456118577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36187548364900683274824769 27140661273675512456118577)
                  ·
                    refine ⟨20355495955256634342088933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27140661273675512456118577 20355495955256634342088933)
                    ·
                      refine ⟨3816655491610618939141675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20355495955256634342088933 3816655491610618939141675)
                      ·
                        rfl

theorem cell23_7432910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_7432910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432910 prefixEnd_7432910 := by exact prefixLift 7432910
  have htrace : WordTrace (prefixWord ++ tailWord_7432910) baseStart_7432910 baseEnd_7432910 := by
    simpa [prefixWord, tailWord_7432910, baseEnd_7432910] using wordTrace_append hprefix tailTrace_7432910
  have hstable : (prefixWord ++ tailWord_7432910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432910).length < 2 ^ (prefixWord ++ tailWord_7432910).sum := by decide
  have hdescent : baseEnd_7432910 < baseStart_7432910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432920 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 7]
def baseStart_7432920 : Nat := 118140960795 + 7432920 * 2 ^ 59
def prefixEnd_7432920 : Nat := 4983230072969 + 3 ^ 40 * 7432920 * 2
def baseEnd_7432920 : Nat := 424073402935240433335181

theorem tailTrace_7432920 : CollatzResearch.WordTrace tailWord_7432920 prefixEnd_7432920 424073402935240433335181 := by
  unfold tailWord_7432920
  simp only [CollatzResearch.WordTrace]
  refine ⟨135550432115903878257848107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180733909487871837677130809 135550432115903878257848107)
  ·
    refine ⟨203325648173855817386772161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135550432115903878257848107 203325648173855817386772161)
    ·
      refine ⟨152494236130391863040079121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203325648173855817386772161 152494236130391863040079121)
      ·
        refine ⟨114370677097793897280059341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152494236130391863040079121 114370677097793897280059341)
        ·
          refine ⟨42889003911672711480022253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114370677097793897280059341 42889003911672711480022253)
          ·
            refine ⟨16083376466877266805008345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42889003911672711480022253 16083376466877266805008345)
            ·
              refine ⟨12062532350157950103756259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16083376466877266805008345 12062532350157950103756259)
              ·
                refine ⟨18093798525236925155634389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12062532350157950103756259 18093798525236925155634389)
                ·
                  refine ⟨424073402935240433335181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18093798525236925155634389 424073402935240433335181)
                  ·
                    rfl

theorem cell23_7432920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 7].length) (baseStart_7432920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432920 prefixEnd_7432920 := by exact prefixLift 7432920
  have htrace : WordTrace (prefixWord ++ tailWord_7432920) baseStart_7432920 baseEnd_7432920 := by
    simpa [prefixWord, tailWord_7432920, baseEnd_7432920] using wordTrace_append hprefix tailTrace_7432920
  have hstable : (prefixWord ++ tailWord_7432920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432920).length < 2 ^ (prefixWord ++ tailWord_7432920).sum := by decide
  have hdescent : baseEnd_7432920 < baseStart_7432920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432950 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_7432950 : Nat := 118140960795 + 7432950 * 2 ^ 59
def prefixEnd_7432950 : Nat := 4983230072969 + 3 ^ 40 * 7432950 * 2
def baseEnd_7432950 : Nat := 1272225343612266260880497

theorem tailTrace_7432950 : CollatzResearch.WordTrace tailWord_7432950 prefixEnd_7432950 1272225343612266260880497 := by
  unfold tailWord_7432950
  simp only [CollatzResearch.WordTrace]
  refine ⟨16943872401356191977455519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180734638947799381092858869 16943872401356191977455519)
  ·
    refine ⟨25415808602034287966183279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16943872401356191977455519 25415808602034287966183279)
    ·
      refine ⟨38123712903051431949274919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25415808602034287966183279 38123712903051431949274919)
      ·
        refine ⟨57185569354577147923912379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38123712903051431949274919 57185569354577147923912379)
        ·
          refine ⟨85778354031865721885868569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57185569354577147923912379 85778354031865721885868569)
          ·
            refine ⟨64333765523899291414401427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85778354031865721885868569 64333765523899291414401427)
            ·
              refine ⟨96500648285848937121602141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64333765523899291414401427 96500648285848937121602141)
              ·
                refine ⟨36187743107193351420600803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96500648285848937121602141 36187743107193351420600803)
                ·
                  refine ⟨54281614660790027130901205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36187743107193351420600803 54281614660790027130901205)
                  ·
                    refine ⟨1272225343612266260880497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54281614660790027130901205 1272225343612266260880497)
                    ·
                      rfl

theorem cell23_7432950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_7432950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432950 prefixEnd_7432950 := by exact prefixLift 7432950
  have htrace : WordTrace (prefixWord ++ tailWord_7432950) baseStart_7432950 baseEnd_7432950 := by
    simpa [prefixWord, tailWord_7432950, baseEnd_7432950] using wordTrace_append hprefix tailTrace_7432950
  have hstable : (prefixWord ++ tailWord_7432950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432950).length < 2 ^ (prefixWord ++ tailWord_7432950).sum := by decide
  have hdescent : baseEnd_7432950 < baseStart_7432950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7432967 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 2, 5]
def baseStart_7432967 : Nat := 118140960795 + 7432967 * 2 ^ 59
def prefixEnd_7432967 : Nat := 4983230072969 + 3 ^ 40 * 7432967 * 2
def baseEnd_7432967 : Nat := 1272228253335975072042971

theorem tailTrace_7432967 : CollatzResearch.WordTrace tailWord_7432967 prefixEnd_7432967 1272228253335975072042971 := by
  unfold tailWord_7432967
  simp only [CollatzResearch.WordTrace]
  refine ⟨271102578462637483542657155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180735052308424989028438103 271102578462637483542657155)
  ·
    refine ⟨406653867693956225313985733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271102578462637483542657155 406653867693956225313985733)
    ·
      refine ⟨76247600192616792246372325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 406653867693956225313985733 76247600192616792246372325)
      ·
        refine ⟨14296425036115648546194811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76247600192616792246372325 14296425036115648546194811)
        ·
          refine ⟨21444637554173472819292217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14296425036115648546194811 21444637554173472819292217)
          ·
            refine ⟨16083478165630104614469163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21444637554173472819292217 16083478165630104614469163)
            ·
              refine ⟨24125217248445156921703745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16083478165630104614469163 24125217248445156921703745)
              ·
                refine ⟨18093912936333867691277809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24125217248445156921703745 18093912936333867691277809)
                ·
                  refine ⟨13570434702250400768458357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18093912936333867691277809 13570434702250400768458357)
                  ·
                    refine ⟨1272228253335975072042971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13570434702250400768458357 1272228253335975072042971)
                    ·
                      rfl

theorem cell23_7432967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_7432967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7432967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7432967 prefixEnd_7432967 := by exact prefixLift 7432967
  have htrace : WordTrace (prefixWord ++ tailWord_7432967) baseStart_7432967 baseEnd_7432967 := by
    simpa [prefixWord, tailWord_7432967, baseEnd_7432967] using wordTrace_append hprefix tailTrace_7432967
  have hstable : (prefixWord ++ tailWord_7432967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7432967).length < 2 ^ (prefixWord ++ tailWord_7432967).sum := by decide
  have hdescent : baseEnd_7432967 < baseStart_7432967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7432967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433040 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 3, 5]
def baseStart_7433040 : Nat := 118140960795 + 7433040 * 2 ^ 59
def prefixEnd_7433040 : Nat := 4983230072969 + 3 ^ 40 * 7433040 * 2
def baseEnd_7433040 : Nat := 1272240748031901143505359

theorem tailTrace_7433040 : CollatzResearch.WordTrace tailWord_7433040 prefixEnd_7433040 1272240748031901143505359 := by
  unfold tailWord_7433040
  simp only [CollatzResearch.WordTrace]
  refine ⟨135552620495686508505032287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180736827327582011340043049 135552620495686508505032287)
  ·
    refine ⟨203328930743529762757548431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135552620495686508505032287 203328930743529762757548431)
    ·
      refine ⟨304993396115294644136322647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203328930743529762757548431 304993396115294644136322647)
      ·
        refine ⟨457490094172941966204483971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304993396115294644136322647 457490094172941966204483971)
        ·
          refine ⟨686235141259412949306725957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457490094172941966204483971 686235141259412949306725957)
          ·
            refine ⟨128669088986139927995011117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 686235141259412949306725957 128669088986139927995011117)
            ·
              refine ⟨48250908369802472998129169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128669088986139927995011117 48250908369802472998129169)
              ·
                refine ⟨36188181277351854748596877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48250908369802472998129169 36188181277351854748596877)
                ·
                  refine ⟨13570567979006945530723829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36188181277351854748596877 13570567979006945530723829)
                  ·
                    refine ⟨1272240748031901143505359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13570567979006945530723829 1272240748031901143505359)
                    ·
                      rfl

theorem cell23_7433040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 3, 5].length) (baseStart_7433040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433040 prefixEnd_7433040 := by exact prefixLift 7433040
  have htrace : WordTrace (prefixWord ++ tailWord_7433040) baseStart_7433040 baseEnd_7433040 := by
    simpa [prefixWord, tailWord_7433040, baseEnd_7433040] using wordTrace_append hprefix tailTrace_7433040
  have hstable : (prefixWord ++ tailWord_7433040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433040).length < 2 ^ (prefixWord ++ tailWord_7433040).sum := by decide
  have hdescent : baseEnd_7433040 < baseStart_7433040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433058 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_7433058 : Nat := 118140960795 + 7433058 * 2 ^ 59
def prefixEnd_7433058 : Nat := 4983230072969 + 3 ^ 40 * 7433058 * 2
def baseEnd_7433058 : Nat := 3816731486747484360090995

theorem tailTrace_7433058 : CollatzResearch.WordTrace tailWord_7433058 prefixEnd_7433058 3816731486747484360090995 := by
  unfold tailWord_7433058
  simp only [CollatzResearch.WordTrace]
  refine ⟨67776474376326951521054957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180737265003538537389479885 67776474376326951521054957)
  ·
    refine ⟨25416177891122606820395609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67776474376326951521054957 25416177891122606820395609)
    ·
      refine ⟨19062133418341955115296707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25416177891122606820395609 19062133418341955115296707)
      ·
        refine ⟨28593200127512932672945061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19062133418341955115296707 28593200127512932672945061)
        ·
          refine ⟨5361225023908674876177199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28593200127512932672945061 5361225023908674876177199)
          ·
            refine ⟨8041837535863012314265799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5361225023908674876177199 8041837535863012314265799)
            ·
              refine ⟨12062756303794518471398699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8041837535863012314265799 12062756303794518471398699)
              ·
                refine ⟨18094134455691777707098049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12062756303794518471398699 18094134455691777707098049)
                ·
                  refine ⟨13570600841768833280323537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18094134455691777707098049 13570600841768833280323537)
                  ·
                    refine ⟨10177950631326624960242653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13570600841768833280323537 10177950631326624960242653)
                    ·
                      refine ⟨3816731486747484360090995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10177950631326624960242653 3816731486747484360090995)
                      ·
                        rfl

theorem cell23_7433058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_7433058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433058 prefixEnd_7433058 := by exact prefixLift 7433058
  have htrace : WordTrace (prefixWord ++ tailWord_7433058) baseStart_7433058 baseEnd_7433058 := by
    simpa [prefixWord, tailWord_7433058, baseEnd_7433058] using wordTrace_append hprefix tailTrace_7433058
  have hstable : (prefixWord ++ tailWord_7433058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433058).length < 2 ^ (prefixWord ++ tailWord_7433058).sum := by decide
  have hdescent : baseEnd_7433058 < baseStart_7433058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433064 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_7433064 : Nat := 118140960795 + 7433064 * 2 ^ 59
def prefixEnd_7433064 : Nat := 4983230072969 + 3 ^ 40 * 7433064 * 2
def baseEnd_7433064 : Nat := 3816734567631411336615967

theorem tailTrace_7433064 : CollatzResearch.WordTrace tailWord_7433064 prefixEnd_7433064 3816734567631411336615967 := by
  unfold tailWord_7433064
  simp only [CollatzResearch.WordTrace]
  refine ⟨135553058171643034554469123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180737410895524046072625497 135553058171643034554469123)
  ·
    refine ⟨203329587257464551831703685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135553058171643034554469123 203329587257464551831703685)
    ·
      refine ⟨38124297610774603468444441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203329587257464551831703685 38124297610774603468444441)
      ·
        refine ⟨28593223208080952601333331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38124297610774603468444441 28593223208080952601333331)
        ·
          refine ⟨42889834812121428901999997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28593223208080952601333331 42889834812121428901999997)
          ·
            refine ⟨16083688054545535838249999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42889834812121428901999997 16083688054545535838249999)
            ·
              refine ⟨24125532081818303757374999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16083688054545535838249999 24125532081818303757374999)
              ·
                refine ⟨36188298122727455636062499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24125532081818303757374999 36188298122727455636062499)
                ·
                  refine ⟨54282447184091183454093749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36188298122727455636062499 54282447184091183454093749)
                  ·
                    refine ⟨5088979423508548448821289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54282447184091183454093749 5088979423508548448821289)
                    ·
                      refine ⟨3816734567631411336615967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5088979423508548448821289 3816734567631411336615967)
                      ·
                        rfl

theorem cell23_7433064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_7433064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433064 prefixEnd_7433064 := by exact prefixLift 7433064
  have htrace : WordTrace (prefixWord ++ tailWord_7433064) baseStart_7433064 baseEnd_7433064 := by
    simpa [prefixWord, tailWord_7433064, baseEnd_7433064] using wordTrace_append hprefix tailTrace_7433064
  have hstable : (prefixWord ++ tailWord_7433064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433064).length < 2 ^ (prefixWord ++ tailWord_7433064).sum := by decide
  have hdescent : baseEnd_7433064 < baseStart_7433064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433074 : List Nat := [3, 2, 1, 2, 1, 1, 6, 1, 1, 5]
def baseStart_7433074 : Nat := 118140960795 + 7433074 * 2 ^ 59
def prefixEnd_7433074 : Nat := 4983230072969 + 3 ^ 40 * 7433074 * 2
def baseEnd_7433074 : Nat := 1272246567479318765830307

theorem tailTrace_7433074 : CollatzResearch.WordTrace tailWord_7433074 prefixEnd_7433074 1272246567479318765830307 := by
  unfold tailWord_7433074
  simp only [CollatzResearch.WordTrace]
  refine ⟨67776620268312460204200569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180737654048833227211201517 67776620268312460204200569)
  ·
    refine ⟨50832465201234345153150427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67776620268312460204200569 50832465201234345153150427)
    ·
      refine ⟨76248697801851517729725641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50832465201234345153150427 76248697801851517729725641)
      ·
        refine ⟨57186523351388638297294231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76248697801851517729725641 57186523351388638297294231)
        ·
          refine ⟨85779785027082957445941347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57186523351388638297294231 85779785027082957445941347)
          ·
            refine ⟨128669677540624436168912021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85779785027082957445941347 128669677540624436168912021)
            ·
              refine ⟨6031391134716770445417751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128669677540624436168912021 6031391134716770445417751)
              ·
                refine ⟨9047086702075155668126627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6031391134716770445417751 9047086702075155668126627)
                ·
                  refine ⟨13570630053112733502189941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9047086702075155668126627 13570630053112733502189941)
                  ·
                    refine ⟨1272246567479318765830307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13570630053112733502189941 1272246567479318765830307)
                    ·
                      rfl

theorem cell23_7433074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_7433074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433074 prefixEnd_7433074 := by exact prefixLift 7433074
  have htrace : WordTrace (prefixWord ++ tailWord_7433074) baseStart_7433074 baseEnd_7433074 := by
    simpa [prefixWord, tailWord_7433074, baseEnd_7433074] using wordTrace_append hprefix tailTrace_7433074
  have hstable : (prefixWord ++ tailWord_7433074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433074).length < 2 ^ (prefixWord ++ tailWord_7433074).sum := by decide
  have hdescent : baseEnd_7433074 < baseStart_7433074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433097 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 1, 1, 5]
def baseStart_7433097 : Nat := 118140960795 + 7433097 * 2 ^ 59
def prefixEnd_7433097 : Nat := 4983230072969 + 3 ^ 40 * 7433097 * 2
def baseEnd_7433097 : Nat := 3816751512493009707503315

theorem tailTrace_7433097 : CollatzResearch.WordTrace tailWord_7433097 prefixEnd_7433097 3816751512493009707503315 := by
  unfold tailWord_7433097
  simp only [CollatzResearch.WordTrace]
  refine ⟨271107319952166515744889545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180738213301444343829926363 271107319952166515744889545)
  ·
    refine ⟨203330489964124886808667159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271107319952166515744889545 203330489964124886808667159)
    ·
      refine ⟨304995734946187330213000739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203330489964124886808667159 304995734946187330213000739)
      ·
        refine ⟨457493602419280995319501109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304995734946187330213000739 457493602419280995319501109)
        ·
          refine ⟨42890025226807593311203229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 457493602419280995319501109 42890025226807593311203229)
          ·
            refine ⟨16083759460052847491701211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42890025226807593311203229 16083759460052847491701211)
            ·
              refine ⟨24125639190079271237551817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16083759460052847491701211 24125639190079271237551817)
              ·
                refine ⟨18094229392559453428163863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24125639190079271237551817 18094229392559453428163863)
                ·
                  refine ⟨27141344088839180142245795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18094229392559453428163863 27141344088839180142245795)
                  ·
                    refine ⟨40712016133258770213368693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27141344088839180142245795 40712016133258770213368693)
                    ·
                      refine ⟨3816751512493009707503315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40712016133258770213368693 3816751512493009707503315)
                      ·
                        rfl

theorem cell23_7433097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_7433097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433097 prefixEnd_7433097 := by exact prefixLift 7433097
  have htrace : WordTrace (prefixWord ++ tailWord_7433097) baseStart_7433097 baseEnd_7433097 := by
    simpa [prefixWord, tailWord_7433097, baseEnd_7433097] using wordTrace_append hprefix tailTrace_7433097
  have hstable : (prefixWord ++ tailWord_7433097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433097).length < 2 ^ (prefixWord ++ tailWord_7433097).sum := by decide
  have hdescent : baseEnd_7433097 < baseStart_7433097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433144 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 4, 1, 3]
def baseStart_7433144 : Nat := 118140960795 + 7433144 * 2 ^ 59
def prefixEnd_7433144 : Nat := 4983230072969 + 3 ^ 40 * 7433144 * 2
def baseEnd_7433144 : Nat := 3816775646083771023615599

theorem tailTrace_7433144 : CollatzResearch.WordTrace tailWord_7433144 prefixEnd_7433144 3816775646083771023615599 := by
  unfold tailWord_7433144
  simp only [CollatzResearch.WordTrace]
  refine ⟨135554517091498121385925243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180739356121997495181233657 135554517091498121385925243)
  ·
    refine ⟨203331775637247182078887865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135554517091498121385925243 203331775637247182078887865)
    ·
      refine ⟨152498831727935386559165899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203331775637247182078887865 152498831727935386559165899)
      ·
        refine ⟨228748247591903079838748849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152498831727935386559165899 228748247591903079838748849)
        ·
          refine ⟨171561185693927309879061637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228748247591903079838748849 171561185693927309879061637)
          ·
            refine ⟨32167722317611370602324057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171561185693927309879061637 32167722317611370602324057)
            ·
              refine ⟨24125791738208527951743043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32167722317611370602324057 24125791738208527951743043)
              ·
                refine ⟨36188687607312791927614565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24125791738208527951743043 36188687607312791927614565)
                ·
                  refine ⟨6785378926371148486427731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36188687607312791927614565 6785378926371148486427731)
                  ·
                    refine ⟨10178068389556722729641597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6785378926371148486427731 10178068389556722729641597)
                    ·
                      refine ⟨3816775646083771023615599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10178068389556722729641597 3816775646083771023615599)
                      ·
                        rfl

theorem cell23_7433144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_7433144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433144 prefixEnd_7433144 := by exact prefixLift 7433144
  have htrace : WordTrace (prefixWord ++ tailWord_7433144) baseStart_7433144 baseEnd_7433144 := by
    simpa [prefixWord, tailWord_7433144, baseEnd_7433144] using wordTrace_append hprefix tailTrace_7433144
  have hstable : (prefixWord ++ tailWord_7433144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433144).length < 2 ^ (prefixWord ++ tailWord_7433144).sum := by decide
  have hdescent : baseEnd_7433144 < baseStart_7433144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433145 : List Nat := [1, 2, 1, 4, 2, 3, 3, 2, 1, 2, 2]
def baseStart_7433145 : Nat := 118140960795 + 7433145 * 2 ^ 59
def prefixEnd_7433145 : Nat := 4983230072969 + 3 ^ 40 * 7433145 * 2
def baseEnd_7433145 : Nat := 3816776159564425519703095

theorem tailTrace_7433145 : CollatzResearch.WordTrace tailWord_7433145 prefixEnd_7433145 3816776159564425519703095 := by
  unfold tailWord_7433145
  simp only [CollatzResearch.WordTrace]
  refine ⟨271109070655992619942636889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180739380437328413295091259 271109070655992619942636889)
  ·
    refine ⟨203331802991994464956977667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271109070655992619942636889 203331802991994464956977667)
    ·
      refine ⟨304997704487991697435466501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203331802991994464956977667 304997704487991697435466501)
      ·
        refine ⟨57187069591498443269149969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304997704487991697435466501 57187069591498443269149969)
        ·
          refine ⟨42890302193623832451862477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57187069591498443269149969 42890302193623832451862477)
          ·
            refine ⟨16083863322608937169448429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42890302193623832451862477 16083863322608937169448429)
            ·
              refine ⟨6031448745978351438543161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16083863322608937169448429 6031448745978351438543161)
              ·
                refine ⟨4523586559483763578907371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6031448745978351438543161 4523586559483763578907371)
                ·
                  refine ⟨6785379839225645368361057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4523586559483763578907371 6785379839225645368361057)
                  ·
                    refine ⟨5089034879419234026270793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6785379839225645368361057 5089034879419234026270793)
                    ·
                      refine ⟨3816776159564425519703095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5089034879419234026270793 3816776159564425519703095)
                      ·
                        rfl

theorem cell23_7433145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_7433145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433145 prefixEnd_7433145 := by exact prefixLift 7433145
  have htrace : WordTrace (prefixWord ++ tailWord_7433145) baseStart_7433145 baseEnd_7433145 := by
    simpa [prefixWord, tailWord_7433145, baseEnd_7433145] using wordTrace_append hprefix tailTrace_7433145
  have hstable : (prefixWord ++ tailWord_7433145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433145).length < 2 ^ (prefixWord ++ tailWord_7433145).sum := by decide
  have hdescent : baseEnd_7433145 < baseStart_7433145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433165 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_7433165 : Nat := 118140960795 + 7433165 * 2 ^ 59
def prefixEnd_7433165 : Nat := 4983230072969 + 3 ^ 40 * 7433165 * 2
def baseEnd_7433165 : Nat := 3816786429177515441453003

theorem tailTrace_7433165 : CollatzResearch.WordTrace tailWord_7433165 prefixEnd_7433165 3816786429177515441453003 := by
  unfold tailWord_7433165
  simp only [CollatzResearch.WordTrace]
  refine ⟨271109800115920163358364949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180739866743946775572243299 271109800115920163358364949)
  ·
    refine ⟨12708271880433757657423357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 271109800115920163358364949 12708271880433757657423357)
    ·
      refine ⟨4765601955162659121533759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12708271880433757657423357 4765601955162659121533759)
      ·
        refine ⟨7148402932743988682300639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4765601955162659121533759 7148402932743988682300639)
        ·
          refine ⟨10722604399115983023450959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7148402932743988682300639 10722604399115983023450959)
          ·
            refine ⟨16083906598673974535176439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10722604399115983023450959 16083906598673974535176439)
            ·
              refine ⟨24125859898010961802764659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16083906598673974535176439 24125859898010961802764659)
              ·
                refine ⟨36188789847016442704146989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24125859898010961802764659 36188789847016442704146989)
                ·
                  refine ⟨13570796192631166014055121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36188789847016442704146989 13570796192631166014055121)
                  ·
                    refine ⟨10178097144473374510541341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13570796192631166014055121 10178097144473374510541341)
                    ·
                      refine ⟨3816786429177515441453003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10178097144473374510541341 3816786429177515441453003)
                      ·
                        rfl

theorem cell23_7433165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_7433165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433165 prefixEnd_7433165 := by exact prefixLift 7433165
  have htrace : WordTrace (prefixWord ++ tailWord_7433165) baseStart_7433165 baseEnd_7433165 := by
    simpa [prefixWord, tailWord_7433165, baseEnd_7433165] using wordTrace_append hprefix tailTrace_7433165
  have hstable : (prefixWord ++ tailWord_7433165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433165).length < 2 ^ (prefixWord ++ tailWord_7433165).sum := by decide
  have hdescent : baseEnd_7433165 < baseStart_7433165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433187 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 5]
def baseStart_7433187 : Nat := 118140960795 + 7433187 * 2 ^ 59
def prefixEnd_7433187 : Nat := 4983230072969 + 3 ^ 40 * 7433187 * 2
def baseEnd_7433187 : Nat := 3816797725751914355377901

theorem tailTrace_7433187 : CollatzResearch.WordTrace tailWord_7433187 prefixEnd_7433187 3816797725751914355377901 := by
  unfold tailWord_7433187
  simp only [CollatzResearch.WordTrace]
  refine ⟨271110602521840461115665815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180740401681226974077110543 271110602521840461115665815)
  ·
    refine ⟨406665903782760691673498723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271110602521840461115665815 406665903782760691673498723)
    ·
      refine ⟨609998855674141037510248085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406665903782760691673498723 609998855674141037510248085)
      ·
        refine ⟨28593696359725361133292879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 609998855674141037510248085 28593696359725361133292879)
        ·
          refine ⟨42890544539588041699939319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28593696359725361133292879 42890544539588041699939319)
          ·
            refine ⟨64335816809382062549908979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42890544539588041699939319 64335816809382062549908979)
            ·
              refine ⟨96503725214073093824863469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64335816809382062549908979 96503725214073093824863469)
              ·
                refine ⟨36188896955277410184323801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96503725214073093824863469 36188896955277410184323801)
                ·
                  refine ⟨27141672716458057638242851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36188896955277410184323801 27141672716458057638242851)
                  ·
                    refine ⟨40712509074687086457364277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27141672716458057638242851 40712509074687086457364277)
                    ·
                      refine ⟨3816797725751914355377901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40712509074687086457364277 3816797725751914355377901)
                      ·
                        rfl

theorem cell23_7433187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_7433187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433187 prefixEnd_7433187 := by exact prefixLift 7433187
  have htrace : WordTrace (prefixWord ++ tailWord_7433187) baseStart_7433187 baseEnd_7433187 := by
    simpa [prefixWord, tailWord_7433187, baseEnd_7433187] using wordTrace_append hprefix tailTrace_7433187
  have hstable : (prefixWord ++ tailWord_7433187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433187).length < 2 ^ (prefixWord ++ tailWord_7433187).sum := by decide
  have hdescent : baseEnd_7433187 < baseStart_7433187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433294 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_7433294 : Nat := 118140960795 + 7433294 * 2 ^ 59
def prefixEnd_7433294 : Nat := 4983230072969 + 3 ^ 40 * 7433294 * 2
def baseEnd_7433294 : Nat := 3816852668181945436739909

theorem tailTrace_7433294 : CollatzResearch.WordTrace tailWord_7433294 prefixEnd_7433294 3816852668181945436739909 := by
  unfold tailWord_7433294
  simp only [CollatzResearch.WordTrace]
  refine ⟨33889313141556602298726367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180743003421635212259873957 33889313141556602298726367)
  ·
    refine ⟨50833969712334903448089551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33889313141556602298726367 50833969712334903448089551)
    ·
      refine ⟨76250954568502355172134327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50833969712334903448089551 76250954568502355172134327)
      ·
        refine ⟨114376431852753532758201491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76250954568502355172134327 114376431852753532758201491)
        ·
          refine ⟨171564647779130299137302237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114376431852753532758201491 171564647779130299137302237)
          ·
            refine ⟨64336742917173862176488339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171564647779130299137302237 64336742917173862176488339)
            ·
              refine ⟨96505114375760793264732509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64336742917173862176488339 96505114375760793264732509)
              ·
                refine ⟨36189417890910297474274691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96505114375760793264732509 36189417890910297474274691)
                ·
                  refine ⟨54284126836365446211412037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36189417890910297474274691 54284126836365446211412037)
                  ·
                    refine ⟨10178273781818521164639757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54284126836365446211412037 10178273781818521164639757)
                    ·
                      refine ⟨3816852668181945436739909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10178273781818521164639757 3816852668181945436739909)
                      ·
                        rfl

theorem cell23_7433294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_7433294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433294 prefixEnd_7433294 := by exact prefixLift 7433294
  have htrace : WordTrace (prefixWord ++ tailWord_7433294) baseStart_7433294 baseEnd_7433294 := by
    simpa [prefixWord, tailWord_7433294, baseEnd_7433294] using wordTrace_append hprefix tailTrace_7433294
  have hstable : (prefixWord ++ tailWord_7433294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433294).length < 2 ^ (prefixWord ++ tailWord_7433294).sum := by decide
  have hdescent : baseEnd_7433294 < baseStart_7433294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433297 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 8]
def baseStart_7433297 : Nat := 118140960795 + 7433297 * 2 ^ 59
def prefixEnd_7433297 : Nat := 4983230072969 + 3 ^ 40 * 7433297 * 2
def baseEnd_7433297 : Nat := 424094912069323213889155

theorem tailTrace_7433297 : CollatzResearch.WordTrace tailWord_7433297 prefixEnd_7433297 424094912069323213889155 := by
  unfold tailWord_7433297
  simp only [CollatzResearch.WordTrace]
  refine ⟨271114614551441949902170145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180743076367627966601446763 271114614551441949902170145)
  ·
    refine ⟨203335960913581462426627609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271114614551441949902170145 203335960913581462426627609)
    ·
      refine ⟨152501970685186096819970707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203335960913581462426627609 152501970685186096819970707)
      ·
        refine ⟨228752956027779145229956061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152501970685186096819970707 228752956027779145229956061)
        ·
          refine ⟨85782358510417179461233523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228752956027779145229956061 85782358510417179461233523)
          ·
            refine ⟨128673537765625769191850285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85782358510417179461233523 128673537765625769191850285)
            ·
              refine ⟨48252576662109663446943857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128673537765625769191850285 48252576662109663446943857)
              ·
                refine ⟨36189432496582247585207893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48252576662109663446943857 36189432496582247585207893)
                ·
                  refine ⟨424094912069323213889155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36189432496582247585207893 424094912069323213889155)
                  ·
                    rfl

theorem cell23_7433297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 8].length) (baseStart_7433297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433297 prefixEnd_7433297 := by exact prefixLift 7433297
  have htrace : WordTrace (prefixWord ++ tailWord_7433297) baseStart_7433297 baseEnd_7433297 := by
    simpa [prefixWord, tailWord_7433297, baseEnd_7433297] using wordTrace_append hprefix tailTrace_7433297
  have hstable : (prefixWord ++ tailWord_7433297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433297).length < 2 ^ (prefixWord ++ tailWord_7433297).sum := by decide
  have hdescent : baseEnd_7433297 < baseStart_7433297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433341 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 5, 1, 3]
def baseStart_7433341 : Nat := 118140960795 + 7433341 * 2 ^ 59
def prefixEnd_7433341 : Nat := 4983230072969 + 3 ^ 40 * 7433341 * 2
def baseEnd_7433341 : Nat := 3816876801772706752852193

theorem tailTrace_7433341 : CollatzResearch.WordTrace tailWord_7433341 prefixEnd_7433341 3816876801772706752852193 := by
  unfold tailWord_7433341
  simp only [CollatzResearch.WordTrace]
  refine ⟨271116219363282545416771877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180744146242188363611181251 271116219363282545416771877)
  ·
    refine ⟨50834291130615477265644727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271116219363282545416771877 50834291130615477265644727)
    ·
      refine ⟨76251436695923215898467091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50834291130615477265644727 76251436695923215898467091)
      ·
        refine ⟨114377155043884823847700637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76251436695923215898467091 114377155043884823847700637)
        ·
          refine ⟨42891433141456808942887739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114377155043884823847700637 42891433141456808942887739)
          ·
            refine ⟨64337149712185213414331609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42891433141456808942887739 64337149712185213414331609)
            ·
              refine ⟨48252862284138910060748707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64337149712185213414331609 48252862284138910060748707)
              ·
                refine ⟨72379293426208365091123061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48252862284138910060748707 72379293426208365091123061)
                ·
                  refine ⟨6785558758707034227292787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72379293426208365091123061 6785558758707034227292787)
                  ·
                    refine ⟨10178338138060551340939181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6785558758707034227292787 10178338138060551340939181)
                    ·
                      refine ⟨3816876801772706752852193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10178338138060551340939181 3816876801772706752852193)
                      ·
                        rfl

theorem cell23_7433341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_7433341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433341 prefixEnd_7433341 := by exact prefixLift 7433341
  have htrace : WordTrace (prefixWord ++ tailWord_7433341) baseStart_7433341 baseEnd_7433341 := by
    simpa [prefixWord, tailWord_7433341, baseEnd_7433341] using wordTrace_append hprefix tailTrace_7433341
  have hstable : (prefixWord ++ tailWord_7433341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433341).length < 2 ^ (prefixWord ++ tailWord_7433341).sum := by decide
  have hdescent : baseEnd_7433341 < baseStart_7433341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433342 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_7433342 : Nat := 118140960795 + 7433342 * 2 ^ 59
def prefixEnd_7433342 : Nat := 4983230072969 + 3 ^ 40 * 7433342 * 2
def baseEnd_7433342 : Nat := 3816877315253361248939689

theorem tailTrace_7433342 : CollatzResearch.WordTrace tailWord_7433342 prefixEnd_7433342 3816877315253361248939689 := by
  unfold tailWord_7433342
  simp only [CollatzResearch.WordTrace]
  refine ⟨33889531979534865323444785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180744170557519281725038853 33889531979534865323444785)
  ·
    refine ⟨25417148984651148992583589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33889531979534865323444785 25417148984651148992583589)
    ·
      refine ⟨4765715434622090436109423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25417148984651148992583589 4765715434622090436109423)
      ·
        refine ⟨7148573151933135654164135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4765715434622090436109423 7148573151933135654164135)
        ·
          refine ⟨10722859727899703481246203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7148573151933135654164135 10722859727899703481246203)
          ·
            refine ⟨16084289591849555221869305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10722859727899703481246203 16084289591849555221869305)
            ·
              refine ⟨12063217193887166416401979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16084289591849555221869305 12063217193887166416401979)
              ·
                refine ⟨18094825790830749624602969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12063217193887166416401979 18094825790830749624602969)
                ·
                  refine ⟨13571119343123062218452227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18094825790830749624602969 13571119343123062218452227)
                  ·
                    refine ⟨20356679014684593327678341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13571119343123062218452227 20356679014684593327678341)
                    ·
                      refine ⟨3816877315253361248939689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20356679014684593327678341 3816877315253361248939689)
                      ·
                        rfl

theorem cell23_7433342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_7433342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433342 prefixEnd_7433342 := by exact prefixLift 7433342
  have htrace : WordTrace (prefixWord ++ tailWord_7433342) baseStart_7433342 baseEnd_7433342 := by
    simpa [prefixWord, tailWord_7433342, baseEnd_7433342] using wordTrace_append hprefix tailTrace_7433342
  have hstable : (prefixWord ++ tailWord_7433342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433342).length < 2 ^ (prefixWord ++ tailWord_7433342).sum := by decide
  have hdescent : baseEnd_7433342 < baseStart_7433342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433368 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 2, 3, 2]
def baseStart_7433368 : Nat := 118140960795 + 7433368 * 2 ^ 59
def prefixEnd_7433368 : Nat := 4983230072969 + 3 ^ 40 * 7433368 * 2
def baseEnd_7433368 : Nat := 3816890665750378147214569

theorem tailTrace_7433368 : CollatzResearch.WordTrace tailWord_7433368 prefixEnd_7433368 3816890665750378147214569 := by
  unfold tailWord_7433368
  simp only [CollatzResearch.WordTrace]
  refine ⟨135558602067092364514002379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180744802756123152685336505 135558602067092364514002379)
  ·
    refine ⟨203337903100638546771003569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135558602067092364514002379 203337903100638546771003569)
    ·
      refine ⟨152503427325478910078252677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203337903100638546771003569 152503427325478910078252677)
      ·
        refine ⟨28594392623527295639672377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152503427325478910078252677 28594392623527295639672377)
        ·
          refine ⟨21445794467645471729754283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28594392623527295639672377 21445794467645471729754283)
          ·
            refine ⟨32168691701468207594631425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21445794467645471729754283 32168691701468207594631425)
            ·
              refine ⟨24126518776101155695973569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32168691701468207594631425 24126518776101155695973569)
              ·
                refine ⟨18094889082075866771980177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24126518776101155695973569 18094889082075866771980177)
                ·
                  refine ⟨13571166811556900078985133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18094889082075866771980177 13571166811556900078985133)
                  ·
                    refine ⟨5089187554333837529619425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13571166811556900078985133 5089187554333837529619425)
                    ·
                      refine ⟨3816890665750378147214569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5089187554333837529619425 3816890665750378147214569)
                      ·
                        rfl

theorem cell23_7433368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_7433368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433368 prefixEnd_7433368 := by exact prefixLift 7433368
  have htrace : WordTrace (prefixWord ++ tailWord_7433368) baseStart_7433368 baseEnd_7433368 := by
    simpa [prefixWord, tailWord_7433368, baseEnd_7433368] using wordTrace_append hprefix tailTrace_7433368
  have hstable : (prefixWord ++ tailWord_7433368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433368).length < 2 ^ (prefixWord ++ tailWord_7433368).sum := by decide
  have hdescent : baseEnd_7433368 < baseStart_7433368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433391 : List Nat := [1, 1, 2, 1, 2, 3, 4, 3, 2, 4]
def baseStart_7433391 : Nat := 118140960795 + 7433391 * 2 ^ 59
def prefixEnd_7433391 : Nat := 4983230072969 + 3 ^ 40 * 7433391 * 2
def baseEnd_7433391 : Nat := 1272300825268477185742321

theorem tailTrace_7433391 : CollatzResearch.WordTrace tailWord_7433391 prefixEnd_7433391 1272300825268477185742321 := by
  unfold tailWord_7433391
  simp only [CollatzResearch.WordTrace]
  refine ⟨271118043013101403956092027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180745362008734269304061351 271118043013101403956092027)
  ·
    refine ⟨406677064519652105934138041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271118043013101403956092027 406677064519652105934138041)
    ·
      refine ⟨305007798389739079450603531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406677064519652105934138041 305007798389739079450603531)
      ·
        refine ⟨457511697584608619175905297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305007798389739079450603531 457511697584608619175905297)
        ·
          refine ⟨343133773188456464381928973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457511697584608619175905297 343133773188456464381928973)
          ·
            refine ⟨128675164945671174143223365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343133773188456464381928973 128675164945671174143223365)
            ·
              refine ⟨24126593427313345151854381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128675164945671174143223365 24126593427313345151854381)
              ·
                refine ⟨9047472535242504431945393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24126593427313345151854381 9047472535242504431945393)
                ·
                  refine ⟨6785604401431878323959045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9047472535242504431945393 6785604401431878323959045)
                  ·
                    refine ⟨1272300825268477185742321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6785604401431878323959045 1272300825268477185742321)
                    ·
                      rfl

theorem cell23_7433391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 4].length) (baseStart_7433391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433391 prefixEnd_7433391 := by exact prefixLift 7433391
  have htrace : WordTrace (prefixWord ++ tailWord_7433391) baseStart_7433391 baseEnd_7433391 := by
    simpa [prefixWord, tailWord_7433391, baseEnd_7433391] using wordTrace_append hprefix tailTrace_7433391
  have hstable : (prefixWord ++ tailWord_7433391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433391).length < 2 ^ (prefixWord ++ tailWord_7433391).sum := by decide
  have hdescent : baseEnd_7433391 < baseStart_7433391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433401 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 3, 2, 3]
def baseStart_7433401 : Nat := 118140960795 + 7433401 * 2 ^ 59
def prefixEnd_7433401 : Nat := 4983230072969 + 3 ^ 40 * 7433401 * 2
def baseEnd_7433401 : Nat := 3816907610611976518101917

theorem tailTrace_7433401 : CollatzResearch.WordTrace tailWord_7433401 prefixEnd_7433401 3816907610611976518101917 := by
  unfold tailWord_7433401
  simp only [CollatzResearch.WordTrace]
  refine ⟨271118407743065175663956057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180745605162043450442637371 271118407743065175663956057)
  ·
    refine ⟨203338805807298881747967043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271118407743065175663956057 203338805807298881747967043)
    ·
      refine ⟨305008208710948322621950565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203338805807298881747967043 305008208710948322621950565)
      ·
        refine ⟨57189039133302810491615731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305008208710948322621950565 57189039133302810491615731)
        ·
          refine ⟨85783558699954215737423597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57189039133302810491615731 85783558699954215737423597)
          ·
            refine ⟨32168834512482830901533849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85783558699954215737423597 32168834512482830901533849)
            ·
              refine ⟨24126625884362123176150387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32168834512482830901533849 24126625884362123176150387)
              ·
                refine ⟨36189938826543184764225581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24126625884362123176150387 36189938826543184764225581)
                ·
                  refine ⟨13571227059953694286584593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36189938826543184764225581 13571227059953694286584593)
                  ·
                    refine ⟨10178420294965270714938445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13571227059953694286584593 10178420294965270714938445)
                    ·
                      refine ⟨3816907610611976518101917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10178420294965270714938445 3816907610611976518101917)
                      ·
                        rfl

theorem cell23_7433401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_7433401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433401 prefixEnd_7433401 := by exact prefixLift 7433401
  have htrace : WordTrace (prefixWord ++ tailWord_7433401) baseStart_7433401 baseEnd_7433401 := by
    simpa [prefixWord, tailWord_7433401, baseEnd_7433401] using wordTrace_append hprefix tailTrace_7433401
  have hstable : (prefixWord ++ tailWord_7433401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433401).length < 2 ^ (prefixWord ++ tailWord_7433401).sum := by decide
  have hdescent : baseEnd_7433401 < baseStart_7433401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433412 : List Nat := [2, 3, 3, 1, 4, 1, 2, 1, 1, 5]
def baseStart_7433412 : Nat := 118140960795 + 7433412 * 2 ^ 59
def prefixEnd_7433412 : Nat := 4983230072969 + 3 ^ 40 * 7433412 * 2
def baseEnd_7433412 : Nat := 1272304419633058658354789

theorem tailTrace_7433412 : CollatzResearch.WordTrace tailWord_7433412 prefixEnd_7433412 1272304419633058658354789 := by
  unfold tailWord_7433412
  simp only [CollatzResearch.WordTrace]
  refine ⟨135559404473012662271303245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180745872630683549695070993 135559404473012662271303245)
  ·
    refine ⟨50834776677379748351738717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135559404473012662271303245 50834776677379748351738717)
    ·
      refine ⟨19063041254017405631902019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50834776677379748351738717 19063041254017405631902019)
      ·
        refine ⟨28594561881026108447853029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19063041254017405631902019 28594561881026108447853029)
        ·
          refine ⟨5361480352692395333972443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28594561881026108447853029 5361480352692395333972443)
          ·
            refine ⟨8042220529038593000958665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5361480352692395333972443 8042220529038593000958665)
            ·
              refine ⟨6031665396778944750718999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8042220529038593000958665 6031665396778944750718999)
              ·
                refine ⟨9047498095168417126078499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6031665396778944750718999 9047498095168417126078499)
                ·
                  refine ⟨13571247142752625689117749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9047498095168417126078499 13571247142752625689117749)
                  ·
                    refine ⟨1272304419633058658354789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13571247142752625689117749 1272304419633058658354789)
                    ·
                      rfl

theorem cell23_7433412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_7433412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433412 prefixEnd_7433412 := by exact prefixLift 7433412
  have htrace : WordTrace (prefixWord ++ tailWord_7433412) baseStart_7433412 baseEnd_7433412 := by
    simpa [prefixWord, tailWord_7433412, baseEnd_7433412] using wordTrace_append hprefix tailTrace_7433412
  have hstable : (prefixWord ++ tailWord_7433412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433412).length < 2 ^ (prefixWord ++ tailWord_7433412).sum := by decide
  have hdescent : baseEnd_7433412 < baseStart_7433412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433418 : List Nat := [3, 1, 2, 1, 3, 3, 1, 3, 1, 2, 3]
def baseStart_7433418 : Nat := 118140960795 + 7433418 * 2 ^ 59
def prefixEnd_7433418 : Nat := 4983230072969 + 3 ^ 40 * 7433418 * 2
def baseEnd_7433418 : Nat := 3816916339783102951589339

theorem tailTrace_7433418 : CollatzResearch.WordTrace tailWord_7433418 prefixEnd_7433418 3816916339783102951589339 := by
  unfold tailWord_7433418
  simp only [CollatzResearch.WordTrace]
  refine ⟨67779756946000896891831227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180746018522669058378216605 67779756946000896891831227)
  ·
    refine ⟨101669635419001345337746841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67779756946000896891831227 101669635419001345337746841)
    ·
      refine ⟨76252226564251009003310131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101669635419001345337746841 76252226564251009003310131)
      ·
        refine ⟨114378339846376513504965197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76252226564251009003310131 114378339846376513504965197)
        ·
          refine ⟨42891877442391192564361949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114378339846376513504965197 42891877442391192564361949)
          ·
            refine ⟨16084454040896697211635731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42891877442391192564361949 16084454040896697211635731)
            ·
              refine ⟨24126681061345045817453597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16084454040896697211635731 24126681061345045817453597)
              ·
                refine ⟨9047505398004392181545099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24126681061345045817453597 9047505398004392181545099)
                ·
                  refine ⟨13571258097006588272317649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9047505398004392181545099 13571258097006588272317649)
                  ·
                    refine ⟨10178443572754941204238237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13571258097006588272317649 10178443572754941204238237)
                    ·
                      refine ⟨3816916339783102951589339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10178443572754941204238237 3816916339783102951589339)
                      ·
                        rfl

theorem cell23_7433418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_7433418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433418 prefixEnd_7433418 := by exact prefixLift 7433418
  have htrace : WordTrace (prefixWord ++ tailWord_7433418) baseStart_7433418 baseEnd_7433418 := by
    simpa [prefixWord, tailWord_7433418, baseEnd_7433418] using wordTrace_append hprefix tailTrace_7433418
  have hstable : (prefixWord ++ tailWord_7433418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433418).length < 2 ^ (prefixWord ++ tailWord_7433418).sum := by decide
  have hdescent : baseEnd_7433418 < baseStart_7433418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433445 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 1, 2, 4]
def baseStart_7433445 : Nat := 118140960795 + 7433445 * 2 ^ 59
def prefixEnd_7433445 : Nat := 4983230072969 + 3 ^ 40 * 7433445 * 2
def baseEnd_7433445 : Nat := 3816930203760774345951715

theorem tailTrace_7433445 : CollatzResearch.WordTrace tailWord_7433445 prefixEnd_7433445 3816930203760774345951715 := by
  unfold tailWord_7433445
  simp only [CollatzResearch.WordTrace]
  refine ⟨271120012554905771178557789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180746675036603847452371859 271120012554905771178557789)
  ·
    refine ⟨101670004708089664191959171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271120012554905771178557789 101670004708089664191959171)
    ·
      refine ⟨152505007062134496287938757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101670004708089664191959171 152505007062134496287938757)
      ·
        refine ⟨28594688824150218053988517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152505007062134496287938757 28594688824150218053988517)
        ·
          refine ⟨5361504154528165885122847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28594688824150218053988517 5361504154528165885122847)
          ·
            refine ⟨8042256231792248827684271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5361504154528165885122847 8042256231792248827684271)
            ·
              refine ⟨12063384347688373241526407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8042256231792248827684271 12063384347688373241526407)
              ·
                refine ⟨18095076521532559862289611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12063384347688373241526407 18095076521532559862289611)
                ·
                  refine ⟨27142614782298839793434417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18095076521532559862289611 27142614782298839793434417)
                  ·
                    refine ⟨20356961086724129845075813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27142614782298839793434417 20356961086724129845075813)
                    ·
                      refine ⟨3816930203760774345951715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20356961086724129845075813 3816930203760774345951715)
                      ·
                        rfl

theorem cell23_7433445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_7433445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433445 prefixEnd_7433445 := by exact prefixLift 7433445
  have htrace : WordTrace (prefixWord ++ tailWord_7433445) baseStart_7433445 baseEnd_7433445 := by
    simpa [prefixWord, tailWord_7433445, baseEnd_7433445] using wordTrace_append hprefix tailTrace_7433445
  have hstable : (prefixWord ++ tailWord_7433445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433445).length < 2 ^ (prefixWord ++ tailWord_7433445).sum := by decide
  have hdescent : baseEnd_7433445 < baseStart_7433445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433526 : List Nat := [5, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7433526 : Nat := 118140960795 + 7433526 * 2 ^ 59
def prefixEnd_7433526 : Nat := 4983230072969 + 3 ^ 40 * 7433526 * 2
def baseEnd_7433526 : Nat := 3816971795693788529038843

theorem tailTrace_7433526 : CollatzResearch.WordTrace tailWord_7433526 prefixEnd_7433526 3816971795693788529038843 := by
  unfold tailWord_7433526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16945185429225770125766027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180748644578408214674837621 16945185429225770125766027)
  ·
    refine ⟨25417778143838655188649041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16945185429225770125766027 25417778143838655188649041)
    ·
      refine ⟨19063333607878991391486781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25417778143838655188649041 19063333607878991391486781)
      ·
        refine ⟨7148750102954621771807543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19063333607878991391486781 7148750102954621771807543)
        ·
          refine ⟨10723125154431932657711315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7148750102954621771807543 10723125154431932657711315)
          ·
            refine ⟨16084687731647898986566973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10723125154431932657711315 16084687731647898986566973)
            ·
              refine ⟨6031757899367962119962615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16084687731647898986566973 6031757899367962119962615)
              ·
                refine ⟨9047636849051943179943923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6031757899367962119962615 9047636849051943179943923)
                ·
                  refine ⟨13571455273577914769915885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9047636849051943179943923 13571455273577914769915885)
                  ·
                    refine ⟨5089295727591718038718457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13571455273577914769915885 5089295727591718038718457)
                    ·
                      refine ⟨3816971795693788529038843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5089295727591718038718457 3816971795693788529038843)
                      ·
                        rfl

theorem cell23_7433526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7433526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433526 prefixEnd_7433526 := by exact prefixLift 7433526
  have htrace : WordTrace (prefixWord ++ tailWord_7433526) baseStart_7433526 baseEnd_7433526 := by
    simpa [prefixWord, tailWord_7433526, baseEnd_7433526] using wordTrace_append hprefix tailTrace_7433526
  have hstable : (prefixWord ++ tailWord_7433526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433526).length < 2 ^ (prefixWord ++ tailWord_7433526).sum := by decide
  have hdescent : baseEnd_7433526 < baseStart_7433526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433548 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 2, 5, 2]
def baseStart_7433548 : Nat := 118140960795 + 7433548 * 2 ^ 59
def prefixEnd_7433548 : Nat := 4983230072969 + 3 ^ 40 * 7433548 * 2
def baseEnd_7433548 : Nat := 3816983092268187442963741

theorem tailTrace_7433548 : CollatzResearch.WordTrace tailWord_7433548 prefixEnd_7433548 3816983092268187442963741 := by
  unfold tailWord_7433548
  simp only [CollatzResearch.WordTrace]
  refine ⟨135561884636766309884778649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180749179515688413179704865 135561884636766309884778649)
  ·
    refine ⟨101671413477574732413583987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135561884636766309884778649 101671413477574732413583987)
    ·
      refine ⟨152507120216362098620375981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101671413477574732413583987 152507120216362098620375981)
      ·
        refine ⟨57190170081135786982640993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152507120216362098620375981 57190170081135786982640993)
        ·
          refine ⟨42892627560851840236980745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57190170081135786982640993 42892627560851840236980745)
          ·
            refine ⟨32169470670638880177735559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42892627560851840236980745 32169470670638880177735559)
            ·
              refine ⟨48254206005958320266603339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32169470670638880177735559 48254206005958320266603339)
              ·
                refine ⟨72381309008937480399905009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48254206005958320266603339 72381309008937480399905009)
                ·
                  refine ⟨54285981756703110299928757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72381309008937480399905009 54285981756703110299928757)
                  ·
                    refine ⟨5089310789690916590618321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54285981756703110299928757 5089310789690916590618321)
                    ·
                      refine ⟨3816983092268187442963741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5089310789690916590618321 3816983092268187442963741)
                      ·
                        rfl

theorem cell23_7433548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_7433548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433548 prefixEnd_7433548 := by exact prefixLift 7433548
  have htrace : WordTrace (prefixWord ++ tailWord_7433548) baseStart_7433548 baseEnd_7433548 := by
    simpa [prefixWord, tailWord_7433548, baseEnd_7433548] using wordTrace_append hprefix tailTrace_7433548
  have hstable : (prefixWord ++ tailWord_7433548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433548).length < 2 ^ (prefixWord ++ tailWord_7433548).sum := by decide
  have hdescent : baseEnd_7433548 < baseStart_7433548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433561 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 4, 1, 4]
def baseStart_7433561 : Nat := 118140960795 + 7433561 * 2 ^ 59
def prefixEnd_7433561 : Nat := 4983230072969 + 3 ^ 40 * 7433561 * 2
def baseEnd_7433561 : Nat := 3816989767516695892101181

theorem tailTrace_7433561 : CollatzResearch.WordTrace tailWord_7433561 prefixEnd_7433561 3816989767516695892101181 := by
  unfold tailWord_7433561
  simp only [CollatzResearch.WordTrace]
  refine ⟨271124243422485522989780537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180749495614990348659853691 271124243422485522989780537)
  ·
    refine ⟨203343182566864142242335403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271124243422485522989780537 203343182566864142242335403)
    ·
      refine ⟨305014773850296213363503105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203343182566864142242335403 305014773850296213363503105)
      ·
        refine ⟨228761080387722160022627329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305014773850296213363503105 228761080387722160022627329)
        ·
          refine ⟨171570810290791620016970497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228761080387722160022627329 171570810290791620016970497)
          ·
            refine ⟨128678107718093715012727873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171570810290791620016970497 128678107718093715012727873)
            ·
              refine ⟨96508580788570286259545905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128678107718093715012727873 96508580788570286259545905)
              ·
                refine ⟨72381435591427714694659429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96508580788570286259545905 72381435591427714694659429)
                ·
                  refine ⟨13571519173392696505248643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72381435591427714694659429 13571519173392696505248643)
                  ·
                    refine ⟨20357278760089044757872965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13571519173392696505248643 20357278760089044757872965)
                    ·
                      refine ⟨3816989767516695892101181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20357278760089044757872965 3816989767516695892101181)
                      ·
                        rfl

theorem cell23_7433561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_7433561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433561 prefixEnd_7433561 := by exact prefixLift 7433561
  have htrace : WordTrace (prefixWord ++ tailWord_7433561) baseStart_7433561 baseEnd_7433561 := by
    simpa [prefixWord, tailWord_7433561, baseEnd_7433561] using wordTrace_append hprefix tailTrace_7433561
  have hstable : (prefixWord ++ tailWord_7433561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433561).length < 2 ^ (prefixWord ++ tailWord_7433561).sum := by decide
  have hdescent : baseEnd_7433561 < baseStart_7433561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433575 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 2, 5]
def baseStart_7433575 : Nat := 118140960795 + 7433575 * 2 ^ 59
def prefixEnd_7433575 : Nat := 4983230072969 + 3 ^ 40 * 7433575 * 2
def baseEnd_7433575 : Nat := 1272332318748619612442039

theorem tailTrace_7433575 : CollatzResearch.WordTrace tailWord_7433575 prefixEnd_7433575 1272332318748619612442039 := by
  unfold tailWord_7433575
  simp only [CollatzResearch.WordTrace]
  refine ⟨271124754044434803380790179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180749836029623202253860119 271124754044434803380790179)
  ·
    refine ⟨406687131066652205071185269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271124754044434803380790179 406687131066652205071185269)
    ·
      refine ⟨38126918537498644225423619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 406687131066652205071185269 38126918537498644225423619)
      ·
        refine ⟨57190377806247966338135429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38126918537498644225423619 57190377806247966338135429)
        ·
          refine ⟨10723195838671493688400393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57190377806247966338135429 10723195838671493688400393)
          ·
            refine ⟨8042396879003620266300295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10723195838671493688400393 8042396879003620266300295)
            ·
              refine ⟨12063595318505430399450443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8042396879003620266300295 12063595318505430399450443)
              ·
                refine ⟨18095392977758145599175665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12063595318505430399450443 18095392977758145599175665)
                ·
                  refine ⟨13571544733318609199381749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18095392977758145599175665 13571544733318609199381749)
                  ·
                    refine ⟨1272332318748619612442039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13571544733318609199381749 1272332318748619612442039)
                    ·
                      rfl

theorem cell23_7433575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_7433575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433575 prefixEnd_7433575 := by exact prefixLift 7433575
  have htrace : WordTrace (prefixWord ++ tailWord_7433575) baseStart_7433575 baseEnd_7433575 := by
    simpa [prefixWord, tailWord_7433575, baseEnd_7433575] using wordTrace_append hprefix tailTrace_7433575
  have hstable : (prefixWord ++ tailWord_7433575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433575).length < 2 ^ (prefixWord ++ tailWord_7433575).sum := by decide
  have hdescent : baseEnd_7433575 < baseStart_7433575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433605 : List Nat := [1, 3, 1, 1, 3, 1, 4, 4, 1, 4]
def baseStart_7433605 : Nat := 118140960795 + 7433605 * 2 ^ 59
def prefixEnd_7433605 : Nat := 4983230072969 + 3 ^ 40 * 7433605 * 2
def baseEnd_7433605 : Nat := 1272337453555164573316993

theorem tailTrace_7433605 : CollatzResearch.WordTrace tailWord_7433605 prefixEnd_7433605 1272337453555164573316993 := by
  unfold tailWord_7433605
  simp only [CollatzResearch.WordTrace]
  refine ⟨271125848234326118504382269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180750565489550745669588179 271125848234326118504382269)
  ·
    refine ⟨101672193087872294439143351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271125848234326118504382269 101672193087872294439143351)
    ·
      refine ⟨152508289631808441658715027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101672193087872294439143351 152508289631808441658715027)
      ·
        refine ⟨228762434447712662488072541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152508289631808441658715027 228762434447712662488072541)
        ·
          refine ⟨85785912917892248433027203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228762434447712662488072541 85785912917892248433027203)
          ·
            refine ⟨128678869376838372649540805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85785912917892248433027203 128678869376838372649540805)
            ·
              refine ⟨24127288008157194871788901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128678869376838372649540805 24127288008157194871788901)
              ·
                refine ⟨4523866501529474038460419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24127288008157194871788901 4523866501529474038460419)
                ·
                  refine ⟨6785799752294211057690629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4523866501529474038460419 6785799752294211057690629)
                  ·
                    refine ⟨1272337453555164573316993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6785799752294211057690629 1272337453555164573316993)
                    ·
                      rfl

theorem cell23_7433605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_7433605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433605 prefixEnd_7433605 := by exact prefixLift 7433605
  have htrace : WordTrace (prefixWord ++ tailWord_7433605) baseStart_7433605 baseEnd_7433605 := by
    simpa [prefixWord, tailWord_7433605, baseEnd_7433605] using wordTrace_append hprefix tailTrace_7433605
  have hstable : (prefixWord ++ tailWord_7433605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433605).length < 2 ^ (prefixWord ++ tailWord_7433605).sum := by decide
  have hdescent : baseEnd_7433605 < baseStart_7433605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433655 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 2, 3, 2]
def baseStart_7433655 : Nat := 118140960795 + 7433655 * 2 ^ 59
def prefixEnd_7433655 : Nat := 4983230072969 + 3 ^ 40 * 7433655 * 2
def baseEnd_7433655 : Nat := 3817038034698218524325749

theorem tailTrace_7433655 : CollatzResearch.WordTrace tailWord_7433655 prefixEnd_7433655 3817038034698218524325749 := by
  unfold tailWord_7433655
  simp only [CollatzResearch.WordTrace]
  refine ⟨271127671884144977043702419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180751781256096651362468279 271127671884144977043702419)
  ·
    refine ⟨406691507826217465565553629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271127671884144977043702419 406691507826217465565553629)
    ·
      refine ⟨152509315434831549587082611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406691507826217465565553629 152509315434831549587082611)
      ·
        refine ⟨228763973152247324380623917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152509315434831549587082611 228763973152247324380623917)
        ·
          refine ⟨85786489932092746642733969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228763973152247324380623917 85786489932092746642733969)
          ·
            refine ⟨64339867449069559982050477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85786489932092746642733969 64339867449069559982050477)
            ·
              refine ⟨24127450293401084993268929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64339867449069559982050477 24127450293401084993268929)
              ·
                refine ⟨18095587720050813744951697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24127450293401084993268929 18095587720050813744951697)
                ·
                  refine ⟨13571690790038110308713773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18095587720050813744951697 13571690790038110308713773)
                  ·
                    refine ⟨5089384046264291365767665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13571690790038110308713773 5089384046264291365767665)
                    ·
                      refine ⟨3817038034698218524325749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5089384046264291365767665 3817038034698218524325749)
                      ·
                        rfl

theorem cell23_7433655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 3, 2].length) (baseStart_7433655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433655 prefixEnd_7433655 := by exact prefixLift 7433655
  have htrace : WordTrace (prefixWord ++ tailWord_7433655) baseStart_7433655 baseEnd_7433655 := by
    simpa [prefixWord, tailWord_7433655, baseEnd_7433655] using wordTrace_append hprefix tailTrace_7433655
  have hstable : (prefixWord ++ tailWord_7433655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433655).length < 2 ^ (prefixWord ++ tailWord_7433655).sum := by decide
  have hdescent : baseEnd_7433655 < baseStart_7433655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433732 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_7433732 : Nat := 118140960795 + 7433732 * 2 ^ 59
def prefixEnd_7433732 : Nat := 4983230072969 + 3 ^ 40 * 7433732 * 2
def baseEnd_7433732 : Nat := 3817077572708614723062895

theorem tailTrace_7433732 : CollatzResearch.WordTrace tailWord_7433732 prefixEnd_7433732 3817077572708614723062895 := by
  unfold tailWord_7433732
  simp only [CollatzResearch.WordTrace]
  refine ⟨135565240152433009597127725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180753653536577346129503633 135565240152433009597127725)
  ·
    refine ⟨50836965057162378598922897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135565240152433009597127725 50836965057162378598922897)
    ·
      refine ⟨38127723792871783949192173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50836965057162378598922897 38127723792871783949192173)
      ·
        refine ⟨14297896422326918980947065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38127723792871783949192173 14297896422326918980947065)
        ·
          refine ⟨10723422316745189235710299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14297896422326918980947065 10723422316745189235710299)
          ·
            refine ⟨16085133475117783853565449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10723422316745189235710299 16085133475117783853565449)
            ·
              refine ⟨12063850106338337890174087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16085133475117783853565449 12063850106338337890174087)
              ·
                refine ⟨18095775159507506835261131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12063850106338337890174087 18095775159507506835261131)
                ·
                  refine ⟨27143662739261260252891697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18095775159507506835261131 27143662739261260252891697)
                  ·
                    refine ⟨20357747054445945189668773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27143662739261260252891697 20357747054445945189668773)
                    ·
                      refine ⟨3817077572708614723062895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20357747054445945189668773 3817077572708614723062895)
                      ·
                        rfl

theorem cell23_7433732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_7433732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433732 prefixEnd_7433732 := by exact prefixLift 7433732
  have htrace : WordTrace (prefixWord ++ tailWord_7433732) baseStart_7433732 baseEnd_7433732 := by
    simpa [prefixWord, tailWord_7433732, baseEnd_7433732] using wordTrace_append hprefix tailTrace_7433732
  have hstable : (prefixWord ++ tailWord_7433732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433732).length < 2 ^ (prefixWord ++ tailWord_7433732).sum := by decide
  have hdescent : baseEnd_7433732 < baseStart_7433732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433735 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_7433735 : Nat := 118140960795 + 7433735 * 2 ^ 59
def prefixEnd_7433735 : Nat := 4983230072969 + 3 ^ 40 * 7433735 * 2
def baseEnd_7433735 : Nat := 3817079113150578211325381

theorem tailTrace_7433735 : CollatzResearch.WordTrace tailWord_7433735 prefixEnd_7433735 3817079113150578211325381 := by
  unfold tailWord_7433735
  simp only [CollatzResearch.WordTrace]
  refine ⟨271130589723855150706614659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180753726482570100471076439 271130589723855150706614659)
  ·
    refine ⟨406695884585782726059921989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271130589723855150706614659 406695884585782726059921989)
    ·
      refine ⟨76255478359834261136235373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 406695884585782726059921989 76255478359834261136235373)
      ·
        refine ⟨28595804384937847926088265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76255478359834261136235373 28595804384937847926088265)
        ·
          refine ⟨21446853288703385944566199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28595804384937847926088265 21446853288703385944566199)
          ·
            refine ⟨32170279933055078916849299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21446853288703385944566199 32170279933055078916849299)
            ·
              refine ⟨48255419899582618375273949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32170279933055078916849299 48255419899582618375273949)
              ·
                refine ⟨18095782462343481890727731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48255419899582618375273949 18095782462343481890727731)
                ·
                  refine ⟨27143673693515222836091597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18095782462343481890727731 27143673693515222836091597)
                  ·
                    refine ⟨10178877635068208563534349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27143673693515222836091597 10178877635068208563534349)
                    ·
                      refine ⟨3817079113150578211325381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10178877635068208563534349 3817079113150578211325381)
                      ·
                        rfl

theorem cell23_7433735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_7433735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433735 prefixEnd_7433735 := by exact prefixLift 7433735
  have htrace : WordTrace (prefixWord ++ tailWord_7433735) baseStart_7433735 baseEnd_7433735 := by
    simpa [prefixWord, tailWord_7433735, baseEnd_7433735] using wordTrace_append hprefix tailTrace_7433735
  have hstable : (prefixWord ++ tailWord_7433735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433735).length < 2 ^ (prefixWord ++ tailWord_7433735).sum := by decide
  have hdescent : baseEnd_7433735 < baseStart_7433735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433745 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 3, 3, 2]
def baseStart_7433745 : Nat := 118140960795 + 7433745 * 2 ^ 59
def prefixEnd_7433745 : Nat := 4983230072969 + 3 ^ 40 * 7433745 * 2
def baseEnd_7433745 : Nat := 3817084247957123172200335

theorem tailTrace_7433745 : CollatzResearch.WordTrace tailWord_7433745 prefixEnd_7433745 3817084247957123172200335 := by
  unfold tailWord_7433745
  simp only [CollatzResearch.WordTrace]
  refine ⟨271130954453818922414478689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180753969635879281609652459 271130954453818922414478689)
  ·
    refine ⟨203348215840364191810859017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271130954453818922414478689 203348215840364191810859017)
    ·
      refine ⟨152511161880273143858144263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203348215840364191810859017 152511161880273143858144263)
      ·
        refine ⟨228766742820409715787216395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152511161880273143858144263 228766742820409715787216395)
        ·
          refine ⟨343150114230614573680824593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228766742820409715787216395 343150114230614573680824593)
          ·
            refine ⟨257362585672960930260618445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343150114230614573680824593 257362585672960930260618445)
            ·
              refine ⟨96510969627360348847731917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257362585672960930260618445 96510969627360348847731917)
              ·
                refine ⟨36191613610260130817899469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96510969627360348847731917 36191613610260130817899469)
                ·
                  refine ⟨13571855103847549056712301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36191613610260130817899469 13571855103847549056712301)
                  ·
                    refine ⟨5089445663942830896267113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13571855103847549056712301 5089445663942830896267113)
                    ·
                      refine ⟨3817084247957123172200335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5089445663942830896267113 3817084247957123172200335)
                      ·
                        rfl

theorem cell23_7433745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 3, 2].length) (baseStart_7433745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433745 prefixEnd_7433745 := by exact prefixLift 7433745
  have htrace : WordTrace (prefixWord ++ tailWord_7433745) baseStart_7433745 baseEnd_7433745 := by
    simpa [prefixWord, tailWord_7433745, baseEnd_7433745] using wordTrace_append hprefix tailTrace_7433745
  have hstable : (prefixWord ++ tailWord_7433745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433745).length < 2 ^ (prefixWord ++ tailWord_7433745).sum := by decide
  have hdescent : baseEnd_7433745 < baseStart_7433745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433778 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_7433778 : Nat := 118140960795 + 7433778 * 2 ^ 59
def prefixEnd_7433778 : Nat := 4983230072969 + 3 ^ 40 * 7433778 * 2
def baseEnd_7433778 : Nat := 3817101192818721543087683

theorem tailTrace_7433778 : CollatzResearch.WordTrace tailWord_7433778 prefixEnd_7433778 3817101192818721543087683 := by
  unfold tailWord_7433778
  simp only [CollatzResearch.WordTrace]
  refine ⟨67783039515674842262607497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180754772041799579366953325 67783039515674842262607497)
  ·
    refine ⟨50837279636756131696955623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67783039515674842262607497 50837279636756131696955623)
    ·
      refine ⟨76255919455134197545433435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50837279636756131696955623 76255919455134197545433435)
      ·
        refine ⟨114383879182701296318150153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76255919455134197545433435 114383879182701296318150153)
        ·
          refine ⟨85787909387025972238612615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114383879182701296318150153 85787909387025972238612615)
          ·
            refine ⟨128681864080538958357918923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85787909387025972238612615 128681864080538958357918923)
            ·
              refine ⟨193022796120808437536878385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128681864080538958357918923 193022796120808437536878385)
              ·
                refine ⟨144767097090606328152658789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193022796120808437536878385 144767097090606328152658789)
                ·
                  refine ⟨27143830704488686528623523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144767097090606328152658789 27143830704488686528623523)
                  ·
                    refine ⟨40715746056733029792935285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27143830704488686528623523 40715746056733029792935285)
                    ·
                      refine ⟨3817101192818721543087683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40715746056733029792935285 3817101192818721543087683)
                      ·
                        rfl

theorem cell23_7433778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_7433778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433778 prefixEnd_7433778 := by exact prefixLift 7433778
  have htrace : WordTrace (prefixWord ++ tailWord_7433778) baseStart_7433778 baseEnd_7433778 := by
    simpa [prefixWord, tailWord_7433778, baseEnd_7433778] using wordTrace_append hprefix tailTrace_7433778
  have hstable : (prefixWord ++ tailWord_7433778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433778).length < 2 ^ (prefixWord ++ tailWord_7433778).sum := by decide
  have hdescent : baseEnd_7433778 < baseStart_7433778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433832 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 7]
def baseStart_7433832 : Nat := 118140960795 + 7433832 * 2 ^ 59
def prefixEnd_7433832 : Nat := 4983230072969 + 3 ^ 40 * 7433832 * 2
def baseEnd_7433832 : Nat := 424125435641562703534715

theorem tailTrace_7433832 : CollatzResearch.WordTrace tailWord_7433832 prefixEnd_7433832 424125435641562703534715 := by
  unfold tailWord_7433832
  simp only [CollatzResearch.WordTrace]
  refine ⟨135567063802251868136447875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180756085069669157515263833 135567063802251868136447875)
  ·
    refine ⟨203350595703377802204671813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135567063802251868136447875 203350595703377802204671813)
    ·
      refine ⟨38128236694383337913375965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203350595703377802204671813 38128236694383337913375965)
      ·
        refine ⟨14298088760393751717515987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38128236694383337913375965 14298088760393751717515987)
        ·
          refine ⟨21447133140590627576273981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14298088760393751717515987 21447133140590627576273981)
          ·
            refine ⟨8042674927721485341102743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21447133140590627576273981 8042674927721485341102743)
            ·
              refine ⟨12064012391582228011654115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8042674927721485341102743 12064012391582228011654115)
              ·
                refine ⟨18096018587373342017481173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12064012391582228011654115 18096018587373342017481173)
                ·
                  refine ⟨424125435641562703534715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18096018587373342017481173 424125435641562703534715)
                  ·
                    rfl

theorem cell23_7433832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 7].length) (baseStart_7433832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433832 prefixEnd_7433832 := by exact prefixLift 7433832
  have htrace : WordTrace (prefixWord ++ tailWord_7433832) baseStart_7433832 baseEnd_7433832 := by
    simpa [prefixWord, tailWord_7433832, baseEnd_7433832] using wordTrace_append hprefix tailTrace_7433832
  have hstable : (prefixWord ++ tailWord_7433832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433832).length < 2 ^ (prefixWord ++ tailWord_7433832).sum := by decide
  have hdescent : baseEnd_7433832 < baseStart_7433832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433865 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 2, 1, 4]
def baseStart_7433865 : Nat := 118140960795 + 7433865 * 2 ^ 59
def prefixEnd_7433865 : Nat := 4983230072969 + 3 ^ 40 * 7433865 * 2
def baseEnd_7433865 : Nat := 3817145865635662702699783

theorem tailTrace_7433865 : CollatzResearch.WordTrace tailWord_7433865 prefixEnd_7433865 3817145865635662702699783 := by
  unfold tailWord_7433865
  simp only [CollatzResearch.WordTrace]
  refine ⟨271135331213384182908847049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180756887475589455272564699 271135331213384182908847049)
  ·
    refine ⟨203351498410038137181635287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271135331213384182908847049 203351498410038137181635287)
    ·
      refine ⟨305027247615057205772452931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203351498410038137181635287 305027247615057205772452931)
      ·
        refine ⟨457540871422585808658679397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305027247615057205772452931 457540871422585808658679397)
        ·
          refine ⟨85788913391734839123502387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 457540871422585808658679397 85788913391734839123502387)
          ·
            refine ⟨128683370087602258685253581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85788913391734839123502387 128683370087602258685253581)
            ·
              refine ⟨48256263782850847006970093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128683370087602258685253581 48256263782850847006970093)
              ·
                refine ⟨18096098918569067627613785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48256263782850847006970093 18096098918569067627613785)
                ·
                  refine ⟨13572074188926800720710339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18096098918569067627613785 13572074188926800720710339)
                  ·
                    refine ⟨20358111283390201081065509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13572074188926800720710339 20358111283390201081065509)
                    ·
                      refine ⟨3817145865635662702699783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20358111283390201081065509 3817145865635662702699783)
                      ·
                        rfl

theorem cell23_7433865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_7433865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433865 prefixEnd_7433865 := by exact prefixLift 7433865
  have htrace : WordTrace (prefixWord ++ tailWord_7433865) baseStart_7433865 baseEnd_7433865 := by
    simpa [prefixWord, tailWord_7433865, baseEnd_7433865] using wordTrace_append hprefix tailTrace_7433865
  have hstable : (prefixWord ++ tailWord_7433865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433865).length < 2 ^ (prefixWord ++ tailWord_7433865).sum := by decide
  have hdescent : baseEnd_7433865 < baseStart_7433865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433885 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_7433885 : Nat := 118140960795 + 7433885 * 2 ^ 59
def prefixEnd_7433885 : Nat := 4983230072969 + 3 ^ 40 * 7433885 * 2
def baseEnd_7433885 : Nat := 3817156135248752624449691

theorem tailTrace_7433885 : CollatzResearch.WordTrace tailWord_7433885 prefixEnd_7433885 3817156135248752624449691 := by
  unfold tailWord_7433885
  simp only [CollatzResearch.WordTrace]
  refine ⟨271136060673311726324575109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180757373782207817549716739 271136060673311726324575109)
  ·
    refine ⟨50838011376245948685857833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271136060673311726324575109 50838011376245948685857833)
    ·
      refine ⟨38128508532184461514393375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50838011376245948685857833 38128508532184461514393375)
      ·
        refine ⟨57192762798276692271590063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38128508532184461514393375 57192762798276692271590063)
        ·
          refine ⟨85789144197415038407385095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57192762798276692271590063 85789144197415038407385095)
          ·
            refine ⟨128683716296122557611077643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85789144197415038407385095 128683716296122557611077643)
            ·
              refine ⟨193025574444183836416616465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128683716296122557611077643 193025574444183836416616465)
              ·
                refine ⟨144769180833137877312462349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193025574444183836416616465 144769180833137877312462349)
                ·
                  refine ⟨54288442812426703992173381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144769180833137877312462349 54288442812426703992173381)
                  ·
                    refine ⟨10179083027330006998532509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54288442812426703992173381 10179083027330006998532509)
                    ·
                      refine ⟨3817156135248752624449691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10179083027330006998532509 3817156135248752624449691)
                      ·
                        rfl

theorem cell23_7433885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_7433885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433885 prefixEnd_7433885 := by exact prefixLift 7433885
  have htrace : WordTrace (prefixWord ++ tailWord_7433885) baseStart_7433885 baseEnd_7433885 := by
    simpa [prefixWord, tailWord_7433885, baseEnd_7433885] using wordTrace_append hprefix tailTrace_7433885
  have hstable : (prefixWord ++ tailWord_7433885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433885).length < 2 ^ (prefixWord ++ tailWord_7433885).sum := by decide
  have hdescent : baseEnd_7433885 < baseStart_7433885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433909 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 3, 4]
def baseStart_7433909 : Nat := 118140960795 + 7433909 * 2 ^ 59
def prefixEnd_7433909 : Nat := 4983230072969 + 3 ^ 40 * 7433909 * 2
def baseEnd_7433909 : Nat := 1272389486261486843516527

theorem tailTrace_7433909 : CollatzResearch.WordTrace tailWord_7433909 prefixEnd_7433909 1272389486261486843516527 := by
  unfold tailWord_7433909
  simp only [CollatzResearch.WordTrace]
  refine ⟨271136936025224778423448781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180757957350149852282299187 271136936025224778423448781)
  ·
    refine ⟨101676351009459291908793293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271136936025224778423448781 101676351009459291908793293)
    ·
      refine ⟨38128631628547234465797485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101676351009459291908793293 38128631628547234465797485)
      ·
        refine ⟨14298236860705212924674057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38128631628547234465797485 14298236860705212924674057)
        ·
          refine ⟨10723677645528909693505543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14298236860705212924674057 10723677645528909693505543)
          ·
            refine ⟨16085516468293364540258315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10723677645528909693505543 16085516468293364540258315)
            ·
              refine ⟨24128274702440046810387473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16085516468293364540258315 24128274702440046810387473)
              ·
                refine ⟨18096206026830035107790605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24128274702440046810387473 18096206026830035107790605)
                ·
                  refine ⟨6786077260061263165421477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18096206026830035107790605 6786077260061263165421477)
                  ·
                    refine ⟨1272389486261486843516527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6786077260061263165421477 1272389486261486843516527)
                    ·
                      rfl

theorem cell23_7433909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_7433909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433909 prefixEnd_7433909 := by exact prefixLift 7433909
  have htrace : WordTrace (prefixWord ++ tailWord_7433909) baseStart_7433909 baseEnd_7433909 := by
    simpa [prefixWord, tailWord_7433909, baseEnd_7433909] using wordTrace_append hprefix tailTrace_7433909
  have hstable : (prefixWord ++ tailWord_7433909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433909).length < 2 ^ (prefixWord ++ tailWord_7433909).sum := by decide
  have hdescent : baseEnd_7433909 < baseStart_7433909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7433992 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_7433992 : Nat := 118140960795 + 7433992 * 2 ^ 59
def prefixEnd_7433992 : Nat := 4983230072969 + 3 ^ 40 * 7433992 * 2
def baseEnd_7433992 : Nat := 3817211077678783705811699

theorem tailTrace_7433992 : CollatzResearch.WordTrace tailWord_7433992 prefixEnd_7433992 3817211077678783705811699 := by
  unfold tailWord_7433992
  simp only [CollatzResearch.WordTrace]
  refine ⟨135569981641962041799360115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180759975522616055732480153 135569981641962041799360115)
  ·
    refine ⟨203354972462943062699040173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135569981641962041799360115 203354972462943062699040173)
    ·
      refine ⟨76258114673603648512140065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203354972462943062699040173 76258114673603648512140065)
      ·
        refine ⟨57193586005202736384105049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76258114673603648512140065 57193586005202736384105049)
        ·
          refine ⟨42895189503902052288078787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57193586005202736384105049 42895189503902052288078787)
          ·
            refine ⟨64342784255853078432118181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42895189503902052288078787 64342784255853078432118181)
            ·
              refine ⟨12064272047972452206022159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64342784255853078432118181 12064272047972452206022159)
              ·
                refine ⟨18096408071958678309033239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12064272047972452206022159 18096408071958678309033239)
                ·
                  refine ⟨27144612107938017463549859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18096408071958678309033239 27144612107938017463549859)
                  ·
                    refine ⟨40716918161907026195324789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27144612107938017463549859 40716918161907026195324789)
                    ·
                      refine ⟨3817211077678783705811699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40716918161907026195324789 3817211077678783705811699)
                      ·
                        rfl

theorem cell23_7433992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_7433992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7433992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7433992 prefixEnd_7433992 := by exact prefixLift 7433992
  have htrace : WordTrace (prefixWord ++ tailWord_7433992) baseStart_7433992 baseEnd_7433992 := by
    simpa [prefixWord, tailWord_7433992, baseEnd_7433992] using wordTrace_append hprefix tailTrace_7433992
  have hstable : (prefixWord ++ tailWord_7433992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7433992).length < 2 ^ (prefixWord ++ tailWord_7433992).sum := by decide
  have hdescent : baseEnd_7433992 < baseStart_7433992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7433992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434015 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 6]
def baseStart_7434015 : Nat := 118140960795 + 7434015 * 2 ^ 59
def prefixEnd_7434015 : Nat := 4983230072969 + 3 ^ 40 * 7434015 * 2
def baseEnd_7434015 : Nat := 3817222887733837115824093

theorem tailTrace_7434015 : CollatzResearch.WordTrace tailWord_7434015 prefixEnd_7434015 3817222887733837115824093 := by
  unfold tailWord_7434015
  simp only [CollatzResearch.WordTrace]
  refine ⟨271140802162840758526807499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180760534775227172351204999 271140802162840758526807499)
  ·
    refine ⟨406711203244261137790211249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271140802162840758526807499 406711203244261137790211249)
    ·
      refine ⟨305033402433195853342658437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406711203244261137790211249 305033402433195853342658437)
      ·
        refine ⟨57193762956224222501748457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305033402433195853342658437 57193762956224222501748457)
        ·
          refine ⟨42895322217168166876311343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57193762956224222501748457 42895322217168166876311343)
          ·
            refine ⟨64342983325752250314467015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42895322217168166876311343 64342983325752250314467015)
            ·
              refine ⟨96514474988628375471700523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64342983325752250314467015 96514474988628375471700523)
              ·
                refine ⟨144771712482942563207550785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96514474988628375471700523 144771712482942563207550785)
                ·
                  refine ⟨108578784362206922405663089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144771712482942563207550785 108578784362206922405663089)
                  ·
                    refine ⟨81434088271655191804247317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108578784362206922405663089 81434088271655191804247317)
                    ·
                      refine ⟨3817222887733837115824093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81434088271655191804247317 3817222887733837115824093)
                      ·
                        rfl

theorem cell23_7434015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_7434015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434015 prefixEnd_7434015 := by exact prefixLift 7434015
  have htrace : WordTrace (prefixWord ++ tailWord_7434015) baseStart_7434015 baseEnd_7434015 := by
    simpa [prefixWord, tailWord_7434015, baseEnd_7434015] using wordTrace_append hprefix tailTrace_7434015
  have hstable : (prefixWord ++ tailWord_7434015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434015).length < 2 ^ (prefixWord ++ tailWord_7434015).sum := by decide
  have hdescent : baseEnd_7434015 < baseStart_7434015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434056 : List Nat := [2, 1, 3, 1, 1, 5, 2, 2, 2, 1, 3]
def baseStart_7434056 : Nat := 118140960795 + 7434056 * 2 ^ 59
def prefixEnd_7434056 : Nat := 4983230072969 + 3 ^ 40 * 7434056 * 2
def baseEnd_7434056 : Nat := 3817243940440671455411405

theorem tailTrace_7434056 : CollatzResearch.WordTrace tailWord_7434056 prefixEnd_7434056 3817243940440671455411405 := by
  unfold tailWord_7434056
  simp only [CollatzResearch.WordTrace]
  refine ⟨135571148777846111264525011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180761531703794815019366681 135571148777846111264525011)
  ·
    refine ⟨203356723166769166896787517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135571148777846111264525011 203356723166769166896787517)
    ·
      refine ⟨76258771187538437586295319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203356723166769166896787517 76258771187538437586295319)
      ·
        refine ⟨114388156781307656379442979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76258771187538437586295319 114388156781307656379442979)
        ·
          refine ⟨171582235171961484569164469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114388156781307656379442979 171582235171961484569164469)
          ·
            refine ⟨16085834547371389178359169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171582235171961484569164469 16085834547371389178359169)
            ·
              refine ⟨12064375910528541883769377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16085834547371389178359169 12064375910528541883769377)
              ·
                refine ⟨9048281932896406412827033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12064375910528541883769377 9048281932896406412827033)
                ·
                  refine ⟨6786211449672304809620275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9048281932896406412827033 6786211449672304809620275)
                  ·
                    refine ⟨10179317174508457214430413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6786211449672304809620275 10179317174508457214430413)
                    ·
                      refine ⟨3817243940440671455411405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10179317174508457214430413 3817243940440671455411405)
                      ·
                        rfl

theorem cell23_7434056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_7434056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434056 prefixEnd_7434056 := by exact prefixLift 7434056
  have htrace : WordTrace (prefixWord ++ tailWord_7434056) baseStart_7434056 baseEnd_7434056 := by
    simpa [prefixWord, tailWord_7434056, baseEnd_7434056] using wordTrace_append hprefix tailTrace_7434056
  have hstable : (prefixWord ++ tailWord_7434056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434056).length < 2 ^ (prefixWord ++ tailWord_7434056).sum := by decide
  have hdescent : baseEnd_7434056 < baseStart_7434056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434079 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 1, 4, 2]
def baseStart_7434079 : Nat := 118140960795 + 7434079 * 2 ^ 59
def prefixEnd_7434079 : Nat := 4983230072969 + 3 ^ 40 * 7434079 * 2
def baseEnd_7434079 : Nat := 3817255750495724865423799

theorem tailTrace_7434079 : CollatzResearch.WordTrace tailWord_7434079 prefixEnd_7434079 3817255750495724865423799 := by
  unfold tailWord_7434079
  simp only [CollatzResearch.WordTrace]
  refine ⟨271143136434608897457137291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180762090956405931638091527 271143136434608897457137291)
  ·
    refine ⟨406714704651913346185705937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271143136434608897457137291 406714704651913346185705937)
    ·
      refine ⟨305036028488935009639279453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406714704651913346185705937 305036028488935009639279453)
      ·
        refine ⟨114388510683350628614729795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305036028488935009639279453 114388510683350628614729795)
        ·
          refine ⟨171582766025025942922094693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114388510683350628614729795 171582766025025942922094693)
          ·
            refine ⟨32171768629692364297892755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171582766025025942922094693 32171768629692364297892755)
            ·
              refine ⟨48257652944538546446839133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32171768629692364297892755 48257652944538546446839133)
              ·
                refine ⟨18096619854201954917564675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48257652944538546446839133 18096619854201954917564675)
                ·
                  refine ⟨27144929781302932376347013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18096619854201954917564675 27144929781302932376347013)
                  ·
                    refine ⟨5089674333994299820565065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27144929781302932376347013 5089674333994299820565065)
                    ·
                      refine ⟨3817255750495724865423799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5089674333994299820565065 3817255750495724865423799)
                      ·
                        rfl

theorem cell23_7434079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_7434079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434079 prefixEnd_7434079 := by exact prefixLift 7434079
  have htrace : WordTrace (prefixWord ++ tailWord_7434079) baseStart_7434079 baseEnd_7434079 := by
    simpa [prefixWord, tailWord_7434079, baseEnd_7434079] using wordTrace_append hprefix tailTrace_7434079
  have hstable : (prefixWord ++ tailWord_7434079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434079).length < 2 ^ (prefixWord ++ tailWord_7434079).sum := by decide
  have hdescent : baseEnd_7434079 < baseStart_7434079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434095 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 7]
def baseStart_7434095 : Nat := 118140960795 + 7434095 * 2 ^ 59
def prefixEnd_7434095 : Nat := 4983230072969 + 3 ^ 40 * 7434095 * 2
def baseEnd_7434095 : Nat := 3817263966186196802823725

theorem tailTrace_7434095 : CollatzResearch.WordTrace tailWord_7434095 prefixEnd_7434095 3817263966186196802823725 := by
  unfold tailWord_7434095
  simp only [CollatzResearch.WordTrace]
  refine ⟨271143720002550932189719739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180762480001700621459813159 271143720002550932189719739)
  ·
    refine ⟨406715580003826398284579609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271143720002550932189719739 406715580003826398284579609)
    ·
      refine ⟨305036685002869798713434707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406715580003826398284579609 305036685002869798713434707)
      ·
        refine ⟨457555027504304698070152061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305036685002869798713434707 457555027504304698070152061)
        ·
          refine ⟨171583135314114261776307023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457555027504304698070152061 171583135314114261776307023)
          ·
            refine ⟨257374702971171392664460535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171583135314114261776307023 257374702971171392664460535)
            ·
              refine ⟨386062054456757088996690803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257374702971171392664460535 386062054456757088996690803)
              ·
                refine ⟨579093081685135633495036205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386062054456757088996690803 579093081685135633495036205)
                ·
                  refine ⟨217159905631925862560638577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579093081685135633495036205 217159905631925862560638577)
                  ·
                    refine ⟨162869929223944396920478933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 217159905631925862560638577 162869929223944396920478933)
                    ·
                      refine ⟨3817263966186196802823725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162869929223944396920478933 3817263966186196802823725)
                      ·
                        rfl

theorem cell23_7434095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_7434095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434095 prefixEnd_7434095 := by exact prefixLift 7434095
  have htrace : WordTrace (prefixWord ++ tailWord_7434095) baseStart_7434095 baseEnd_7434095 := by
    simpa [prefixWord, tailWord_7434095, baseEnd_7434095] using wordTrace_append hprefix tailTrace_7434095
  have hstable : (prefixWord ++ tailWord_7434095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434095).length < 2 ^ (prefixWord ++ tailWord_7434095).sum := by decide
  have hdescent : baseEnd_7434095 < baseStart_7434095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434112 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 3]
def baseStart_7434112 : Nat := 118140960795 + 7434112 * 2 ^ 59
def prefixEnd_7434112 : Nat := 4983230072969 + 3 ^ 40 * 7434112 * 2
def baseEnd_7434112 : Nat := 3817272695357323236311147

theorem tailTrace_7434112 : CollatzResearch.WordTrace tailWord_7434112 prefixEnd_7434112 3817272695357323236311147 := by
  unfold tailWord_7434112
  simp only [CollatzResearch.WordTrace]
  refine ⟨135572170021744672046544295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180762893362326229395392393 135572170021744672046544295)
  ·
    refine ⟨203358255032617008069816443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135572170021744672046544295 203358255032617008069816443)
    ·
      refine ⟨305037382548925512104724665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203358255032617008069816443 305037382548925512104724665)
      ·
        refine ⟨228778036911694134078543499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305037382548925512104724665 228778036911694134078543499)
        ·
          refine ⟨343167055367541201117815249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228778036911694134078543499 343167055367541201117815249)
          ·
            refine ⟨257375291525655900838361437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343167055367541201117815249 257375291525655900838361437)
            ·
              refine ⟨96515734322120962814385539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257375291525655900838361437 96515734322120962814385539)
              ·
                refine ⟨144773601483181444221578309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96515734322120962814385539 144773601483181444221578309)
                ·
                  refine ⟨27145050278096520791545933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144773601483181444221578309 27145050278096520791545933)
                  ·
                    refine ⟨10179393854286195296829725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27145050278096520791545933 10179393854286195296829725)
                    ·
                      refine ⟨3817272695357323236311147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10179393854286195296829725 3817272695357323236311147)
                      ·
                        rfl

theorem cell23_7434112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_7434112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434112 prefixEnd_7434112 := by exact prefixLift 7434112
  have htrace : WordTrace (prefixWord ++ tailWord_7434112) baseStart_7434112 baseEnd_7434112 := by
    simpa [prefixWord, tailWord_7434112, baseEnd_7434112] using wordTrace_append hprefix tailTrace_7434112
  have hstable : (prefixWord ++ tailWord_7434112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434112).length < 2 ^ (prefixWord ++ tailWord_7434112).sum := by decide
  have hdescent : baseEnd_7434112 < baseStart_7434112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434119 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 7]
def baseStart_7434119 : Nat := 118140960795 + 7434119 * 2 ^ 59
def prefixEnd_7434119 : Nat := 4983230072969 + 3 ^ 40 * 7434119 * 2
def baseEnd_7434119 : Nat := 424141809969100523213735

theorem tailTrace_7434119 : CollatzResearch.WordTrace tailWord_7434119 prefixEnd_7434119 424141809969100523213735 := by
  unfold tailWord_7434119
  simp only [CollatzResearch.WordTrace]
  refine ⟨271144595354463984288593411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180763063569642656192395607 271144595354463984288593411)
  ·
    refine ⟨406716893031695976432890117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271144595354463984288593411 406716893031695976432890117)
    ·
      refine ⟨76259417443442995581166897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 406716893031695976432890117 76259417443442995581166897)
      ·
        refine ⟨57194563082582246685875173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76259417443442995581166897 57194563082582246685875173)
        ·
          refine ⟨10723980577984171253601595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57194563082582246685875173 10723980577984171253601595)
          ·
            refine ⟨16085970866976256880402393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10723980577984171253601595 16085970866976256880402393)
            ·
              refine ⟨12064478150232192660301795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16085970866976256880402393 12064478150232192660301795)
              ·
                refine ⟨18096717225348288990452693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12064478150232192660301795 18096717225348288990452693)
                ·
                  refine ⟨424141809969100523213735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18096717225348288990452693 424141809969100523213735)
                  ·
                    rfl

theorem cell23_7434119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 7].length) (baseStart_7434119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434119 prefixEnd_7434119 := by exact prefixLift 7434119
  have htrace : WordTrace (prefixWord ++ tailWord_7434119) baseStart_7434119 baseEnd_7434119 := by
    simpa [prefixWord, tailWord_7434119, baseEnd_7434119] using wordTrace_append hprefix tailTrace_7434119
  have hstable : (prefixWord ++ tailWord_7434119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434119).length < 2 ^ (prefixWord ++ tailWord_7434119).sum := by decide
  have hdescent : baseEnd_7434119 < baseStart_7434119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434169 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 2, 1, 4]
def baseStart_7434169 : Nat := 118140960795 + 7434169 * 2 ^ 59
def prefixEnd_7434169 : Nat := 4983230072969 + 3 ^ 40 * 7434169 * 2
def baseEnd_7434169 : Nat := 3817301963754629513298385

theorem tailTrace_7434169 : CollatzResearch.WordTrace tailWord_7434169 prefixEnd_7434169 3817301963754629513298385 := by
  unfold tailWord_7434169
  simp only [CollatzResearch.WordTrace]
  refine ⟨271146419004282842827913561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180764279336188561885275707 271146419004282842827913561)
  ·
    refine ⟨203359814253212132120935171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271146419004282842827913561 203359814253212132120935171)
    ·
      refine ⟨305039721379818198181402757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203359814253212132120935171 305039721379818198181402757)
      ·
        refine ⟨57194947758715912159013017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305039721379818198181402757 57194947758715912159013017)
        ·
          refine ⟨42896210819036934119259763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57194947758715912159013017 42896210819036934119259763)
          ·
            refine ⟨64344316228555401178889645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42896210819036934119259763 64344316228555401178889645)
            ·
              refine ⟨24129118585708275442083617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64344316228555401178889645 24129118585708275442083617)
              ·
                refine ⟨18096838939281206581562713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24129118585708275442083617 18096838939281206581562713)
                ·
                  refine ⟨13572629204460904936172035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18096838939281206581562713 13572629204460904936172035)
                  ·
                    refine ⟨20358943806691357404258053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13572629204460904936172035 20358943806691357404258053)
                    ·
                      refine ⟨3817301963754629513298385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20358943806691357404258053 3817301963754629513298385)
                      ·
                        rfl

theorem cell23_7434169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_7434169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434169 prefixEnd_7434169 := by exact prefixLift 7434169
  have htrace : WordTrace (prefixWord ++ tailWord_7434169) baseStart_7434169 baseEnd_7434169 := by
    simpa [prefixWord, tailWord_7434169, baseEnd_7434169] using wordTrace_append hprefix tailTrace_7434169
  have hstable : (prefixWord ++ tailWord_7434169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434169).length < 2 ^ (prefixWord ++ tailWord_7434169).sum := by decide
  have hdescent : baseEnd_7434169 < baseStart_7434169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434230 : List Nat := [5, 1, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_7434230 : Nat := 118140960795 + 7434230 * 2 ^ 59
def prefixEnd_7434230 : Nat := 4983230072969 + 3 ^ 40 * 7434230 * 2
def baseEnd_7434230 : Nat := 1272444428691517924878535

theorem tailTrace_7434230 : CollatzResearch.WordTrace tailWord_7434230 prefixEnd_7434230 1272444428691517924878535 := by
  unfold tailWord_7434230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16946790241066365640367759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180765762571374566830589429 16946790241066365640367759)
  ·
    refine ⟨25420185361599548460551639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16946790241066365640367759 25420185361599548460551639)
    ·
      refine ⟨38130278042399322690827459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25420185361599548460551639 38130278042399322690827459)
      ·
        refine ⟨57195417063598984036241189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38130278042399322690827459 57195417063598984036241189)
        ·
          refine ⟨10724140699424809506795223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57195417063598984036241189 10724140699424809506795223)
          ·
            refine ⟨16086211049137214260192835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10724140699424809506795223 16086211049137214260192835)
            ·
              refine ⟨24129316573705821390289253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16086211049137214260192835 24129316573705821390289253)
              ·
                refine ⟨4524246857569841510679235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24129316573705821390289253 4524246857569841510679235)
                ·
                  refine ⟨6786370286354762266018853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4524246857569841510679235 6786370286354762266018853)
                  ·
                    refine ⟨1272444428691517924878535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6786370286354762266018853 1272444428691517924878535)
                    ·
                      rfl

theorem cell23_7434230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_7434230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434230 prefixEnd_7434230 := by exact prefixLift 7434230
  have htrace : WordTrace (prefixWord ++ tailWord_7434230) baseStart_7434230 baseEnd_7434230 := by
    simpa [prefixWord, tailWord_7434230, baseEnd_7434230] using wordTrace_append hprefix tailTrace_7434230
  have hstable : (prefixWord ++ tailWord_7434230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434230).length < 2 ^ (prefixWord ++ tailWord_7434230).sum := by decide
  have hdescent : baseEnd_7434230 < baseStart_7434230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434236 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 3, 1, 3]
def baseStart_7434236 : Nat := 118140960795 + 7434236 * 2 ^ 59
def prefixEnd_7434236 : Nat := 4983230072969 + 3 ^ 40 * 7434236 * 2
def baseEnd_7434236 : Nat := 3817336366958480751160577

theorem tailTrace_7434236 : CollatzResearch.WordTrace tailWord_7434236 prefixEnd_7434236 3817336366958480751160577 := by
  unfold tailWord_7434236
  simp only [CollatzResearch.WordTrace]
  refine ⟨135574431347520056635301281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180765908463360075513735041 135574431347520056635301281)
  ·
    refine ⟨101680823510640042476475961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135574431347520056635301281 101680823510640042476475961)
    ·
      refine ⟨76260617632980031857356971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101680823510640042476475961 76260617632980031857356971)
      ·
        refine ⟨114390926449470047786035457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76260617632980031857356971 114390926449470047786035457)
        ·
          refine ⟨85793194837102535839526593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114390926449470047786035457 85793194837102535839526593)
          ·
            refine ⟨64344896127826901879644945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85793194837102535839526593 64344896127826901879644945)
            ·
              refine ⟨48258672095870176409733709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64344896127826901879644945 48258672095870176409733709)
              ·
                refine ⟨18097002035951316153650141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48258672095870176409733709 18097002035951316153650141)
                ·
                  refine ⟨6786375763481743557618803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18097002035951316153650141 6786375763481743557618803)
                  ·
                    refine ⟨10179563645222615336428205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6786375763481743557618803 10179563645222615336428205)
                    ·
                      refine ⟨3817336366958480751160577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10179563645222615336428205 3817336366958480751160577)
                      ·
                        rfl

theorem cell23_7434236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_7434236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434236 prefixEnd_7434236 := by exact prefixLift 7434236
  have htrace : WordTrace (prefixWord ++ tailWord_7434236) baseStart_7434236 baseEnd_7434236 := by
    simpa [prefixWord, tailWord_7434236, baseEnd_7434236] using wordTrace_append hprefix tailTrace_7434236
  have hstable : (prefixWord ++ tailWord_7434236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434236).length < 2 ^ (prefixWord ++ tailWord_7434236).sum := by decide
  have hdescent : baseEnd_7434236 < baseStart_7434236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434259 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 4]
def baseStart_7434259 : Nat := 118140960795 + 7434259 * 2 ^ 59
def prefixEnd_7434259 : Nat := 4983230072969 + 3 ^ 40 * 7434259 * 2
def baseEnd_7434259 : Nat := 3817348177013534161172971

theorem tailTrace_7434259 : CollatzResearch.WordTrace tailWord_7434259 prefixEnd_7434259 3817348177013534161172971 := by
  unfold tailWord_7434259
  simp only [CollatzResearch.WordTrace]
  refine ⟨271149701573956788198689831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180766467715971192132459887 271149701573956788198689831)
  ·
    refine ⟨406724552360935182298034747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271149701573956788198689831 406724552360935182298034747)
    ·
      refine ⟨610086828541402773447052121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406724552360935182298034747 610086828541402773447052121)
      ·
        refine ⟨457565121406052080085289091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610086828541402773447052121 457565121406052080085289091)
        ·
          refine ⟨686347682109078120127933637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457565121406052080085289091 686347682109078120127933637)
          ·
            refine ⟨128690190395452147523987557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 686347682109078120127933637 128690190395452147523987557)
            ·
              refine ⟨24129410699147277660747667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128690190395452147523987557 24129410699147277660747667)
              ·
                refine ⟨36194116048720916491121501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24129410699147277660747667 36194116048720916491121501)
                ·
                  refine ⟨13572793518270343684170563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36194116048720916491121501 13572793518270343684170563)
                  ·
                    refine ⟨20359190277405515526255845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13572793518270343684170563 20359190277405515526255845)
                    ·
                      refine ⟨3817348177013534161172971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20359190277405515526255845 3817348177013534161172971)
                      ·
                        rfl

theorem cell23_7434259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_7434259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434259 prefixEnd_7434259 := by exact prefixLift 7434259
  have htrace : WordTrace (prefixWord ++ tailWord_7434259) baseStart_7434259 baseEnd_7434259 := by
    simpa [prefixWord, tailWord_7434259, baseEnd_7434259] using wordTrace_append hprefix tailTrace_7434259
  have hstable : (prefixWord ++ tailWord_7434259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434259).length < 2 ^ (prefixWord ++ tailWord_7434259).sum := by decide
  have hdescent : baseEnd_7434259 < baseStart_7434259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
