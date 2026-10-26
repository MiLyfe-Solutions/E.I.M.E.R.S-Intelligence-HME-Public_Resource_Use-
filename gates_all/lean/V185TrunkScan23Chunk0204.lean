import V185TrunkScan23Chunk0203

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1206902 : List Nat := [5, 1, 1, 2, 4, 1, 1, 8]
def baseStart_1206902 : Nat := 118140960795 + 1206902 * 2 ^ 59
def prefixEnd_1206902 : Nat := 4983230072969 + 3 ^ 40 * 1206902 * 2
def baseEnd_1206902 : Nat := 22952623291583045336095

theorem tailTrace_1206902 : CollatzResearch.WordTrace tailWord_1206902 prefixEnd_1206902 22952623291583045336095 := by
  unfold tailWord_1206902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2751208267100478206028935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29346221515738434197641973 2751208267100478206028935)
  ·
    refine ⟨4126812400650717309043403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2751208267100478206028935 4126812400650717309043403)
    ·
      refine ⟨6190218600976075963565105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4126812400650717309043403 6190218600976075963565105)
      ·
        refine ⟨4642663950732056972673829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6190218600976075963565105 4642663950732056972673829)
        ·
          refine ⟨870499490762260682376343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4642663950732056972673829 870499490762260682376343)
          ·
            refine ⟨1305749236143391023564515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870499490762260682376343 1305749236143391023564515)
            ·
              refine ⟨1958623854215086535346773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305749236143391023564515 1958623854215086535346773)
              ·
                refine ⟨22952623291583045336095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1958623854215086535346773 22952623291583045336095)
                ·
                  rfl

theorem cell23_1206902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_1206902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206902 prefixEnd_1206902 := by exact prefixLift 1206902
  have htrace : WordTrace (prefixWord ++ tailWord_1206902) baseStart_1206902 baseEnd_1206902 := by
    simpa [prefixWord, tailWord_1206902, baseEnd_1206902] using wordTrace_append hprefix tailTrace_1206902
  have hstable : (prefixWord ++ tailWord_1206902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206902).length < 2 ^ (prefixWord ++ tailWord_1206902).sum := by decide
  have hdescent : baseEnd_1206902 < baseStart_1206902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206905 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 3, 3, 2]
def baseStart_1206905 : Nat := 118140960795 + 1206905 * 2 ^ 59
def prefixEnd_1206905 : Nat := 4983230072969 + 3 ^ 40 * 1206905 * 2
def baseEnd_1206905 : Nat := 619722369314705712337051

theorem tailTrace_1206905 : CollatzResearch.WordTrace tailWord_1206905 prefixEnd_1206905 619722369314705712337051 := by
  unfold tailWord_1206905
  simp only [CollatzResearch.WordTrace]
  refine ⟨44019441692596782808822169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29346294461731188539214779 44019441692596782808822169)
  ·
    refine ⟨33014581269447587106616627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44019441692596782808822169 33014581269447587106616627)
    ·
      refine ⟨49521871904171380659924941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33014581269447587106616627 49521871904171380659924941)
      ·
        refine ⟨18570701964064267747471853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49521871904171380659924941 18570701964064267747471853)
        ·
          refine ⟨6964013236524100405301945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18570701964064267747471853 6964013236524100405301945)
          ·
            refine ⟨5223009927393075303976459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6964013236524100405301945 5223009927393075303976459)
            ·
              refine ⟨7834514891089612955964689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5223009927393075303976459 7834514891089612955964689)
              ·
                refine ⟨5875886168317209716973517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7834514891089612955964689 5875886168317209716973517)
                ·
                  refine ⟨2203457313118953643865069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5875886168317209716973517 2203457313118953643865069)
                  ·
                    refine ⟨826296492419607616449401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2203457313118953643865069 826296492419607616449401)
                    ·
                      refine ⟨619722369314705712337051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 826296492419607616449401 619722369314705712337051)
                      ·
                        rfl

theorem cell23_1206905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_1206905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206905 prefixEnd_1206905 := by exact prefixLift 1206905
  have htrace : WordTrace (prefixWord ++ tailWord_1206905) baseStart_1206905 baseEnd_1206905 := by
    simpa [prefixWord, tailWord_1206905, baseEnd_1206905] using wordTrace_append hprefix tailTrace_1206905
  have hstable : (prefixWord ++ tailWord_1206905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206905).length < 2 ^ (prefixWord ++ tailWord_1206905).sum := by decide
  have hdescent : baseEnd_1206905 < baseStart_1206905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206935 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 1, 4, 2]
def baseStart_1206935 : Nat := 118140960795 + 1206935 * 2 ^ 59
def prefixEnd_1206935 : Nat := 4983230072969 + 3 ^ 40 * 1206935 * 2
def baseEnd_1206935 : Nat := 619737773734340594961913

theorem tailTrace_1206935 : CollatzResearch.WordTrace tailWord_1206935 prefixEnd_1206935 619737773734340594961913 := by
  unfold tailWord_1206935
  simp only [CollatzResearch.WordTrace]
  refine ⟨44020535882488097932414259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29347023921658731954942839 44020535882488097932414259)
  ·
    refine ⟨66030803823732146898621389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44020535882488097932414259 66030803823732146898621389)
    ·
      refine ⟨24761551433899555086983021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66030803823732146898621389 24761551433899555086983021)
      ·
        refine ⟨9285581787712333157618633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24761551433899555086983021 9285581787712333157618633)
        ·
          refine ⟨6964186340784249868213975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9285581787712333157618633 6964186340784249868213975)
          ·
            refine ⟨10446279511176374802320963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6964186340784249868213975 10446279511176374802320963)
            ·
              refine ⟨15669419266764562203481445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10446279511176374802320963 15669419266764562203481445)
              ·
                refine ⟨2938016112518355413152771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15669419266764562203481445 2938016112518355413152771)
                ·
                  refine ⟨4407024168777533119729157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938016112518355413152771 4407024168777533119729157)
                  ·
                    refine ⟨826317031645787459949217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4407024168777533119729157 826317031645787459949217)
                    ·
                      refine ⟨619737773734340594961913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 826317031645787459949217 619737773734340594961913)
                      ·
                        rfl

theorem cell23_1206935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_1206935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206935 prefixEnd_1206935 := by exact prefixLift 1206935
  have htrace : WordTrace (prefixWord ++ tailWord_1206935) baseStart_1206935 baseEnd_1206935 := by
    simpa [prefixWord, tailWord_1206935, baseEnd_1206935] using wordTrace_append hprefix tailTrace_1206935
  have hstable : (prefixWord ++ tailWord_1206935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206935).length < 2 ^ (prefixWord ++ tailWord_1206935).sum := by decide
  have hdescent : baseEnd_1206935 < baseStart_1206935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206948 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_1206948 : Nat := 118140960795 + 1206948 * 2 ^ 59
def prefixEnd_1206948 : Nat := 4983230072969 + 3 ^ 40 * 1206948 * 2
def baseEnd_1206948 : Nat := 619744448982849044099353

theorem tailTrace_1206948 : CollatzResearch.WordTrace tailWord_1206948 prefixEnd_1206948 619744448982849044099353 := by
  unfold tailWord_1206948
  simp only [CollatzResearch.WordTrace]
  refine ⟨22010505015720500576318749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29347340020960667435091665 22010505015720500576318749)
  ·
    refine ⟨8253939380895187716119531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22010505015720500576318749 8253939380895187716119531)
    ·
      refine ⟨12380909071342781574179297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8253939380895187716119531 12380909071342781574179297)
      ·
        refine ⟨9285681803507086180634473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12380909071342781574179297 9285681803507086180634473)
        ·
          refine ⟨6964261352630314635475855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9285681803507086180634473 6964261352630314635475855)
          ·
            refine ⟨10446392028945471953213783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6964261352630314635475855 10446392028945471953213783)
            ·
              refine ⟨15669588043418207929820675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10446392028945471953213783 15669588043418207929820675)
              ·
                refine ⟨23504382065127311894731013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15669588043418207929820675 23504382065127311894731013)
                ·
                  refine ⟨4407071637211370980262065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23504382065127311894731013 4407071637211370980262065)
                  ·
                    refine ⟨3305303727908528235196549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4407071637211370980262065 3305303727908528235196549)
                    ·
                      refine ⟨619744448982849044099353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3305303727908528235196549 619744448982849044099353)
                      ·
                        rfl

theorem cell23_1206948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_1206948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206948 prefixEnd_1206948 := by exact prefixLift 1206948
  have htrace : WordTrace (prefixWord ++ tailWord_1206948) baseStart_1206948 baseEnd_1206948 := by
    simpa [prefixWord, tailWord_1206948, baseEnd_1206948] using wordTrace_append hprefix tailTrace_1206948
  have hstable : (prefixWord ++ tailWord_1206948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206948).length < 2 ^ (prefixWord ++ tailWord_1206948).sum := by decide
  have hdescent : baseEnd_1206948 < baseStart_1206948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206965 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1206965 : Nat := 118140960795 + 1206965 * 2 ^ 59
def prefixEnd_1206965 : Nat := 4983230072969 + 3 ^ 40 * 1206965 * 2
def baseEnd_1206965 : Nat := 619753178153975477586775

theorem tailTrace_1206965 : CollatzResearch.WordTrace tailWord_1206965 prefixEnd_1206965 619753178153975477586775 := by
  unfold tailWord_1206965
  simp only [CollatzResearch.WordTrace]
  refine ⟨44021630072379413056006349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29347753381586275370670899 44021630072379413056006349)
  ·
    refine ⟨16508111277142279896002381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44021630072379413056006349 16508111277142279896002381)
    ·
      refine ⟨6190541728928354961000893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16508111277142279896002381 6190541728928354961000893)
      ·
        refine ⟨2321453148348133110375335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6190541728928354961000893 2321453148348133110375335)
        ·
          refine ⟨3482179722522199665563003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2321453148348133110375335 3482179722522199665563003)
          ·
            refine ⟨5223269583783299498344505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3482179722522199665563003 5223269583783299498344505)
            ·
              refine ⟨3917452187837474623758379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5223269583783299498344505 3917452187837474623758379)
              ·
                refine ⟨5876178281756211935637569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3917452187837474623758379 5876178281756211935637569)
                ·
                  refine ⟨4407133711317158951728177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5876178281756211935637569 4407133711317158951728177)
                  ·
                    refine ⟨3305350283487869213796133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4407133711317158951728177 3305350283487869213796133)
                    ·
                      refine ⟨619753178153975477586775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3305350283487869213796133 619753178153975477586775)
                      ·
                        rfl

theorem cell23_1206965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1206965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1206965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1206965 prefixEnd_1206965 := by exact prefixLift 1206965
  have htrace : WordTrace (prefixWord ++ tailWord_1206965) baseStart_1206965 baseEnd_1206965 := by
    simpa [prefixWord, tailWord_1206965, baseEnd_1206965] using wordTrace_append hprefix tailTrace_1206965
  have hstable : (prefixWord ++ tailWord_1206965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206965).length < 2 ^ (prefixWord ++ tailWord_1206965).sum := by decide
  have hdescent : baseEnd_1206965 < baseStart_1206965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207025 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 1, 6, 2]
def baseStart_1207025 : Nat := 118140960795 + 1207025 * 2 ^ 59
def prefixEnd_1207025 : Nat := 4983230072969 + 3 ^ 40 * 1207025 * 2
def baseEnd_1207025 : Nat := 619783986993245242836499

theorem tailTrace_1207025 : CollatzResearch.WordTrace tailWord_1207025 prefixEnd_1207025 619783986993245242836499 := by
  unfold tailWord_1207025
  simp only [CollatzResearch.WordTrace]
  refine ⟨44023818452162043303190529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29349212301441362202127019 44023818452162043303190529)
  ·
    refine ⟨33017863839121532477392897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44023818452162043303190529 33017863839121532477392897)
    ·
      refine ⟨24763397879341149358044673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33017863839121532477392897 24763397879341149358044673)
      ·
        refine ⟨18572548409505862018533505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24763397879341149358044673 18572548409505862018533505)
        ·
          refine ⟨13929411307129396513900129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18572548409505862018533505 13929411307129396513900129)
          ·
            refine ⟨10447058480347047385425097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13929411307129396513900129 10447058480347047385425097)
            ·
              refine ⟨7835293860260285539068823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10447058480347047385425097 7835293860260285539068823)
              ·
                refine ⟨11752940790390428308603235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7835293860260285539068823 11752940790390428308603235)
                ·
                  refine ⟨17629411185585642462904853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11752940790390428308603235 17629411185585642462904853)
                  ·
                    refine ⟨826378649324326990448665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17629411185585642462904853 826378649324326990448665)
                    ·
                      refine ⟨619783986993245242836499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 826378649324326990448665 619783986993245242836499)
                      ·
                        rfl

theorem cell23_1207025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_1207025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207025 prefixEnd_1207025 := by exact prefixLift 1207025
  have htrace : WordTrace (prefixWord ++ tailWord_1207025) baseStart_1207025 baseEnd_1207025 := by
    simpa [prefixWord, tailWord_1207025, baseEnd_1207025] using wordTrace_append hprefix tailTrace_1207025
  have hstable : (prefixWord ++ tailWord_1207025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207025).length < 2 ^ (prefixWord ++ tailWord_1207025).sum := by decide
  have hdescent : baseEnd_1207025 < baseStart_1207025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207042 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1207042 : Nat := 118140960795 + 1207042 * 2 ^ 59
def prefixEnd_1207042 : Nat := 4983230072969 + 3 ^ 40 * 1207042 * 2
def baseEnd_1207042 : Nat := 619792716164371676323921

theorem tailTrace_1207042 : CollatzResearch.WordTrace tailWord_1207042 prefixEnd_1207042 619792716164371676323921 := by
  unfold tailWord_1207042
  simp only [CollatzResearch.WordTrace]
  refine ⟨11006109623275113801639845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29349625662066970137706253 11006109623275113801639845)
  ·
    refine ⟨2063645554364083837807471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11006109623275113801639845 2063645554364083837807471)
    ·
      refine ⟨3095468331546125756711207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2063645554364083837807471 3095468331546125756711207)
      ·
        refine ⟨4643202497319188635066811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3095468331546125756711207 4643202497319188635066811)
        ·
          refine ⟨6964803745978782952600217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4643202497319188635066811 6964803745978782952600217)
          ·
            refine ⟨5223602809484087214450163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6964803745978782952600217 5223602809484087214450163)
            ·
              refine ⟨7835404214226130821675245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5223602809484087214450163 7835404214226130821675245)
              ·
                refine ⟨2938276580334799058128217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7835404214226130821675245 2938276580334799058128217)
                ·
                  refine ⟨2203707435251099293596163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2938276580334799058128217 2203707435251099293596163)
                  ·
                    refine ⟨3305561152876648940394245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2203707435251099293596163 3305561152876648940394245)
                    ·
                      refine ⟨619792716164371676323921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3305561152876648940394245 619792716164371676323921)
                      ·
                        rfl

theorem cell23_1207042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1207042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207042 prefixEnd_1207042 := by exact prefixLift 1207042
  have htrace : WordTrace (prefixWord ++ tailWord_1207042) baseStart_1207042 baseEnd_1207042 := by
    simpa [prefixWord, tailWord_1207042, baseEnd_1207042] using wordTrace_append hprefix tailTrace_1207042
  have hstable : (prefixWord ++ tailWord_1207042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207042).length < 2 ^ (prefixWord ++ tailWord_1207042).sum := by decide
  have hdescent : baseEnd_1207042 < baseStart_1207042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207052 : List Nat := [2, 2, 1, 2, 2, 1, 1, 7, 1, 4]
def baseStart_1207052 : Nat := 118140960795 + 1207052 * 2 ^ 59
def prefixEnd_1207052 : Nat := 4983230072969 + 3 ^ 40 * 1207052 * 2
def baseEnd_1207052 : Nat := 206599283656972212399625

theorem tailTrace_1207052 : CollatzResearch.WordTrace tailWord_1207052 prefixEnd_1207052 206599283656972212399625 := by
  unfold tailWord_1207052
  simp only [CollatzResearch.WordTrace]
  refine ⟨22012401611532113457211705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29349868815376151276282273 22012401611532113457211705)
  ·
    refine ⟨16509301208649085092908779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22012401611532113457211705 16509301208649085092908779)
    ·
      refine ⟨24763951812973627639363169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16509301208649085092908779 24763951812973627639363169)
      ·
        refine ⟨18572963859730220729522377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24763951812973627639363169 18572963859730220729522377)
        ·
          refine ⟨13929722894797665547141783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18572963859730220729522377 13929722894797665547141783)
          ·
            refine ⟨20894584342196498320712675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13929722894797665547141783 20894584342196498320712675)
            ·
              refine ⟨31341876513294747481069013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20894584342196498320712675 31341876513294747481069013)
              ·
                refine ⟨734575230780345644087555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31341876513294747481069013 734575230780345644087555)
                ·
                  refine ⟨1101862846170518466131333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 734575230780345644087555 1101862846170518466131333)
                  ·
                    refine ⟨206599283656972212399625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1101862846170518466131333 206599283656972212399625)
                    ·
                      rfl

theorem cell23_1207052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_1207052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207052 prefixEnd_1207052 := by exact prefixLift 1207052
  have htrace : WordTrace (prefixWord ++ tailWord_1207052) baseStart_1207052 baseEnd_1207052 := by
    simpa [prefixWord, tailWord_1207052, baseEnd_1207052] using wordTrace_append hprefix tailTrace_1207052
  have hstable : (prefixWord ++ tailWord_1207052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207052).length < 2 ^ (prefixWord ++ tailWord_1207052).sum := by decide
  have hdescent : baseEnd_1207052 < baseStart_1207052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207095 : List Nat := [1, 1, 3, 1, 2, 1, 4, 4, 1, 5]
def baseStart_1207095 : Nat := 118140960795 + 1207095 * 2 ^ 59
def prefixEnd_1207095 : Nat := 4983230072969 + 3 ^ 40 * 1207095 * 2
def baseEnd_1207095 : Nat := 206606643546353322987059

theorem tailTrace_1207095 : CollatzResearch.WordTrace tailWord_1207095 prefixEnd_1207095 206606643546353322987059 := by
  unfold tailWord_1207095
  simp only [CollatzResearch.WordTrace]
  refine ⟨44026371561908445258238739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29350914374605630172159159 44026371561908445258238739)
  ·
    refine ⟨66039557342862667887358109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44026371561908445258238739 66039557342862667887358109)
    ·
      refine ⟨24764834003573500457759291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66039557342862667887358109 24764834003573500457759291)
      ·
        refine ⟨37147251005360250686638937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24764834003573500457759291 37147251005360250686638937)
        ·
          refine ⟨27860438254020188014979203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37147251005360250686638937 27860438254020188014979203)
          ·
            refine ⟨41790657381030282022468805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27860438254020188014979203 41790657381030282022468805)
            ·
              refine ⟨7835748258943177879212901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41790657381030282022468805 7835748258943177879212901)
              ·
                refine ⟨1469202798551845852352419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7835748258943177879212901 1469202798551845852352419)
                ·
                  refine ⟨2203804197827768778528629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469202798551845852352419 2203804197827768778528629)
                  ·
                    refine ⟨206606643546353322987059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2203804197827768778528629 206606643546353322987059)
                    ·
                      rfl

theorem cell23_1207095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_1207095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207095 prefixEnd_1207095 := by exact prefixLift 1207095
  have htrace : WordTrace (prefixWord ++ tailWord_1207095) baseStart_1207095 baseEnd_1207095 := by
    simpa [prefixWord, tailWord_1207095, baseEnd_1207095] using wordTrace_append hprefix tailTrace_1207095
  have hstable : (prefixWord ++ tailWord_1207095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207095).length < 2 ^ (prefixWord ++ tailWord_1207095).sum := by decide
  have hdescent : baseEnd_1207095 < baseStart_1207095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207115 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 3, 8, 2]
def baseStart_1207115 : Nat := 118140960795 + 1207115 * 2 ^ 59
def prefixEnd_1207115 : Nat := 4983230072969 + 3 ^ 40 * 1207115 * 2
def baseEnd_1207115 : Nat := 619830200252149890711085

theorem tailTrace_1207115 : CollatzResearch.WordTrace tailWord_1207115 prefixEnd_1207115 619830200252149890711085 := by
  unfold tailWord_1207115
  simp only [CollatzResearch.WordTrace]
  refine ⟨44027101021835988673966799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29351400681223992449311199 44027101021835988673966799)
  ·
    refine ⟨66040651532753983010950199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44027101021835988673966799 66040651532753983010950199)
    ·
      refine ⟨99060977299130974516425299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66040651532753983010950199 99060977299130974516425299)
      ·
        refine ⟨148591465948696461774637949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99060977299130974516425299 148591465948696461774637949)
        ·
          refine ⟨55721799730761173165489231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148591465948696461774637949 55721799730761173165489231)
          ·
            refine ⟨83582699596141759748233847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55721799730761173165489231 83582699596141759748233847)
            ·
              refine ⟨125374049394212639622350771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83582699596141759748233847 125374049394212639622350771)
              ·
                refine ⟨188061074091318959433526157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125374049394212639622350771 188061074091318959433526157)
                ·
                  refine ⟨70522902784244609787572309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188061074091318959433526157 70522902784244609787572309)
                  ·
                    refine ⟨826440267002866520948113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70522902784244609787572309 826440267002866520948113)
                    ·
                      refine ⟨619830200252149890711085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 826440267002866520948113 619830200252149890711085)
                      ·
                        rfl

theorem cell23_1207115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 8, 2].length) (baseStart_1207115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207115 prefixEnd_1207115 := by exact prefixLift 1207115
  have htrace : WordTrace (prefixWord ++ tailWord_1207115) baseStart_1207115 baseEnd_1207115 := by
    simpa [prefixWord, tailWord_1207115, baseEnd_1207115] using wordTrace_append hprefix tailTrace_1207115
  have hstable : (prefixWord ++ tailWord_1207115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207115).length < 2 ^ (prefixWord ++ tailWord_1207115).sum := by decide
  have hdescent : baseEnd_1207115 < baseStart_1207115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207135 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 5]
def baseStart_1207135 : Nat := 118140960795 + 1207135 * 2 ^ 59
def prefixEnd_1207135 : Nat := 4983230072969 + 3 ^ 40 * 1207135 * 2
def baseEnd_1207135 : Nat := 619840469865239812460993

theorem tailTrace_1207135 : CollatzResearch.WordTrace tailWord_1207135 prefixEnd_1207135 619840469865239812460993 := by
  unfold tailWord_1207135
  simp only [CollatzResearch.WordTrace]
  refine ⟨44027830481763532089694859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29351886987842354726463239 44027830481763532089694859)
  ·
    refine ⟨66041745722645298134542289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44027830481763532089694859 66041745722645298134542289)
    ·
      refine ⟨49531309291983973600906717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66041745722645298134542289 49531309291983973600906717)
      ·
        refine ⟨18574240984493990100340019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49531309291983973600906717 18574240984493990100340019)
        ·
          refine ⟨27861361476740985150510029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18574240984493990100340019 27861361476740985150510029)
          ·
            refine ⟨10448010553777869431441261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27861361476740985150510029 10448010553777869431441261)
            ·
              refine ⟨3918003957666701036790473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10448010553777869431441261 3918003957666701036790473)
              ·
                refine ⟨2938502968250025777592855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3918003957666701036790473 2938502968250025777592855)
                ·
                  refine ⟨4407754452375038666389283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938502968250025777592855 4407754452375038666389283)
                  ·
                    refine ⟨6611631678562557999583925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4407754452375038666389283 6611631678562557999583925)
                    ·
                      refine ⟨619840469865239812460993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6611631678562557999583925 619840469865239812460993)
                      ·
                        rfl

theorem cell23_1207135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_1207135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207135 prefixEnd_1207135 := by exact prefixLift 1207135
  have htrace : WordTrace (prefixWord ++ tailWord_1207135) baseStart_1207135 baseEnd_1207135 := by
    simpa [prefixWord, tailWord_1207135, baseEnd_1207135] using wordTrace_append hprefix tailTrace_1207135
  have hstable : (prefixWord ++ tailWord_1207135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207135).length < 2 ^ (prefixWord ++ tailWord_1207135).sum := by decide
  have hdescent : baseEnd_1207135 < baseStart_1207135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207152 : List Nat := [2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 3]
def baseStart_1207152 : Nat := 118140960795 + 1207152 * 2 ^ 59
def prefixEnd_1207152 : Nat := 4983230072969 + 3 ^ 40 * 1207152 * 2
def baseEnd_1207152 : Nat := 619849199036366245948415

theorem tailTrace_1207152 : CollatzResearch.WordTrace tailWord_1207152 prefixEnd_1207152 619849199036366245948415 := by
  unfold tailWord_1207152
  simp only [CollatzResearch.WordTrace]
  refine ⟨22014225261350971996531855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29352300348467962662042473 22014225261350971996531855)
  ·
    refine ⟨33021337892026457994797783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22014225261350971996531855 33021337892026457994797783)
    ·
      refine ⟨49532006838039686992196675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33021337892026457994797783 49532006838039686992196675)
      ·
        refine ⟨74298010257059530488295013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49532006838039686992196675 74298010257059530488295013)
        ·
          refine ⟨13930876923198661966555315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74298010257059530488295013 13930876923198661966555315)
          ·
            refine ⟨20896315384797992949832973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13930876923198661966555315 20896315384797992949832973)
            ·
              refine ⟨7836118269299247356187365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20896315384797992949832973 7836118269299247356187365)
              ·
                refine ⟨1469272175493608879285131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7836118269299247356187365 1469272175493608879285131)
                ·
                  refine ⟨2203908263240413318927697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469272175493608879285131 2203908263240413318927697)
                  ·
                    refine ⟨1652931197430309989195773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2203908263240413318927697 1652931197430309989195773)
                    ·
                      refine ⟨619849199036366245948415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1652931197430309989195773 619849199036366245948415)
                      ·
                        rfl

theorem cell23_1207152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 3].length) (baseStart_1207152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207152 prefixEnd_1207152 := by exact prefixLift 1207152
  have htrace : WordTrace (prefixWord ++ tailWord_1207152) baseStart_1207152 baseEnd_1207152 := by
    simpa [prefixWord, tailWord_1207152, baseEnd_1207152] using wordTrace_append hprefix tailTrace_1207152
  have hstable : (prefixWord ++ tailWord_1207152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207152).length < 2 ^ (prefixWord ++ tailWord_1207152).sum := by decide
  have hdescent : baseEnd_1207152 < baseStart_1207152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207155 : List Nat := [1, 1, 1, 2, 2, 1, 8, 7]
def baseStart_1207155 : Nat := 118140960795 + 1207155 * 2 ^ 59
def prefixEnd_1207155 : Nat := 4983230072969 + 3 ^ 40 * 1207155 * 2
def baseEnd_1207155 : Nat := 22957434795493693859663

theorem tailTrace_1207155 : CollatzResearch.WordTrace tailWord_1207155 prefixEnd_1207155 22957434795493693859663 := by
  unfold tailWord_1207155
  simp only [CollatzResearch.WordTrace]
  refine ⟨44028559941691075505422919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29352373294460717003615279 44028559941691075505422919)
  ·
    refine ⟨66042839912536613258134379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44028559941691075505422919 66042839912536613258134379)
    ·
      refine ⟨99064259868804919887201569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66042839912536613258134379 99064259868804919887201569)
      ·
        refine ⟨74298194901603689915401177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99064259868804919887201569 74298194901603689915401177)
        ·
          refine ⟨55723646176202767436550883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74298194901603689915401177 55723646176202767436550883)
          ·
            refine ⟨83585469264304151154826325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55723646176202767436550883 83585469264304151154826325)
            ·
              refine ⟨979517217941064271345621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 83585469264304151154826325 979517217941064271345621)
              ·
                refine ⟨22957434795493693859663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 979517217941064271345621 22957434795493693859663)
                ·
                  rfl

theorem cell23_1207155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 7].length) (baseStart_1207155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207155 prefixEnd_1207155 := by exact prefixLift 1207155
  have htrace : WordTrace (prefixWord ++ tailWord_1207155) baseStart_1207155 baseEnd_1207155 := by
    simpa [prefixWord, tailWord_1207155, baseEnd_1207155] using wordTrace_append hprefix tailTrace_1207155
  have hstable : (prefixWord ++ tailWord_1207155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207155).length < 2 ^ (prefixWord ++ tailWord_1207155).sum := by decide
  have hdescent : baseEnd_1207155 < baseStart_1207155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207226 : List Nat := [3, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2]
def baseStart_1207226 : Nat := 118140960795 + 1207226 * 2 ^ 59
def prefixEnd_1207226 : Nat := 4983230072969 + 3 ^ 40 * 1207226 * 2
def baseEnd_1207226 : Nat := 619887196604798956423075

theorem tailTrace_1207226 : CollatzResearch.WordTrace tailWord_1207226 prefixEnd_1207226 619887196604798956423075 := by
  unfold tailWord_1207226
  simp only [CollatzResearch.WordTrace]
  refine ⟨11007787381108463657814383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29354099682955903087505021 11007787381108463657814383)
  ·
    refine ⟨16511681071662695486721575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11007787381108463657814383 16511681071662695486721575)
    ·
      refine ⟨24767521607494043230082363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16511681071662695486721575 24767521607494043230082363)
      ·
        refine ⟨37151282411241064845123545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24767521607494043230082363 37151282411241064845123545)
        ·
          refine ⟨27863461808430798633842659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37151282411241064845123545 27863461808430798633842659)
          ·
            refine ⟨41795192712646197950763989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27863461808430798633842659 41795192712646197950763989)
            ·
              refine ⟨979574829202645264471031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 41795192712646197950763989 979574829202645264471031)
              ·
                refine ⟨1469362243803967896706547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979574829202645264471031 1469362243803967896706547)
                ·
                  refine ⟨2204043365705951845059821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469362243803967896706547 2204043365705951845059821)
                  ·
                    refine ⟨826516262139731941897433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2204043365705951845059821 826516262139731941897433)
                    ·
                      refine ⟨619887196604798956423075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 826516262139731941897433 619887196604798956423075)
                      ·
                        rfl

theorem cell23_1207226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2].length) (baseStart_1207226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207226 prefixEnd_1207226 := by exact prefixLift 1207226
  have htrace : WordTrace (prefixWord ++ tailWord_1207226) baseStart_1207226 baseEnd_1207226 := by
    simpa [prefixWord, tailWord_1207226, baseEnd_1207226] using wordTrace_append hprefix tailTrace_1207226
  have hstable : (prefixWord ++ tailWord_1207226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207226).length < 2 ^ (prefixWord ++ tailWord_1207226).sum := by decide
  have hdescent : baseEnd_1207226 < baseStart_1207226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207235 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 4]
def baseStart_1207235 : Nat := 118140960795 + 1207235 * 2 ^ 59
def prefixEnd_1207235 : Nat := 4983230072969 + 3 ^ 40 * 1207235 * 2
def baseEnd_1207235 : Nat := 619891817930689421210533

theorem tailTrace_1207235 : CollatzResearch.WordTrace tailWord_1207235 prefixEnd_1207235 619891817930689421210533 := by
  unfold tailWord_1207235
  simp only [CollatzResearch.WordTrace]
  refine ⟨44031477781401249168335159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29354318520934166112223439 44031477781401249168335159)
  ·
    refine ⟨66047216672101873752502739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44031477781401249168335159 66047216672101873752502739)
    ·
      refine ⟨99070825008152810628754109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66047216672101873752502739 99070825008152810628754109)
      ·
        refine ⟨37151559378057303985782791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99070825008152810628754109 37151559378057303985782791)
        ·
          refine ⟨55727339067085955978674187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37151559378057303985782791 55727339067085955978674187)
          ·
            refine ⟨83591008600628933968011281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55727339067085955978674187 83591008600628933968011281)
            ·
              refine ⟨62693256450471700476008461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83591008600628933968011281 62693256450471700476008461)
              ·
                refine ⟨23509971168926887678503173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62693256450471700476008461 23509971168926887678503173)
                ·
                  refine ⟨4408119594173791439719345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23509971168926887678503173 4408119594173791439719345)
                  ·
                    refine ⟨3306089695630343579789509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4408119594173791439719345 3306089695630343579789509)
                    ·
                      refine ⟨619891817930689421210533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3306089695630343579789509 619891817930689421210533)
                      ·
                        rfl

theorem cell23_1207235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_1207235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207235 prefixEnd_1207235 := by exact prefixLift 1207235
  have htrace : WordTrace (prefixWord ++ tailWord_1207235) baseStart_1207235 baseEnd_1207235 := by
    simpa [prefixWord, tailWord_1207235, baseEnd_1207235] using wordTrace_append hprefix tailTrace_1207235
  have hstable : (prefixWord ++ tailWord_1207235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207235).length < 2 ^ (prefixWord ++ tailWord_1207235).sum := by decide
  have hdescent : baseEnd_1207235 < baseStart_1207235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207239 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 4, 2, 2]
def baseStart_1207239 : Nat := 118140960795 + 1207239 * 2 ^ 59
def prefixEnd_1207239 : Nat := 4983230072969 + 3 ^ 40 * 1207239 * 2
def baseEnd_1207239 : Nat := 619893871853307405560515

theorem tailTrace_1207239 : CollatzResearch.WordTrace tailWord_1207239 prefixEnd_1207239 619893871853307405560515 := by
  unfold tailWord_1207239
  simp only [CollatzResearch.WordTrace]
  refine ⟨44031623673386757851480771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29354415782257838567653847 44031623673386757851480771)
  ·
    refine ⟨66047435510080136777221157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44031623673386757851480771 66047435510080136777221157)
    ·
      refine ⟨12383894158140025645728967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66047435510080136777221157 12383894158140025645728967)
      ·
        refine ⟨18575841237210038468593451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12383894158140025645728967 18575841237210038468593451)
        ·
          refine ⟨27863761855815057702890177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18575841237210038468593451 27863761855815057702890177)
          ·
            refine ⟨20897821391861293277167633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27863761855815057702890177 20897821391861293277167633)
            ·
              refine ⟨15673366043895969957875725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20897821391861293277167633 15673366043895969957875725)
              ·
                refine ⟨5877512266460988734203397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15673366043895969957875725 5877512266460988734203397)
                ·
                  refine ⟨1102033549961435387663137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5877512266460988734203397 1102033549961435387663137)
                  ·
                    refine ⟨826525162471076540747353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1102033549961435387663137 826525162471076540747353)
                    ·
                      refine ⟨619893871853307405560515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 826525162471076540747353 619893871853307405560515)
                      ·
                        rfl

theorem cell23_1207239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_1207239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207239 prefixEnd_1207239 := by exact prefixLift 1207239
  have htrace : WordTrace (prefixWord ++ tailWord_1207239) baseStart_1207239 baseEnd_1207239 := by
    simpa [prefixWord, tailWord_1207239, baseEnd_1207239] using wordTrace_append hprefix tailTrace_1207239
  have hstable : (prefixWord ++ tailWord_1207239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207239).length < 2 ^ (prefixWord ++ tailWord_1207239).sum := by decide
  have hdescent : baseEnd_1207239 < baseStart_1207239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207252 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1207252 : Nat := 118140960795 + 1207252 * 2 ^ 59
def prefixEnd_1207252 : Nat := 4983230072969 + 3 ^ 40 * 1207252 * 2
def baseEnd_1207252 : Nat := 619900547101815854697955

theorem tailTrace_1207252 : CollatzResearch.WordTrace tailWord_1207252 prefixEnd_1207252 619900547101815854697955 := by
  unfold tailWord_1207252
  simp only [CollatzResearch.WordTrace]
  refine ⟨22016048911169830535852005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29354731881559774047802673 22016048911169830535852005)
  ·
    refine ⟨4128009170844343225472251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22016048911169830535852005 4128009170844343225472251)
    ·
      refine ⟨6192013756266514838208377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4128009170844343225472251 6192013756266514838208377)
      ·
        refine ⟨4644010317199886128656283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6192013756266514838208377 4644010317199886128656283)
        ·
          refine ⟨6966015475799829192984425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4644010317199886128656283 6966015475799829192984425)
          ·
            refine ⟨5224511606849871894738319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6966015475799829192984425 5224511606849871894738319)
            ·
              refine ⟨7836767410274807842107479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5224511606849871894738319 7836767410274807842107479)
              ·
                refine ⟨11755151115412211763161219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7836767410274807842107479 11755151115412211763161219)
                ·
                  refine ⟨17632726673118317644741829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11755151115412211763161219 17632726673118317644741829)
                  ·
                    refine ⟨3306136251209684558389093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17632726673118317644741829 3306136251209684558389093)
                    ·
                      refine ⟨619900547101815854697955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3306136251209684558389093 619900547101815854697955)
                      ·
                        rfl

theorem cell23_1207252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1207252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207252 prefixEnd_1207252 := by exact prefixLift 1207252
  have htrace : WordTrace (prefixWord ++ tailWord_1207252) baseStart_1207252 baseEnd_1207252 := by
    simpa [prefixWord, tailWord_1207252, baseEnd_1207252] using wordTrace_append hprefix tailTrace_1207252
  have hstable : (prefixWord ++ tailWord_1207252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207252).length < 2 ^ (prefixWord ++ tailWord_1207252).sum := by decide
  have hdescent : baseEnd_1207252 < baseStart_1207252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207256 : List Nat := [2, 1, 2, 2, 2, 3, 2, 3, 2, 2, 2]
def baseStart_1207256 : Nat := 118140960795 + 1207256 * 2 ^ 59
def prefixEnd_1207256 : Nat := 4983230072969 + 3 ^ 40 * 1207256 * 2
def baseEnd_1207256 : Nat := 619902601024433839047937

theorem tailTrace_1207256 : CollatzResearch.WordTrace tailWord_1207256 prefixEnd_1207256 619902601024433839047937 := by
  unfold tailWord_1207256
  simp only [CollatzResearch.WordTrace]
  refine ⟨22016121857162584877424811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29354829142883446503233081 22016121857162584877424811)
  ·
    refine ⟨33024182785743877316137217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22016121857162584877424811 33024182785743877316137217)
    ·
      refine ⟨24768137089307907987102913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33024182785743877316137217 24768137089307907987102913)
      ·
        refine ⟨18576102816980930990327185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24768137089307907987102913 18576102816980930990327185)
        ·
          refine ⟨13932077112735698242745389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18576102816980930990327185 13932077112735698242745389)
          ·
            refine ⟨5224528917275886841029521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13932077112735698242745389 5224528917275886841029521)
            ·
              refine ⟨3918396687956915130772141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5224528917275886841029521 3918396687956915130772141)
              ·
                refine ⟨1469398757983843174039553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3918396687956915130772141 1469398757983843174039553)
                ·
                  refine ⟨1102049068487882380529665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1469398757983843174039553 1102049068487882380529665)
                  ·
                    refine ⟨826536801365911785397249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1102049068487882380529665 826536801365911785397249)
                    ·
                      refine ⟨619902601024433839047937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 826536801365911785397249 619902601024433839047937)
                      ·
                        rfl

theorem cell23_1207256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_1207256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207256 prefixEnd_1207256 := by exact prefixLift 1207256
  have htrace : WordTrace (prefixWord ++ tailWord_1207256) baseStart_1207256 baseEnd_1207256 := by
    simpa [prefixWord, tailWord_1207256, baseEnd_1207256] using wordTrace_append hprefix tailTrace_1207256
  have hstable : (prefixWord ++ tailWord_1207256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207256).length < 2 ^ (prefixWord ++ tailWord_1207256).sum := by decide
  have hdescent : baseEnd_1207256 < baseStart_1207256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207279 : List Nat := [1, 1, 2, 1, 4, 4, 2, 3, 5]
def baseStart_1207279 : Nat := 118140960795 + 1207279 * 2 ^ 59
def prefixEnd_1207279 : Nat := 4983230072969 + 3 ^ 40 * 1207279 * 2
def baseEnd_1207279 : Nat := 68879379008831916562259

theorem tailTrace_1207279 : CollatzResearch.WordTrace tailWord_1207279 prefixEnd_1207279 68879379008831916562259 := by
  unfold tailWord_1207279
  simp only [CollatzResearch.WordTrace]
  refine ⟨44033082593241844682936891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29355388395494563121957927 44033082593241844682936891)
  ·
    refine ⟨66049623889862767024405337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44033082593241844682936891 66049623889862767024405337)
    ·
      refine ⟨49537217917397075268304003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66049623889862767024405337 49537217917397075268304003)
      ·
        refine ⟨74305826876095612902456005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49537217917397075268304003 74305826876095612902456005)
        ·
          refine ⟨13932342539267927419210501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74305826876095612902456005 13932342539267927419210501)
          ·
            refine ⟨2612314226112736391101969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13932342539267927419210501 2612314226112736391101969)
            ·
              refine ⟨1959235669584552293326477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2612314226112736391101969 1959235669584552293326477)
              ·
                refine ⟨734713376094207109997429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1959235669584552293326477 734713376094207109997429)
                ·
                  refine ⟨68879379008831916562259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 734713376094207109997429 68879379008831916562259)
                  ·
                    rfl

theorem cell23_1207279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 5].length) (baseStart_1207279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207279 prefixEnd_1207279 := by exact prefixLift 1207279
  have htrace : WordTrace (prefixWord ++ tailWord_1207279) baseStart_1207279 baseEnd_1207279 := by
    simpa [prefixWord, tailWord_1207279, baseEnd_1207279] using wordTrace_append hprefix tailTrace_1207279
  have hstable : (prefixWord ++ tailWord_1207279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207279).length < 2 ^ (prefixWord ++ tailWord_1207279).sum := by decide
  have hdescent : baseEnd_1207279 < baseStart_1207279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207284 : List Nat := [2, 6, 2, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1207284 : Nat := 118140960795 + 1207284 * 2 ^ 59
def prefixEnd_1207284 : Nat := 4983230072969 + 3 ^ 40 * 1207284 * 2
def baseEnd_1207284 : Nat := 619916978482759729497809

theorem tailTrace_1207284 : CollatzResearch.WordTrace tailWord_1207284 prefixEnd_1207284 619916978482759729497809 := by
  unfold tailWord_1207284
  simp only [CollatzResearch.WordTrace]
  refine ⟨22016632479111865268434453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29355509972149153691245937 22016632479111865268434453)
  ·
    refine ⟨1032029647458368684457865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22016632479111865268434453 1032029647458368684457865)
    ·
      refine ⟨774022235593776513343399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1032029647458368684457865 774022235593776513343399)
      ·
        refine ⟨1161033353390664770015099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774022235593776513343399 1161033353390664770015099)
        ·
          refine ⟨1741550030085997155022649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1161033353390664770015099 1741550030085997155022649)
          ·
            refine ⟨1306162522564497866266987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1741550030085997155022649 1306162522564497866266987)
            ·
              refine ⟨1959243783846746799400481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1306162522564497866266987 1959243783846746799400481)
              ·
                refine ⟨1469432837885060099550361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1959243783846746799400481 1469432837885060099550361)
                ·
                  refine ⟨1102074628413795074662771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1469432837885060099550361 1102074628413795074662771)
                  ·
                    refine ⟨1653111942620692611994157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1102074628413795074662771 1653111942620692611994157)
                    ·
                      refine ⟨619916978482759729497809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1653111942620692611994157 619916978482759729497809)
                      ·
                        rfl

theorem cell23_1207284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1207284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207284 prefixEnd_1207284 := by exact prefixLift 1207284
  have htrace : WordTrace (prefixWord ++ tailWord_1207284) baseStart_1207284 baseEnd_1207284 := by
    simpa [prefixWord, tailWord_1207284, baseEnd_1207284] using wordTrace_append hprefix tailTrace_1207284
  have hstable : (prefixWord ++ tailWord_1207284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207284).length < 2 ^ (prefixWord ++ tailWord_1207284).sum := by decide
  have hdescent : baseEnd_1207284 < baseStart_1207284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207352 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 8]
def baseStart_1207352 : Nat := 118140960795 + 1207352 * 2 ^ 59
def prefixEnd_1207352 : Nat := 4983230072969 + 3 ^ 40 * 1207352 * 2
def baseEnd_1207352 : Nat := 68883543907473940383055

theorem tailTrace_1207352 : CollatzResearch.WordTrace tailWord_1207352 prefixEnd_1207352 68883543907473940383055 := by
  unfold tailWord_1207352
  simp only [CollatzResearch.WordTrace]
  refine ⟨22017872560988689075172155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29357163414651585433562873 22017872560988689075172155)
  ·
    refine ⟨33026808841483033612758233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22017872560988689075172155 33026808841483033612758233)
    ·
      refine ⟨24770106631112275209568675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33026808841483033612758233 24770106631112275209568675)
      ·
        refine ⟨37155159946668412814353013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24770106631112275209568675 37155159946668412814353013)
        ·
          refine ⟨3483296245000163701345595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37155159946668412814353013 3483296245000163701345595)
          ·
            refine ⟨5224944367500245552018393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3483296245000163701345595 5224944367500245552018393)
            ·
              refine ⟨3918708275625184164013795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5224944367500245552018393 3918708275625184164013795)
              ·
                refine ⟨5878062413437776246020693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3918708275625184164013795 5878062413437776246020693)
                ·
                  refine ⟨68883543907473940383055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5878062413437776246020693 68883543907473940383055)
                  ·
                    rfl

theorem cell23_1207352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 8].length) (baseStart_1207352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207352 prefixEnd_1207352 := by exact prefixLift 1207352
  have htrace : WordTrace (prefixWord ++ tailWord_1207352) baseStart_1207352 baseEnd_1207352 := by
    simpa [prefixWord, tailWord_1207352, baseEnd_1207352] using wordTrace_append hprefix tailTrace_1207352
  have hstable : (prefixWord ++ tailWord_1207352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207352).length < 2 ^ (prefixWord ++ tailWord_1207352).sum := by decide
  have hdescent : baseEnd_1207352 < baseStart_1207352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207356 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 3, 4]
def baseStart_1207356 : Nat := 118140960795 + 1207356 * 2 ^ 59
def prefixEnd_1207356 : Nat := 4983230072969 + 3 ^ 40 * 1207356 * 2
def baseEnd_1207356 : Nat := 206651316363294482599159

theorem tailTrace_1207356 : CollatzResearch.WordTrace tailWord_1207356 prefixEnd_1207356 206651316363294482599159 := by
  unfold tailWord_1207356
  simp only [CollatzResearch.WordTrace]
  refine ⟨22017945506981443416744961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29357260675975257888993281 22017945506981443416744961)
  ·
    refine ⟨16513459130236082562558721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22017945506981443416744961 16513459130236082562558721)
    ·
      refine ⟨12385094347677061921919041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16513459130236082562558721 12385094347677061921919041)
      ·
        refine ⟨9288820760757796441439281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12385094347677061921919041 9288820760757796441439281)
        ·
          refine ⟨6966615570568347331079461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9288820760757796441439281 6966615570568347331079461)
          ·
            refine ⟨1306240419481565124577399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6966615570568347331079461 1306240419481565124577399)
            ·
              refine ⟨1959360629222347686866099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1306240419481565124577399 1959360629222347686866099)
              ·
                refine ⟨2939040943833521530299149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1959360629222347686866099 2939040943833521530299149)
                ·
                  refine ⟨1102140353937570573862181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2939040943833521530299149 1102140353937570573862181)
                  ·
                    refine ⟨206651316363294482599159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1102140353937570573862181 206651316363294482599159)
                    ·
                      rfl

theorem cell23_1207356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_1207356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207356 prefixEnd_1207356 := by exact prefixLift 1207356
  have htrace : WordTrace (prefixWord ++ tailWord_1207356) baseStart_1207356 baseEnd_1207356 := by
    simpa [prefixWord, tailWord_1207356, baseEnd_1207356] using wordTrace_append hprefix tailTrace_1207356
  have hstable : (prefixWord ++ tailWord_1207356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207356).length < 2 ^ (prefixWord ++ tailWord_1207356).sum := by decide
  have hdescent : baseEnd_1207356 < baseStart_1207356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207456 : List Nat := [2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 3]
def baseStart_1207456 : Nat := 118140960795 + 1207456 * 2 ^ 59
def prefixEnd_1207456 : Nat := 4983230072969 + 3 ^ 40 * 1207456 * 2
def baseEnd_1207456 : Nat := 620005297155333056547017

theorem tailTrace_1207456 : CollatzResearch.WordTrace tailWord_1207456 prefixEnd_1207456 620005297155333056547017 := by
  unfold tailWord_1207456
  simp only [CollatzResearch.WordTrace]
  refine ⟨22019769156800301956065111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29359692209067069274753481 22019769156800301956065111)
  ·
    refine ⟨33029653735200452934097667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22019769156800301956065111 33029653735200452934097667)
    ·
      refine ⟨49544480602800679401146501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33029653735200452934097667 49544480602800679401146501)
      ·
        refine ⟨9289590113025127387714969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49544480602800679401146501 9289590113025127387714969)
        ·
          refine ⟨6967192584768845540786227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9289590113025127387714969 6967192584768845540786227)
          ·
            refine ⟨10450788877153268311179341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6967192584768845540786227 10450788877153268311179341)
            ·
              refine ⟨3919045828932475616692253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10450788877153268311179341 3919045828932475616692253)
              ·
                refine ⟨1469642185849678356259595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3919045828932475616692253 1469642185849678356259595)
                ·
                  refine ⟨2204463278774517534389393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469642185849678356259595 2204463278774517534389393)
                  ·
                    refine ⟨1653347459080888150792045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2204463278774517534389393 1653347459080888150792045)
                    ·
                      refine ⟨620005297155333056547017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1653347459080888150792045 620005297155333056547017)
                      ·
                        rfl

theorem cell23_1207456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_1207456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207456 prefixEnd_1207456 := by exact prefixLift 1207456
  have htrace : WordTrace (prefixWord ++ tailWord_1207456) baseStart_1207456 baseEnd_1207456 := by
    simpa [prefixWord, tailWord_1207456, baseEnd_1207456] using wordTrace_append hprefix tailTrace_1207456
  have hstable : (prefixWord ++ tailWord_1207456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207456).length < 2 ^ (prefixWord ++ tailWord_1207456).sum := by decide
  have hdescent : baseEnd_1207456 < baseStart_1207456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207463 : List Nat := [1, 1, 6, 2, 1, 1, 3, 2, 2, 4]
def baseStart_1207463 : Nat := 118140960795 + 1207463 * 2 ^ 59
def prefixEnd_1207463 : Nat := 4983230072969 + 3 ^ 40 * 1207463 * 2
def baseEnd_1207463 : Nat := 206669630506638176386495

theorem tailTrace_1207463 : CollatzResearch.WordTrace tailWord_1207463 prefixEnd_1207463 206669630506638176386495 := by
  unfold tailWord_1207463
  simp only [CollatzResearch.WordTrace]
  refine ⟨44039793624575244107635043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29359862416383496071756695 44039793624575244107635043)
  ·
    refine ⟨66059690436862866161452565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44039793624575244107635043 66059690436862866161452565)
    ·
      refine ⟨3096547989227946851318089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66059690436862866161452565 3096547989227946851318089)
      ·
        refine ⟨2322410991920960138488567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3096547989227946851318089 2322410991920960138488567)
        ·
          refine ⟨3483616487881440207732851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2322410991920960138488567 3483616487881440207732851)
          ·
            refine ⟨5225424731822160311599277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3483616487881440207732851 5225424731822160311599277)
            ·
              refine ⟨1959534274433310116849729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5225424731822160311599277 1959534274433310116849729)
              ·
                refine ⟨1469650705824982587637297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1959534274433310116849729 1469650705824982587637297)
                ·
                  refine ⟨1102238029368736940727973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1469650705824982587637297 1102238029368736940727973)
                  ·
                    refine ⟨206669630506638176386495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1102238029368736940727973 206669630506638176386495)
                    ·
                      rfl

theorem cell23_1207463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_1207463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207463 prefixEnd_1207463 := by exact prefixLift 1207463
  have htrace : WordTrace (prefixWord ++ tailWord_1207463) baseStart_1207463 baseEnd_1207463 := by
    simpa [prefixWord, tailWord_1207463, baseEnd_1207463] using wordTrace_append hprefix tailTrace_1207463
  have hstable : (prefixWord ++ tailWord_1207463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207463).length < 2 ^ (prefixWord ++ tailWord_1207463).sum := by decide
  have hdescent : baseEnd_1207463 < baseStart_1207463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207496 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 3, 3, 2]
def baseStart_1207496 : Nat := 118140960795 + 1207496 * 2 ^ 59
def prefixEnd_1207496 : Nat := 4983230072969 + 3 ^ 40 * 1207496 * 2
def baseEnd_1207496 : Nat := 620025836381512900046833

theorem tailTrace_1207496 : CollatzResearch.WordTrace tailWord_1207496 prefixEnd_1207496 620025836381512900046833 := by
  unfold tailWord_1207496
  simp only [CollatzResearch.WordTrace]
  refine ⟨22020498616727845371793171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29360664822303793829057561 22020498616727845371793171)
  ·
    refine ⟨33030747925091768057689757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22020498616727845371793171 33030747925091768057689757)
    ·
      refine ⟨12386530471909413021633659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33030747925091768057689757 12386530471909413021633659)
      ·
        refine ⟨18579795707864119532450489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12386530471909413021633659 18579795707864119532450489)
        ·
          refine ⟨13934846780898089649337867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18579795707864119532450489 13934846780898089649337867)
          ·
            refine ⟨20902270171347134474006801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13934846780898089649337867 20902270171347134474006801)
            ·
              refine ⟨15676702628510350855505101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20902270171347134474006801 15676702628510350855505101)
              ·
                refine ⟨5878763485691381570814413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15676702628510350855505101 5878763485691381570814413)
                ·
                  refine ⟨2204536307134268089055405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5878763485691381570814413 2204536307134268089055405)
                  ·
                    refine ⟨826701115175350533395777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2204536307134268089055405 826701115175350533395777)
                    ·
                      refine ⟨620025836381512900046833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 826701115175350533395777 620025836381512900046833)
                      ·
                        rfl

theorem cell23_1207496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_1207496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207496 prefixEnd_1207496 := by exact prefixLift 1207496
  have htrace : WordTrace (prefixWord ++ tailWord_1207496) baseStart_1207496 baseEnd_1207496 := by
    simpa [prefixWord, tailWord_1207496, baseEnd_1207496] using wordTrace_append hprefix tailTrace_1207496
  have hstable : (prefixWord ++ tailWord_1207496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207496).length < 2 ^ (prefixWord ++ tailWord_1207496).sum := by decide
  have hdescent : baseEnd_1207496 < baseStart_1207496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207543 : List Nat := [1, 1, 3, 1, 1, 1, 2, 7, 2, 2, 2]
def baseStart_1207543 : Nat := 118140960795 + 1207543 * 2 ^ 59
def prefixEnd_1207543 : Nat := 4983230072969 + 3 ^ 40 * 1207543 * 2
def baseEnd_1207543 : Nat := 620049969972274216159117

theorem tailTrace_1207543 : CollatzResearch.WordTrace tailWord_1207543 prefixEnd_1207543 620049969972274216159117 := by
  unfold tailWord_1207543
  simp only [CollatzResearch.WordTrace]
  refine ⟨44042711464285417770547283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29361807642856945180364855 44042711464285417770547283)
  ·
    refine ⟨66064067196428126655820925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44042711464285417770547283 66064067196428126655820925)
    ·
      refine ⟨24774025198660547495932847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66064067196428126655820925 24774025198660547495932847)
      ·
        refine ⟨37161037797990821243899271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24774025198660547495932847 37161037797990821243899271)
        ·
          refine ⟨55741556696986231865848907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37161037797990821243899271 55741556696986231865848907)
          ·
            refine ⟨83612335045479347798773361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55741556696986231865848907 83612335045479347798773361)
            ·
              refine ⟨62709251284109510849080021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83612335045479347798773361 62709251284109510849080021)
              ·
                refine ⟨1469748076971316660525313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 62709251284109510849080021 1469748076971316660525313)
                ·
                  refine ⟨1102311057728487495393985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1469748076971316660525313 1102311057728487495393985)
                  ·
                    refine ⟨826733293296365621545489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1102311057728487495393985 826733293296365621545489)
                    ·
                      refine ⟨620049969972274216159117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 826733293296365621545489 620049969972274216159117)
                      ·
                        rfl

theorem cell23_1207543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 2, 2].length) (baseStart_1207543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207543 prefixEnd_1207543 := by exact prefixLift 1207543
  have htrace : WordTrace (prefixWord ++ tailWord_1207543) baseStart_1207543 baseEnd_1207543 := by
    simpa [prefixWord, tailWord_1207543, baseEnd_1207543] using wordTrace_append hprefix tailTrace_1207543
  have hstable : (prefixWord ++ tailWord_1207543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207543).length < 2 ^ (prefixWord ++ tailWord_1207543).sum := by decide
  have hdescent : baseEnd_1207543 < baseStart_1207543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207583 : List Nat := [1, 1, 2, 4, 4, 1, 1, 4, 5]
def baseStart_1207583 : Nat := 118140960795 + 1207583 * 2 ^ 59
def prefixEnd_1207583 : Nat := 4983230072969 + 3 ^ 40 * 1207583 * 2
def baseEnd_1207583 : Nat := 68896723244272673295437

theorem tailTrace_1207583 : CollatzResearch.WordTrace tailWord_1207583 prefixEnd_1207583 68896723244272673295437 := by
  unfold tailWord_1207583
  simp only [CollatzResearch.WordTrace]
  refine ⟨44044170384140504602003403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29362780256093669734668935 44044170384140504602003403)
  ·
    refine ⟨66066255576210756903005105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44044170384140504602003403 66066255576210756903005105)
    ·
      refine ⟨49549691682158067677253829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66066255576210756903005105 49549691682158067677253829)
      ·
        refine ⟨9290567190404637689485093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49549691682158067677253829 9290567190404637689485093)
        ·
          refine ⟨1741981348200869566778455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9290567190404637689485093 1741981348200869566778455)
          ·
            refine ⟨2612972022301304350167683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741981348200869566778455 2612972022301304350167683)
            ·
              refine ⟨3919458033451956525251525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2612972022301304350167683 3919458033451956525251525)
              ·
                refine ⟨734898381272241848484661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3919458033451956525251525 734898381272241848484661)
                ·
                  refine ⟨68896723244272673295437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 734898381272241848484661 68896723244272673295437)
                  ·
                    rfl

theorem cell23_1207583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 5].length) (baseStart_1207583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207583 prefixEnd_1207583 := by exact prefixLift 1207583
  have htrace : WordTrace (prefixWord ++ tailWord_1207583) baseStart_1207583 baseEnd_1207583 := by
    simpa [prefixWord, tailWord_1207583, baseEnd_1207583] using wordTrace_append hprefix tailTrace_1207583
  have hstable : (prefixWord ++ tailWord_1207583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207583).length < 2 ^ (prefixWord ++ tailWord_1207583).sum := by decide
  have hdescent : baseEnd_1207583 < baseStart_1207583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207599 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 4]
def baseStart_1207599 : Nat := 118140960795 + 1207599 * 2 ^ 59
def prefixEnd_1207599 : Nat := 4983230072969 + 3 ^ 40 * 1207599 * 2
def baseEnd_1207599 : Nat := 620078724888925997058859

theorem tailTrace_1207599 : CollatzResearch.WordTrace tailWord_1207599 prefixEnd_1207599 620078724888925997058859 := by
  unfold tailWord_1207599
  simp only [CollatzResearch.WordTrace]
  refine ⟨44044753952082539334585851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29363169301388359556390567 44044753952082539334585851)
  ·
    refine ⟨66067130928123809001878777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44044753952082539334585851 66067130928123809001878777)
    ·
      refine ⟨49550348196092856751409083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66067130928123809001878777 49550348196092856751409083)
      ·
        refine ⟨74325522294139285127113625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49550348196092856751409083 74325522294139285127113625)
        ·
          refine ⟨55744141720604463845335219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74325522294139285127113625 55744141720604463845335219)
          ·
            refine ⟨83616212580906695768002829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55744141720604463845335219 83616212580906695768002829)
            ·
              refine ⟨31356079717840010913001061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83616212580906695768002829 31356079717840010913001061)
              ·
                refine ⟨5879264947095002046187699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31356079717840010913001061 5879264947095002046187699)
                ·
                  refine ⟨8818897420642503069281549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5879264947095002046187699 8818897420642503069281549)
                  ·
                    refine ⟨3307086532740938650980581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8818897420642503069281549 3307086532740938650980581)
                    ·
                      refine ⟨620078724888925997058859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3307086532740938650980581 620078724888925997058859)
                      ·
                        rfl

theorem cell23_1207599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_1207599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207599 prefixEnd_1207599 := by exact prefixLift 1207599
  have htrace : WordTrace (prefixWord ++ tailWord_1207599) baseStart_1207599 baseEnd_1207599 := by
    simpa [prefixWord, tailWord_1207599, baseEnd_1207599] using wordTrace_append hprefix tailTrace_1207599
  have hstable : (prefixWord ++ tailWord_1207599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207599).length < 2 ^ (prefixWord ++ tailWord_1207599).sum := by decide
  have hdescent : baseEnd_1207599 < baseStart_1207599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207613 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_1207613 : Nat := 118140960795 + 1207613 * 2 ^ 59
def prefixEnd_1207613 : Nat := 4983230072969 + 3 ^ 40 * 1207613 * 2
def baseEnd_1207613 : Nat := 206695304539362980761265

theorem tailTrace_1207613 : CollatzResearch.WordTrace tailWord_1207613 prefixEnd_1207613 206695304539362980761265 := by
  unfold tailWord_1207613
  simp only [CollatzResearch.WordTrace]
  refine ⟨44045264574031819725595493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29363509716021213150396995 44045264574031819725595493)
  ·
    refine ⟨8258487107630966198549155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44045264574031819725595493 8258487107630966198549155)
    ·
      refine ⟨12387730661446449297823733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8258487107630966198549155 12387730661446449297823733)
      ·
        refine ⟨1161349749510604621670975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12387730661446449297823733 1161349749510604621670975)
        ·
          refine ⟨1742024624265906932506463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1161349749510604621670975 1742024624265906932506463)
          ·
            refine ⟨2613036936398860398759695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1742024624265906932506463 2613036936398860398759695)
            ·
              refine ⟨3919555404598290598139543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613036936398860398759695 3919555404598290598139543)
              ·
                refine ⟨5879333106897435897209315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3919555404598290598139543 5879333106897435897209315)
                ·
                  refine ⟨8818999660346153845813973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5879333106897435897209315 8818999660346153845813973)
                  ·
                    refine ⟨206695304539362980761265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8818999660346153845813973 206695304539362980761265)
                    ·
                      rfl

theorem cell23_1207613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_1207613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207613 prefixEnd_1207613 := by exact prefixLift 1207613
  have htrace : WordTrace (prefixWord ++ tailWord_1207613) baseStart_1207613 baseEnd_1207613 := by
    simpa [prefixWord, tailWord_1207613, baseEnd_1207613] using wordTrace_append hprefix tailTrace_1207613
  have hstable : (prefixWord ++ tailWord_1207613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207613).length < 2 ^ (prefixWord ++ tailWord_1207613).sum := by decide
  have hdescent : baseEnd_1207613 < baseStart_1207613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207616 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 1, 6, 2]
def baseStart_1207616 : Nat := 118140960795 + 1207616 * 2 ^ 59
def prefixEnd_1207616 : Nat := 4983230072969 + 3 ^ 40 * 1207616 * 2
def baseEnd_1207616 : Nat := 620087454060052430546281

theorem tailTrace_1207616 : CollatzResearch.WordTrace tailWord_1207616 prefixEnd_1207616 620087454060052430546281 := by
  unfold tailWord_1207616
  simp only [CollatzResearch.WordTrace]
  refine ⟨22022686996510475618977351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29363582662013967491969801 22022686996510475618977351)
  ·
    refine ⟨33034030494765713428466027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22022686996510475618977351 33034030494765713428466027)
    ·
      refine ⟨49551045742148570142699041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33034030494765713428466027 49551045742148570142699041)
      ·
        refine ⟨37163284306611427607024281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49551045742148570142699041 37163284306611427607024281)
        ·
          refine ⟨27872463229958570705268211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37163284306611427607024281 27872463229958570705268211)
          ·
            refine ⟨41808694844937856057902317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27872463229958570705268211 41808694844937856057902317)
            ·
              refine ⟨15678260566851696021713369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41808694844937856057902317 15678260566851696021713369)
              ·
                refine ⟨11758695425138772016285027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15678260566851696021713369 11758695425138772016285027)
                ·
                  refine ⟨17638043137708158024427541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11758695425138772016285027 17638043137708158024427541)
                  ·
                    refine ⟨826783272080069907395041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17638043137708158024427541 826783272080069907395041)
                    ·
                      refine ⟨620087454060052430546281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 826783272080069907395041 620087454060052430546281)
                      ·
                        rfl

theorem cell23_1207616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 1, 6, 2].length) (baseStart_1207616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207616 prefixEnd_1207616 := by exact prefixLift 1207616
  have htrace : WordTrace (prefixWord ++ tailWord_1207616) baseStart_1207616 baseEnd_1207616 := by
    simpa [prefixWord, tailWord_1207616, baseEnd_1207616] using wordTrace_append hprefix tailTrace_1207616
  have hstable : (prefixWord ++ tailWord_1207616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207616).length < 2 ^ (prefixWord ++ tailWord_1207616).sum := by decide
  have hdescent : baseEnd_1207616 < baseStart_1207616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207666 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_1207666 : Nat := 118140960795 + 1207666 * 2 ^ 59
def prefixEnd_1207666 : Nat := 4983230072969 + 3 ^ 40 * 1207666 * 2
def baseEnd_1207666 : Nat := 620113128092777234921051

theorem tailTrace_1207666 : CollatzResearch.WordTrace tailWord_1207666 prefixEnd_1207666 620113128092777234921051 := by
  unfold tailWord_1207666
  simp only [CollatzResearch.WordTrace]
  refine ⟨11011799410709952444318713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29364798428559873184849901 11011799410709952444318713)
  ·
    refine ⟨8258849558032464333239035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11011799410709952444318713 8258849558032464333239035)
    ·
      refine ⟨12388274337048696499858553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8258849558032464333239035 12388274337048696499858553)
      ·
        refine ⟨9291205752786522374893915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12388274337048696499858553 9291205752786522374893915)
        ·
          refine ⟨13936808629179783562340873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9291205752786522374893915 13936808629179783562340873)
          ·
            refine ⟨10452606471884837671755655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13936808629179783562340873 10452606471884837671755655)
            ·
              refine ⟨15678909707827256507633483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10452606471884837671755655 15678909707827256507633483)
              ·
                refine ⟨23518364561740884761450225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15678909707827256507633483 23518364561740884761450225)
                ·
                  refine ⟨17638773421305663571087669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23518364561740884761450225 17638773421305663571087669)
                  ·
                    refine ⟨1653635008247405959789469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17638773421305663571087669 1653635008247405959789469)
                    ·
                      refine ⟨620113128092777234921051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1653635008247405959789469 620113128092777234921051)
                      ·
                        rfl

theorem cell23_1207666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_1207666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207666 prefixEnd_1207666 := by exact prefixLift 1207666
  have htrace : WordTrace (prefixWord ++ tailWord_1207666) baseStart_1207666 baseEnd_1207666 := by
    simpa [prefixWord, tailWord_1207666, baseEnd_1207666] using wordTrace_append hprefix tailTrace_1207666
  have hstable : (prefixWord ++ tailWord_1207666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207666).length < 2 ^ (prefixWord ++ tailWord_1207666).sum := by decide
  have hdescent : baseEnd_1207666 < baseStart_1207666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207679 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 5]
def baseStart_1207679 : Nat := 118140960795 + 1207679 * 2 ^ 59
def prefixEnd_1207679 : Nat := 4983230072969 + 3 ^ 40 * 1207679 * 2
def baseEnd_1207679 : Nat := 620119803341285684058491

theorem tailTrace_1207679 : CollatzResearch.WordTrace tailWord_1207679 prefixEnd_1207679 620119803341285684058491 := by
  unfold tailWord_1207679
  simp only [CollatzResearch.WordTrace]
  refine ⟨44047671791792712997498091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29365114527861808664998727 44047671791792712997498091)
  ·
    refine ⟨66071507687689069496247137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44047671791792712997498091 66071507687689069496247137)
    ·
      refine ⟨49553630765766802122185353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66071507687689069496247137 49553630765766802122185353)
      ·
        refine ⟨37165223074325101591639015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49553630765766802122185353 37165223074325101591639015)
        ·
          refine ⟨55747834611487652387458523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37165223074325101591639015 55747834611487652387458523)
          ·
            refine ⟨83621751917231478581187785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55747834611487652387458523 83621751917231478581187785)
            ·
              refine ⟨62716313937923608935890839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83621751917231478581187785 62716313937923608935890839)
              ·
                refine ⟨94074470906885413403836259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62716313937923608935890839 94074470906885413403836259)
                ·
                  refine ⟨141111706360328120105754389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94074470906885413403836259 141111706360328120105754389)
                  ·
                    refine ⟨6614611235640380629957237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 141111706360328120105754389 6614611235640380629957237)
                    ·
                      refine ⟨620119803341285684058491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6614611235640380629957237 620119803341285684058491)
                      ·
                        rfl

theorem cell23_1207679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_1207679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207679 prefixEnd_1207679 := by exact prefixLift 1207679
  have htrace : WordTrace (prefixWord ++ tailWord_1207679) baseStart_1207679 baseEnd_1207679 := by
    simpa [prefixWord, tailWord_1207679, baseEnd_1207679] using wordTrace_append hprefix tailTrace_1207679
  have hstable : (prefixWord ++ tailWord_1207679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207679).length < 2 ^ (prefixWord ++ tailWord_1207679).sum := by decide
  have hdescent : baseEnd_1207679 < baseStart_1207679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207694 : List Nat := [4, 1, 1, 4, 2, 1, 3, 2, 1, 4]
def baseStart_1207694 : Nat := 118140960795 + 1207694 * 2 ^ 59
def prefixEnd_1207694 : Nat := 4983230072969 + 3 ^ 40 * 1207694 * 2
def baseEnd_1207694 : Nat := 206709168517034375123641

theorem tailTrace_1207694 : CollatzResearch.WordTrace tailWord_1207694 prefixEnd_1207694 206709168517034375123641 := by
  unfold tailWord_1207694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5506027360842296319911767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29365479257825580372862757 5506027360842296319911767)
  ·
    refine ⟨8259041041263444479867651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5506027360842296319911767 8259041041263444479867651)
    ·
      refine ⟨12388561561895166719801477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8259041041263444479867651 12388561561895166719801477)
      ·
        refine ⟨2322855292855343759962777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12388561561895166719801477 2322855292855343759962777)
        ·
          refine ⟨1742141469641507819972083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2322855292855343759962777 1742141469641507819972083)
          ·
            refine ⟨2613212204462261729958125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1742141469641507819972083 2613212204462261729958125)
            ·
              refine ⟨979954576673348148734297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2613212204462261729958125 979954576673348148734297)
              ·
                refine ⟨734965932505011111550723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 979954576673348148734297 734965932505011111550723)
                ·
                  refine ⟨1102448898757516667326085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 734965932505011111550723 1102448898757516667326085)
                  ·
                    refine ⟨206709168517034375123641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1102448898757516667326085 206709168517034375123641)
                    ·
                      rfl

theorem cell23_1207694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_1207694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207694 prefixEnd_1207694 := by exact prefixLift 1207694
  have htrace : WordTrace (prefixWord ++ tailWord_1207694) baseStart_1207694 baseEnd_1207694 := by
    simpa [prefixWord, tailWord_1207694, baseEnd_1207694] using wordTrace_append hprefix tailTrace_1207694
  have hstable : (prefixWord ++ tailWord_1207694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207694).length < 2 ^ (prefixWord ++ tailWord_1207694).sum := by decide
  have hdescent : baseEnd_1207694 < baseStart_1207694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207716 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_1207716 : Nat := 118140960795 + 1207716 * 2 ^ 59
def prefixEnd_1207716 : Nat := 4983230072969 + 3 ^ 40 * 1207716 * 2
def baseEnd_1207716 : Nat := 206712934041834013098607

theorem tailTrace_1207716 : CollatzResearch.WordTrace tailWord_1207716 prefixEnd_1207716 206712934041834013098607 := by
  unfold tailWord_1207716
  simp only [CollatzResearch.WordTrace]
  refine ⟨22024510646329334158297501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29366014195105778877730001 22024510646329334158297501)
  ·
    refine ⟨8259191492373500309361563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22024510646329334158297501 8259191492373500309361563)
    ·
      refine ⟨12388787238560250464042345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8259191492373500309361563 12388787238560250464042345)
      ·
        refine ⟨9291590428920187848031759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12388787238560250464042345 9291590428920187848031759)
        ·
          refine ⟨13937385643380281772047639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9291590428920187848031759 13937385643380281772047639)
          ·
            refine ⟨20906078465070422658071459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13937385643380281772047639 20906078465070422658071459)
            ·
              refine ⟨31359117697605633987107189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20906078465070422658071459 31359117697605633987107189)
              ·
                refine ⟨2939917284150528186291299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31359117697605633987107189 2939917284150528186291299)
                ·
                  refine ⟨4409875926225792279436949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2939917284150528186291299 4409875926225792279436949)
                  ·
                    refine ⟨206712934041834013098607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4409875926225792279436949 206712934041834013098607)
                    ·
                      rfl

theorem cell23_1207716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_1207716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207716 prefixEnd_1207716 := by exact prefixLift 1207716
  have htrace : WordTrace (prefixWord ++ tailWord_1207716) baseStart_1207716 baseEnd_1207716 := by
    simpa [prefixWord, tailWord_1207716, baseEnd_1207716] using wordTrace_append hprefix tailTrace_1207716
  have hstable : (prefixWord ++ tailWord_1207716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207716).length < 2 ^ (prefixWord ++ tailWord_1207716).sum := by decide
  have hdescent : baseEnd_1207716 < baseStart_1207716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207720 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1207720 : Nat := 118140960795 + 1207720 * 2 ^ 59
def prefixEnd_1207720 : Nat := 4983230072969 + 3 ^ 40 * 1207720 * 2
def baseEnd_1207720 : Nat := 206713618682706674548601

theorem tailTrace_1207720 : CollatzResearch.WordTrace tailWord_1207720 prefixEnd_1207720 206713618682706674548601 := by
  unfold tailWord_1207720
  simp only [CollatzResearch.WordTrace]
  refine ⟨22024583592322088499870307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29366111456429451333160409 22024583592322088499870307)
  ·
    refine ⟨33036875388483132749805461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22024583592322088499870307 33036875388483132749805461)
    ·
      refine ⟨1548603533835146847647131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33036875388483132749805461 1548603533835146847647131)
      ·
        refine ⟨2322905300752720271470697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1548603533835146847647131 2322905300752720271470697)
        ·
          refine ⟨1742178975564540203603023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2322905300752720271470697 1742178975564540203603023)
          ·
            refine ⟨2613268463346810305404535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1742178975564540203603023 2613268463346810305404535)
            ·
              refine ⟨3919902695020215458106803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613268463346810305404535 3919902695020215458106803)
              ·
                refine ⟨5879854042530323187160205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3919902695020215458106803 5879854042530323187160205)
                ·
                  refine ⟨2204945265948871195185077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5879854042530323187160205 2204945265948871195185077)
                  ·
                    refine ⟨206713618682706674548601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2204945265948871195185077 206713618682706674548601)
                    ·
                      rfl

theorem cell23_1207720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1207720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207720 prefixEnd_1207720 := by exact prefixLift 1207720
  have htrace : WordTrace (prefixWord ++ tailWord_1207720) baseStart_1207720 baseEnd_1207720 := by
    simpa [prefixWord, tailWord_1207720, baseEnd_1207720] using wordTrace_append hprefix tailTrace_1207720
  have hstable : (prefixWord ++ tailWord_1207720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207720).length < 2 ^ (prefixWord ++ tailWord_1207720).sum := by decide
  have hdescent : baseEnd_1207720 < baseStart_1207720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207733 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 1, 6]
def baseStart_1207733 : Nat := 118140960795 + 1207733 * 2 ^ 59
def prefixEnd_1207733 : Nat := 4983230072969 + 3 ^ 40 * 1207733 * 2
def baseEnd_1207733 : Nat := 206715843765542824261081

theorem tailTrace_1207733 : CollatzResearch.WordTrace tailWord_1207733 prefixEnd_1207733 206715843765542824261081 := by
  unfold tailWord_1207733
  simp only [CollatzResearch.WordTrace]
  refine ⟨44049641333597080219963853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29366427555731386813309235 44049641333597080219963853)
  ·
    refine ⟨16518615500098905082486445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44049641333597080219963853 16518615500098905082486445)
    ·
      refine ⟨6194480812537089405932417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16518615500098905082486445 6194480812537089405932417)
      ·
        refine ⟨4645860609402817054449313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6194480812537089405932417 4645860609402817054449313)
        ·
          refine ⟨3484395457052112790836985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4645860609402817054449313 3484395457052112790836985)
          ·
            refine ⟨2613296592789084593127739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3484395457052112790836985 2613296592789084593127739)
            ·
              refine ⟨3919944889183626889691609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613296592789084593127739 3919944889183626889691609)
              ·
                refine ⟨2939958666887720167268707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3919944889183626889691609 2939958666887720167268707)
                ·
                  refine ⟨4409938000331580250903061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2939958666887720167268707 4409938000331580250903061)
                  ·
                    refine ⟨206715843765542824261081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4409938000331580250903061 206715843765542824261081)
                    ·
                      rfl

theorem cell23_1207733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_1207733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207733 prefixEnd_1207733 := by exact prefixLift 1207733
  have htrace : WordTrace (prefixWord ++ tailWord_1207733) baseStart_1207733 baseEnd_1207733 := by
    simpa [prefixWord, tailWord_1207733, baseEnd_1207733] using wordTrace_append hprefix tailTrace_1207733
  have hstable : (prefixWord ++ tailWord_1207733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207733).length < 2 ^ (prefixWord ++ tailWord_1207733).sum := by decide
  have hdescent : baseEnd_1207733 < baseStart_1207733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207736 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_1207736 : Nat := 118140960795 + 1207736 * 2 ^ 59
def prefixEnd_1207736 : Nat := 4983230072969 + 3 ^ 40 * 1207736 * 2
def baseEnd_1207736 : Nat := 620149071738591961045729

theorem tailTrace_1207736 : CollatzResearch.WordTrace tailWord_1207736 prefixEnd_1207736 620149071738591961045729 := by
  unfold tailWord_1207736
  simp only [CollatzResearch.WordTrace]
  refine ⟨22024875376293105866161531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29366500501724141154882041 22024875376293105866161531)
  ·
    refine ⟨33037313064439658799242297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22024875376293105866161531 33037313064439658799242297)
    ·
      refine ⟨24777984798329744099431723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33037313064439658799242297 24777984798329744099431723)
      ·
        refine ⟨37166977197494616149147585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24777984798329744099431723 37166977197494616149147585)
        ·
          refine ⟨27875232898120962111860689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37166977197494616149147585 27875232898120962111860689)
          ·
            refine ⟨20906424673590721583895517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27875232898120962111860689 20906424673590721583895517)
            ·
              refine ⟨7839909252596520593960819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20906424673590721583895517 7839909252596520593960819)
              ·
                refine ⟨11759863878894780890941229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7839909252596520593960819 11759863878894780890941229)
                ·
                  refine ⟨4409948954585542834102961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11759863878894780890941229 4409948954585542834102961)
                  ·
                    refine ⟨3307461715939157125577221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4409948954585542834102961 3307461715939157125577221)
                    ·
                      refine ⟨620149071738591961045729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3307461715939157125577221 620149071738591961045729)
                      ·
                        rfl

theorem cell23_1207736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_1207736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207736 prefixEnd_1207736 := by exact prefixLift 1207736
  have htrace : WordTrace (prefixWord ++ tailWord_1207736) baseStart_1207736 baseEnd_1207736 := by
    simpa [prefixWord, tailWord_1207736, baseEnd_1207736] using wordTrace_append hprefix tailTrace_1207736
  have hstable : (prefixWord ++ tailWord_1207736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207736).length < 2 ^ (prefixWord ++ tailWord_1207736).sum := by decide
  have hdescent : baseEnd_1207736 < baseStart_1207736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207743 : List Nat := [1, 1, 2, 2, 2, 1, 1, 7, 1, 2, 3]
def baseStart_1207743 : Nat := 118140960795 + 1207743 * 2 ^ 59
def prefixEnd_1207743 : Nat := 4983230072969 + 3 ^ 40 * 1207743 * 2
def baseEnd_1207743 : Nat := 620152666103173433658197

theorem tailTrace_1207743 : CollatzResearch.WordTrace tailWord_1207743 prefixEnd_1207743 620152666103173433658197 := by
  unfold tailWord_1207743
  simp only [CollatzResearch.WordTrace]
  refine ⟨44050006063560851927827883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29366670709040567951885255 44050006063560851927827883)
  ·
    refine ⟨66075009095341277891741825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44050006063560851927827883 66075009095341277891741825)
    ·
      refine ⟨49556256821505958418806369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66075009095341277891741825 49556256821505958418806369)
      ·
        refine ⟨37167192616129468814104777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49556256821505958418806369 37167192616129468814104777)
        ·
          refine ⟨27875394462097101610578583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37167192616129468814104777 27875394462097101610578583)
          ·
            refine ⟨41813091693145652415867875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27875394462097101610578583 41813091693145652415867875)
            ·
              refine ⟨62719637539718478623801813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41813091693145652415867875 62719637539718478623801813)
              ·
                refine ⟨1469991504837151842745355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 62719637539718478623801813 1469991504837151842745355)
                ·
                  refine ⟨2204987257255727764118033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469991504837151842745355 2204987257255727764118033)
                  ·
                    refine ⟨1653740442941795823088525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2204987257255727764118033 1653740442941795823088525)
                    ·
                      refine ⟨620152666103173433658197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1653740442941795823088525 620152666103173433658197)
                      ·
                        rfl

theorem cell23_1207743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_1207743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207743 prefixEnd_1207743 := by exact prefixLift 1207743
  have htrace : WordTrace (prefixWord ++ tailWord_1207743) baseStart_1207743 baseEnd_1207743 := by
    simpa [prefixWord, tailWord_1207743, baseEnd_1207743] using wordTrace_append hprefix tailTrace_1207743
  have hstable : (prefixWord ++ tailWord_1207743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207743).length < 2 ^ (prefixWord ++ tailWord_1207743).sum := by decide
  have hdescent : baseEnd_1207743 < baseStart_1207743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207790 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_1207790 : Nat := 118140960795 + 1207790 * 2 ^ 59
def prefixEnd_1207790 : Nat := 4983230072969 + 3 ^ 40 * 1207790 * 2
def baseEnd_1207790 : Nat := 620176799693934749770481

theorem tailTrace_1207790 : CollatzResearch.WordTrace tailWord_1207790 prefixEnd_1207790 620176799693934749770481 := by
  unfold tailWord_1207790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5506465036798822369348603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29367813529593719303192549 5506465036798822369348603)
  ·
    refine ⟨8259697555198233554022905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5506465036798822369348603 8259697555198233554022905)
    ·
      refine ⟨6194773166398675165517179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8259697555198233554022905 6194773166398675165517179)
      ·
        refine ⟨9292159749598012748275769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6194773166398675165517179 9292159749598012748275769)
        ·
          refine ⟨6969119812198509561206827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9292159749598012748275769 6969119812198509561206827)
          ·
            refine ⟨10453679718297764341810241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6969119812198509561206827 10453679718297764341810241)
            ·
              refine ⟨7840259788723323256357681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10453679718297764341810241 7840259788723323256357681)
              ·
                refine ⟨5880194841542492442268261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7840259788723323256357681 5880194841542492442268261)
                ·
                  refine ⟨1102536532789217332925299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5880194841542492442268261 1102536532789217332925299)
                  ·
                    refine ⟨1653804799183825999387949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1102536532789217332925299 1653804799183825999387949)
                    ·
                      refine ⟨620176799693934749770481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1653804799183825999387949 620176799693934749770481)
                      ·
                        rfl

theorem cell23_1207790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_1207790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207790 prefixEnd_1207790 := by exact prefixLift 1207790
  have htrace : WordTrace (prefixWord ++ tailWord_1207790) baseStart_1207790 baseEnd_1207790 := by
    simpa [prefixWord, tailWord_1207790, baseEnd_1207790] using wordTrace_append hprefix tailTrace_1207790
  have hstable : (prefixWord ++ tailWord_1207790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207790).length < 2 ^ (prefixWord ++ tailWord_1207790).sum := by decide
  have hdescent : baseEnd_1207790 < baseStart_1207790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207794 : List Nat := [3, 2, 1, 4, 1, 3, 2, 1, 1, 2, 3]
def baseStart_1207794 : Nat := 118140960795 + 1207794 * 2 ^ 59
def prefixEnd_1207794 : Nat := 4983230072969 + 3 ^ 40 * 1207794 * 2
def baseEnd_1207794 : Nat := 620178853616552734120463

theorem tailTrace_1207794 : CollatzResearch.WordTrace tailWord_1207794 prefixEnd_1207794 620178853616552734120463 := by
  unfold tailWord_1207794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11012966546594021909483609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29367910790917391758622957 11012966546594021909483609)
  ·
    refine ⟨8259724909945516432112707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11012966546594021909483609 8259724909945516432112707)
    ·
      refine ⟨12389587364918274648169061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8259724909945516432112707 12389587364918274648169061)
      ·
        refine ⟨2323047630922176496531699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12389587364918274648169061 2323047630922176496531699)
        ·
          refine ⟨3484571446383264744797549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2323047630922176496531699 3484571446383264744797549)
          ·
            refine ⟨1306714292393724279299081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3484571446383264744797549 1306714292393724279299081)
            ·
              refine ⟨980035719295293209474311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1306714292393724279299081 980035719295293209474311)
              ·
                refine ⟨1470053578942939814211467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 980035719295293209474311 1470053578942939814211467)
                ·
                  refine ⟨2205080368414409721317201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1470053578942939814211467 2205080368414409721317201)
                  ·
                    refine ⟨1653810276310807290987901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2205080368414409721317201 1653810276310807290987901)
                    ·
                      refine ⟨620178853616552734120463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1653810276310807290987901 620178853616552734120463)
                      ·
                        rfl

theorem cell23_1207794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_1207794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207794 prefixEnd_1207794 := by exact prefixLift 1207794
  have htrace : WordTrace (prefixWord ++ tailWord_1207794) baseStart_1207794 baseEnd_1207794 := by
    simpa [prefixWord, tailWord_1207794, baseEnd_1207794] using wordTrace_append hprefix tailTrace_1207794
  have hstable : (prefixWord ++ tailWord_1207794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207794).length < 2 ^ (prefixWord ++ tailWord_1207794).sum := by decide
  have hdescent : baseEnd_1207794 < baseStart_1207794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207821 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_1207821 : Nat := 118140960795 + 1207821 * 2 ^ 59
def prefixEnd_1207821 : Nat := 4983230072969 + 3 ^ 40 * 1207821 * 2
def baseEnd_1207821 : Nat := 620192717594224128482839

theorem tailTrace_1207821 : CollatzResearch.WordTrace tailWord_1207821 prefixEnd_1207821 620192717594224128482839 := by
  unfold tailWord_1207821
  simp only [CollatzResearch.WordTrace]
  refine ⟨44052850957278271249167317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29368567304852180832778211 44052850957278271249167317)
  ·
    refine ⟨1032488694311209482402359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 44052850957278271249167317 1032488694311209482402359)
    ·
      refine ⟨1548733041466814223603539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1032488694311209482402359 1548733041466814223603539)
      ·
        refine ⟨2323099562200221335405309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1548733041466814223603539 2323099562200221335405309)
        ·
          refine ⟨871162335825083000776991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2323099562200221335405309 871162335825083000776991)
          ·
            refine ⟨1306743503737624501165487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871162335825083000776991 1306743503737624501165487)
            ·
              refine ⟨1960115255606436751748231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1306743503737624501165487 1960115255606436751748231)
              ·
                refine ⟨2940172883409655127622347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960115255606436751748231 2940172883409655127622347)
                ·
                  refine ⟨4410259325114482691433521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940172883409655127622347 4410259325114482691433521)
                  ·
                    refine ⟨3307694493835862018575141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4410259325114482691433521 3307694493835862018575141)
                    ·
                      refine ⟨620192717594224128482839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3307694493835862018575141 620192717594224128482839)
                      ·
                        rfl

theorem cell23_1207821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_1207821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207821 prefixEnd_1207821 := by exact prefixLift 1207821
  have htrace : WordTrace (prefixWord ++ tailWord_1207821) baseStart_1207821 baseEnd_1207821 := by
    simpa [prefixWord, tailWord_1207821, baseEnd_1207821] using wordTrace_append hprefix tailTrace_1207821
  have hstable : (prefixWord ++ tailWord_1207821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207821).length < 2 ^ (prefixWord ++ tailWord_1207821).sum := by decide
  have hdescent : baseEnd_1207821 < baseStart_1207821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207900 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1207900 : Nat := 118140960795 + 1207900 * 2 ^ 59
def prefixEnd_1207900 : Nat := 4983230072969 + 3 ^ 40 * 1207900 * 2
def baseEnd_1207900 : Nat := 206744427521976439798325

theorem tailTrace_1207900 : CollatzResearch.WordTrace tailWord_1207900 prefixEnd_1207900 206744427521976439798325 := by
  unfold tailWord_1207900
  simp only [CollatzResearch.WordTrace]
  refine ⟨22027866161996033870646577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29370488215994711827528769 22027866161996033870646577)
  ·
    refine ⟨16520899621497025402984933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22027866161996033870646577 16520899621497025402984933)
    ·
      refine ⟨3097668679030692263059675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16520899621497025402984933 3097668679030692263059675)
      ·
        refine ⟨4646503018546038394589513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3097668679030692263059675 4646503018546038394589513)
        ·
          refine ⟨3484877263909528795942135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4646503018546038394589513 3484877263909528795942135)
          ·
            refine ⟨5227315895864293193913203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3484877263909528795942135 5227315895864293193913203)
            ·
              refine ⟨7840973843796439790869805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5227315895864293193913203 7840973843796439790869805)
              ·
                refine ⟨2940365191423664921576177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7840973843796439790869805 2940365191423664921576177)
                ·
                  refine ⟨2205273893567748691182133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2940365191423664921576177 2205273893567748691182133)
                  ·
                    refine ⟨206744427521976439798325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2205273893567748691182133 206744427521976439798325)
                    ·
                      rfl

theorem cell23_1207900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1207900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207900 prefixEnd_1207900 := by exact prefixLift 1207900
  have htrace : WordTrace (prefixWord ++ tailWord_1207900) baseStart_1207900 baseEnd_1207900 := by
    simpa [prefixWord, tailWord_1207900, baseEnd_1207900] using wordTrace_append hprefix tailTrace_1207900
  have hstable : (prefixWord ++ tailWord_1207900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207900).length < 2 ^ (prefixWord ++ tailWord_1207900).sum := by decide
  have hdescent : baseEnd_1207900 < baseStart_1207900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207920 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 4]
def baseStart_1207920 : Nat := 118140960795 + 1207920 * 2 ^ 59
def prefixEnd_1207920 : Nat := 4983230072969 + 3 ^ 40 * 1207920 * 2
def baseEnd_1207920 : Nat := 620243552179019241144883

theorem tailTrace_1207920 : CollatzResearch.WordTrace tailWord_1207920 prefixEnd_1207920 620243552179019241144883 := by
  unfold tailWord_1207920
  simp only [CollatzResearch.WordTrace]
  refine ⟨22028230891959805578510607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29370974522613074104680809 22028230891959805578510607)
  ·
    refine ⟨33042346337939708367765911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22028230891959805578510607 33042346337939708367765911)
    ·
      refine ⟨49563519506909562551648867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33042346337939708367765911 49563519506909562551648867)
      ·
        refine ⟨74345279260364343827473301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49563519506909562551648867 74345279260364343827473301)
        ·
          refine ⟨3484934965329578616912811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74345279260364343827473301 3484934965329578616912811)
          ·
            refine ⟨5227402447994367925369217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3484934965329578616912811 5227402447994367925369217)
            ·
              refine ⟨3920551835995775944026913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5227402447994367925369217 3920551835995775944026913)
              ·
                refine ⟨2940413876996831958020185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3920551835995775944026913 2940413876996831958020185)
                ·
                  refine ⟨2205310407747623968515139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2940413876996831958020185 2205310407747623968515139)
                  ·
                    refine ⟨3307965611621435952772709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2205310407747623968515139 3307965611621435952772709)
                    ·
                      refine ⟨620243552179019241144883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3307965611621435952772709 620243552179019241144883)
                      ·
                        rfl

theorem cell23_1207920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_1207920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207920 prefixEnd_1207920 := by exact prefixLift 1207920
  have htrace : WordTrace (prefixWord ++ tailWord_1207920) baseStart_1207920 baseEnd_1207920 := by
    simpa [prefixWord, tailWord_1207920, baseEnd_1207920] using wordTrace_append hprefix tailTrace_1207920
  have hstable : (prefixWord ++ tailWord_1207920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207920).length < 2 ^ (prefixWord ++ tailWord_1207920).sum := by decide
  have hdescent : baseEnd_1207920 < baseStart_1207920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207937 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_1207937 : Nat := 118140960795 + 1207937 * 2 ^ 59
def prefixEnd_1207937 : Nat := 4983230072969 + 3 ^ 40 * 1207937 * 2
def baseEnd_1207937 : Nat := 620252281350145674632305

theorem tailTrace_1207937 : CollatzResearch.WordTrace tailWord_1207937 prefixEnd_1207937 620252281350145674632305 := by
  unfold tailWord_1207937
  simp only [CollatzResearch.WordTrace]
  refine ⟨44057081824858023060390065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29371387883238682040260043 44057081824858023060390065)
  ·
    refine ⟨33042811368643517295292549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44057081824858023060390065 33042811368643517295292549)
    ·
      refine ⟨6195527131620659492867353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33042811368643517295292549 6195527131620659492867353)
      ·
        refine ⟨4646645348715494619650515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6195527131620659492867353 4646645348715494619650515)
        ·
          refine ⟨6969968023073241929475773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4646645348715494619650515 6969968023073241929475773)
          ·
            refine ⟨2613738008652465723553415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6969968023073241929475773 2613738008652465723553415)
            ·
              refine ⟨3920607012978698585330123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613738008652465723553415 3920607012978698585330123)
              ·
                refine ⟨5880910519468047877995185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3920607012978698585330123 5880910519468047877995185)
                ·
                  refine ⟨4410682889601035908496389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5880910519468047877995185 4410682889601035908496389)
                  ·
                    refine ⟨827003041800194232843073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4410682889601035908496389 827003041800194232843073)
                    ·
                      refine ⟨620252281350145674632305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 827003041800194232843073 620252281350145674632305)
                      ·
                        rfl

theorem cell23_1207937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_1207937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207937 prefixEnd_1207937 := by exact prefixLift 1207937
  have htrace : WordTrace (prefixWord ++ tailWord_1207937) baseStart_1207937 baseEnd_1207937 := by
    simpa [prefixWord, tailWord_1207937, baseEnd_1207937] using wordTrace_append hprefix tailTrace_1207937
  have hstable : (prefixWord ++ tailWord_1207937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207937).length < 2 ^ (prefixWord ++ tailWord_1207937).sum := by decide
  have hdescent : baseEnd_1207937 < baseStart_1207937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207953 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 3]
def baseStart_1207953 : Nat := 118140960795 + 1207953 * 2 ^ 59
def prefixEnd_1207953 : Nat := 4983230072969 + 3 ^ 40 * 1207953 * 2
def baseEnd_1207953 : Nat := 620260497040617612032231

theorem tailTrace_1207953 : CollatzResearch.WordTrace tailWord_1207953 prefixEnd_1207953 620260497040617612032231 := by
  unfold tailWord_1207953
  simp only [CollatzResearch.WordTrace]
  refine ⟨44057665392800057792972513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29371776928533371861981675 44057665392800057792972513)
  ·
    refine ⟨33043249044600043344729385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44057665392800057792972513 33043249044600043344729385)
    ·
      refine ⟨24782436783450032508547039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33043249044600043344729385 24782436783450032508547039)
      ·
        refine ⟨37173655175175048762820559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24782436783450032508547039 37173655175175048762820559)
        ·
          refine ⟨55760482762762573144230839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37173655175175048762820559 55760482762762573144230839)
          ·
            refine ⟨83640724144143859716346259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55760482762762573144230839 83640724144143859716346259)
            ·
              refine ⟨125461086216215789574519389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83640724144143859716346259 125461086216215789574519389)
              ·
                refine ⟨47047907331080921090444771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125461086216215789574519389 47047907331080921090444771)
                ·
                  refine ⟨70571860996621381635667157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47047907331080921090444771 70571860996621381635667157)
                  ·
                    refine ⟨1654027992108313632085949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 70571860996621381635667157 1654027992108313632085949)
                    ·
                      refine ⟨620260497040617612032231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1654027992108313632085949 620260497040617612032231)
                      ·
                        rfl

theorem cell23_1207953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_1207953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207953 prefixEnd_1207953 := by exact prefixLift 1207953
  have htrace : WordTrace (prefixWord ++ tailWord_1207953) baseStart_1207953 baseEnd_1207953 := by
    simpa [prefixWord, tailWord_1207953, baseEnd_1207953] using wordTrace_append hprefix tailTrace_1207953
  have hstable : (prefixWord ++ tailWord_1207953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207953).length < 2 ^ (prefixWord ++ tailWord_1207953).sum := by decide
  have hdescent : baseEnd_1207953 < baseStart_1207953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207954 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_1207954 : Nat := 118140960795 + 1207954 * 2 ^ 59
def prefixEnd_1207954 : Nat := 4983230072969 + 3 ^ 40 * 1207954 * 2
def baseEnd_1207954 : Nat := 620261010521272108119727

theorem tailTrace_1207954 : CollatzResearch.WordTrace tailWord_1207954 prefixEnd_1207954 620261010521272108119727 := by
  unfold tailWord_1207954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11014425466449108740939729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29371801243864289975839277 11014425466449108740939729)
  ·
    refine ⟨8260819099836831555704797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11014425466449108740939729 8260819099836831555704797)
    ·
      refine ⟨3097807162438811833389299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8260819099836831555704797 3097807162438811833389299)
      ·
        refine ⟨4646710743658217750083949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3097807162438811833389299 4646710743658217750083949)
        ·
          refine ⟨1742516528871831656281481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4646710743658217750083949 1742516528871831656281481)
          ·
            refine ⟨1306887396653873742211111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1742516528871831656281481 1306887396653873742211111)
            ·
              refine ⟨1960331094980810613316667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1306887396653873742211111 1960331094980810613316667)
              ·
                refine ⟨2940496642471215919975001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960331094980810613316667 2940496642471215919975001)
                ·
                  refine ⟨2205372481853411939981251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2940496642471215919975001 2205372481853411939981251)
                  ·
                    refine ⟨3308058722780117909971877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2205372481853411939981251 3308058722780117909971877)
                    ·
                      refine ⟨620261010521272108119727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3308058722780117909971877 620261010521272108119727)
                      ·
                        rfl

theorem cell23_1207954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_1207954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207954 prefixEnd_1207954 := by exact prefixLift 1207954
  have htrace : WordTrace (prefixWord ++ tailWord_1207954) baseStart_1207954 baseEnd_1207954 := by
    simpa [prefixWord, tailWord_1207954, baseEnd_1207954] using wordTrace_append hprefix tailTrace_1207954
  have hstable : (prefixWord ++ tailWord_1207954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207954).length < 2 ^ (prefixWord ++ tailWord_1207954).sum := by decide
  have hdescent : baseEnd_1207954 < baseStart_1207954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207987 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 3, 1, 3]
def baseStart_1207987 : Nat := 118140960795 + 1207987 * 2 ^ 59
def prefixEnd_1207987 : Nat := 4983230072969 + 3 ^ 40 * 1207987 * 2
def baseEnd_1207987 : Nat := 620277955382870479007075

theorem tailTrace_1207987 : CollatzResearch.WordTrace tailWord_1207987 prefixEnd_1207987 620277955382870479007075 := by
  unfold tailWord_1207987
  simp only [CollatzResearch.WordTrace]
  refine ⟨44058905474676881599710215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29372603649784587733140143 44058905474676881599710215)
  ·
    refine ⟨66088358212015322399565323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44058905474676881599710215 66088358212015322399565323)
    ·
      refine ⟨99132537318022983599347985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66088358212015322399565323 99132537318022983599347985)
      ·
        refine ⟨74349402988517237699510989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99132537318022983599347985 74349402988517237699510989)
        ·
          refine ⟨27881026120693964137316621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74349402988517237699510989 27881026120693964137316621)
          ·
            refine ⟨10455384795260236551493733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27881026120693964137316621 10455384795260236551493733)
            ·
              refine ⟨1960384649111294353405075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10455384795260236551493733 1960384649111294353405075)
              ·
                refine ⟨2940576973666941530107613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960384649111294353405075 2940576973666941530107613)
                ·
                  refine ⟨1102716365125103073790355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2940576973666941530107613 1102716365125103073790355)
                  ·
                    refine ⟨1654074547687654610685533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1102716365125103073790355 1654074547687654610685533)
                    ·
                      refine ⟨620277955382870479007075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1654074547687654610685533 620277955382870479007075)
                      ·
                        rfl

theorem cell23_1207987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 3, 1, 3].length) (baseStart_1207987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1207987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1207987 prefixEnd_1207987 := by exact prefixLift 1207987
  have htrace : WordTrace (prefixWord ++ tailWord_1207987) baseStart_1207987 baseEnd_1207987 := by
    simpa [prefixWord, tailWord_1207987, baseEnd_1207987] using wordTrace_append hprefix tailTrace_1207987
  have hstable : (prefixWord ++ tailWord_1207987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207987).length < 2 ^ (prefixWord ++ tailWord_1207987).sum := by decide
  have hdescent : baseEnd_1207987 < baseStart_1207987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208037 : List Nat := [1, 3, 1, 4, 1, 1, 2, 4, 2, 4]
def baseStart_1208037 : Nat := 118140960795 + 1208037 * 2 ^ 59
def prefixEnd_1208037 : Nat := 4983230072969 + 3 ^ 40 * 1208037 * 2
def baseEnd_1208037 : Nat := 206767876471865094460615

theorem tailTrace_1208037 : CollatzResearch.WordTrace tailWord_1208037 prefixEnd_1208037 206767876471865094460615 := by
  unfold tailWord_1208037
  simp only [CollatzResearch.WordTrace]
  refine ⟨44060729124495740139030365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29373819416330493426020243 44060729124495740139030365)
  ·
    refine ⟨16522773421685902552136387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44060729124495740139030365 16522773421685902552136387)
    ·
      refine ⟨24784160132528853828204581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16522773421685902552136387 24784160132528853828204581)
      ·
        refine ⟨4647030024849160092788359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24784160132528853828204581 4647030024849160092788359)
        ·
          refine ⟨6970545037273740139182539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4647030024849160092788359 6970545037273740139182539)
          ·
            refine ⟨10455817555910610208773809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6970545037273740139182539 10455817555910610208773809)
            ·
              refine ⟨7841863166932957656580357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10455817555910610208773809 7841863166932957656580357)
              ·
                refine ⟨1470349343799929560608817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7841863166932957656580357 1470349343799929560608817)
                ·
                  refine ⟨1102762007849947170456613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1470349343799929560608817 1102762007849947170456613)
                  ·
                    refine ⟨206767876471865094460615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1102762007849947170456613 206767876471865094460615)
                    ·
                      rfl

theorem cell23_1208037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_1208037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208037 prefixEnd_1208037 := by exact prefixLift 1208037
  have htrace : WordTrace (prefixWord ++ tailWord_1208037) baseStart_1208037 baseEnd_1208037 := by
    simpa [prefixWord, tailWord_1208037, baseEnd_1208037] using wordTrace_append hprefix tailTrace_1208037
  have hstable : (prefixWord ++ tailWord_1208037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208037).length < 2 ^ (prefixWord ++ tailWord_1208037).sum := by decide
  have hdescent : baseEnd_1208037 < baseStart_1208037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208040 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_1208040 : Nat := 118140960795 + 1208040 * 2 ^ 59
def prefixEnd_1208040 : Nat := 4983230072969 + 3 ^ 40 * 1208040 * 2
def baseEnd_1208040 : Nat := 620305169857558771644331

theorem tailTrace_1208040 : CollatzResearch.WordTrace tailWord_1208040 prefixEnd_1208040 620305169857558771644331 := by
  unfold tailWord_1208040
  simp only [CollatzResearch.WordTrace]
  refine ⟨22030419271742435825694787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29373892362323247767593049 22030419271742435825694787)
  ·
    refine ⟨33045628907613653738542181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22030419271742435825694787 33045628907613653738542181)
    ·
      refine ⟨6196055420177560075976659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33045628907613653738542181 6196055420177560075976659)
      ·
        refine ⟨9294083130266340113964989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6196055420177560075976659 9294083130266340113964989)
        ·
          refine ⟨3485281173849877542736871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9294083130266340113964989 3485281173849877542736871)
          ·
            refine ⟨5227921760774816314105307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3485281173849877542736871 5227921760774816314105307)
            ·
              refine ⟨7841882641162224471157961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5227921760774816314105307 7841882641162224471157961)
              ·
                refine ⟨5881411980871668353368471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7841882641162224471157961 5881411980871668353368471)
                ·
                  refine ⟨8822117971307502530052707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5881411980871668353368471 8822117971307502530052707)
                  ·
                    refine ⟨13233176956961253795079061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8822117971307502530052707 13233176956961253795079061)
                    ·
                      refine ⟨620305169857558771644331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13233176956961253795079061 620305169857558771644331)
                      ·
                        rfl

theorem cell23_1208040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_1208040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208040 prefixEnd_1208040 := by exact prefixLift 1208040
  have htrace : WordTrace (prefixWord ++ tailWord_1208040) baseStart_1208040 baseEnd_1208040 := by
    simpa [prefixWord, tailWord_1208040, baseEnd_1208040] using wordTrace_append hprefix tailTrace_1208040
  have hstable : (prefixWord ++ tailWord_1208040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208040).length < 2 ^ (prefixWord ++ tailWord_1208040).sum := by decide
  have hdescent : baseEnd_1208040 < baseStart_1208040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208044 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 3, 2, 2]
def baseStart_1208044 : Nat := 118140960795 + 1208044 * 2 ^ 59
def prefixEnd_1208044 : Nat := 4983230072969 + 3 ^ 40 * 1208044 * 2
def baseEnd_1208044 : Nat := 620307223780176755994313

theorem tailTrace_1208044 : CollatzResearch.WordTrace tailWord_1208044 prefixEnd_1208044 620307223780176755994313 := by
  unfold tailWord_1208044
  simp only [CollatzResearch.WordTrace]
  refine ⟨22030492217735190167267593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29373989623646920223023457 22030492217735190167267593)
  ·
    refine ⟨16522869163301392625450695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22030492217735190167267593 16522869163301392625450695)
    ·
      refine ⟨24784303744952088938176043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16522869163301392625450695 24784303744952088938176043)
      ·
        refine ⟨37176455617428133407264065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24784303744952088938176043 37176455617428133407264065)
        ·
          refine ⟨27882341713071100055448049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37176455617428133407264065 27882341713071100055448049)
          ·
            refine ⟨20911756284803325041586037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27882341713071100055448049 20911756284803325041586037)
            ·
              refine ⟨1960477151700311722648691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20911756284803325041586037 1960477151700311722648691)
              ·
                refine ⟨2940715727550467583973037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960477151700311722648691 2940715727550467583973037)
                ·
                  refine ⟨1102768397831425343989889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2940715727550467583973037 1102768397831425343989889)
                  ·
                    refine ⟨827076298373569007992417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1102768397831425343989889 827076298373569007992417)
                    ·
                      refine ⟨620307223780176755994313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 827076298373569007992417 620307223780176755994313)
                      ·
                        rfl

theorem cell23_1208044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 2, 2].length) (baseStart_1208044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208044 prefixEnd_1208044 := by exact prefixLift 1208044
  have htrace : WordTrace (prefixWord ++ tailWord_1208044) baseStart_1208044 baseEnd_1208044 := by
    simpa [prefixWord, tailWord_1208044, baseEnd_1208044] using wordTrace_append hprefix tailTrace_1208044
  have hstable : (prefixWord ++ tailWord_1208044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208044).length < 2 ^ (prefixWord ++ tailWord_1208044).sum := by decide
  have hdescent : baseEnd_1208044 < baseStart_1208044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208050 : List Nat := [3, 2, 1, 3, 1, 1, 4, 8]
def baseStart_1208050 : Nat := 118140960795 + 1208050 * 2 ^ 59
def prefixEnd_1208050 : Nat := 4983230072969 + 3 ^ 40 * 1208050 * 2
def baseEnd_1208050 : Nat := 22974455728300138241455

theorem tailTrace_1208050 : CollatzResearch.WordTrace tailWord_1208050 prefixEnd_1208050 22974455728300138241455 := by
  unfold tailWord_1208050
  simp only [CollatzResearch.WordTrace]
  refine ⟨11015300818362160839813401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29374135515632428906169069 11015300818362160839813401)
  ·
    refine ⟨8261475613771620629860051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11015300818362160839813401 8261475613771620629860051)
    ·
      refine ⟨12392213420657430944790077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8261475613771620629860051 12392213420657430944790077)
      ·
        refine ⟨4647080032746536604296279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12392213420657430944790077 4647080032746536604296279)
        ·
          refine ⟨6970620049119804906444419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4647080032746536604296279 6970620049119804906444419)
          ·
            refine ⟨10455930073679707359666629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6970620049119804906444419 10455930073679707359666629)
            ·
              refine ⟨1960486888814945129937493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10455930073679707359666629 1960486888814945129937493)
              ·
                refine ⟨22974455728300138241455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1960486888814945129937493 22974455728300138241455)
                ·
                  rfl

theorem cell23_1208050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 8].length) (baseStart_1208050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208050 prefixEnd_1208050 := by exact prefixLift 1208050
  have htrace : WordTrace (prefixWord ++ tailWord_1208050) baseStart_1208050 baseEnd_1208050 := by
    simpa [prefixWord, tailWord_1208050, baseEnd_1208050] using wordTrace_append hprefix tailTrace_1208050
  have hstable : (prefixWord ++ tailWord_1208050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208050).length < 2 ^ (prefixWord ++ tailWord_1208050).sum := by decide
  have hdescent : baseEnd_1208050 < baseStart_1208050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208054 : List Nat := [5, 1, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_1208054 : Nat := 118140960795 + 1208054 * 2 ^ 59
def prefixEnd_1208054 : Nat := 4983230072969 + 3 ^ 40 * 1208054 * 2
def baseEnd_1208054 : Nat := 206770786195573905623089

theorem tailTrace_1208054 : CollatzResearch.WordTrace tailWord_1208054 prefixEnd_1208054 206770786195573905623089 := by
  unfold tailWord_1208054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2753834322839634502649951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29374232776956101361599477 2753834322839634502649951)
  ·
    refine ⟨4130751484259451753974927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2753834322839634502649951 4130751484259451753974927)
    ·
      refine ⟨6196127226389177630962391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4130751484259451753974927 6196127226389177630962391)
      ·
        refine ⟨9294190839583766446443587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6196127226389177630962391 9294190839583766446443587)
        ·
          refine ⟨13941286259375649669665381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9294190839583766446443587 13941286259375649669665381)
          ·
            refine ⟨2613991173632934313062259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13941286259375649669665381 2613991173632934313062259)
            ·
              refine ⟨3920986760449401469593389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613991173632934313062259 3920986760449401469593389)
              ·
                refine ⟨1470370035168525551097521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3920986760449401469593389 1470370035168525551097521)
                ·
                  refine ⟨1102777526376394163323141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1470370035168525551097521 1102777526376394163323141)
                  ·
                    refine ⟨206770786195573905623089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1102777526376394163323141 206770786195573905623089)
                    ·
                      rfl

theorem cell23_1208054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_1208054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208054 prefixEnd_1208054 := by exact prefixLift 1208054
  have htrace : WordTrace (prefixWord ++ tailWord_1208054) baseStart_1208054 baseEnd_1208054 := by
    simpa [prefixWord, tailWord_1208054, baseEnd_1208054] using wordTrace_append hprefix tailTrace_1208054
  have hstable : (prefixWord ++ tailWord_1208054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208054).length < 2 ^ (prefixWord ++ tailWord_1208054).sum := by decide
  have hdescent : baseEnd_1208054 < baseStart_1208054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208084 : List Nat := [2, 4, 4, 1, 1, 11]
def baseStart_1208084 : Nat := 118140960795 + 1208084 * 2 ^ 59
def prefixEnd_1208084 : Nat := 4983230072969 + 3 ^ 40 * 1208084 * 2
def baseEnd_1208084 : Nat := 2552789148174306993803

theorem tailTrace_1208084 : CollatzResearch.WordTrace tailWord_1208084 prefixEnd_1208084 2552789148174306993803 := by
  unfold tailWord_1208084
  simp only [CollatzResearch.WordTrace]
  refine ⟨22031221677662733582995653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29374962236883644777327537 22031221677662733582995653)
  ·
    refine ⟨4130854064561762546811685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22031221677662733582995653 4130854064561762546811685)
    ·
      refine ⟨774535137105330477527191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4130854064561762546811685 774535137105330477527191)
      ·
        refine ⟨1161802705657995716290787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774535137105330477527191 1161802705657995716290787)
        ·
          refine ⟨1742704058486993574436181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1161802705657995716290787 1742704058486993574436181)
          ·
            refine ⟨2552789148174306993803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1742704058486993574436181 2552789148174306993803)
            ·
              rfl

theorem cell23_1208084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 11].length) (baseStart_1208084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208084 prefixEnd_1208084 := by exact prefixLift 1208084
  have htrace : WordTrace (prefixWord ++ tailWord_1208084) baseStart_1208084 baseEnd_1208084 := by
    simpa [prefixWord, tailWord_1208084, baseEnd_1208084] using wordTrace_append hprefix tailTrace_1208084
  have hstable : (prefixWord ++ tailWord_1208084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208084).length < 2 ^ (prefixWord ++ tailWord_1208084).sum := by decide
  have hdescent : baseEnd_1208084 < baseStart_1208084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208104 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_1208104 : Nat := 118140960795 + 1208104 * 2 ^ 59
def prefixEnd_1208104 : Nat := 4983230072969 + 3 ^ 40 * 1208104 * 2
def baseEnd_1208104 : Nat := 620338032619446521244037

theorem tailTrace_1208104 : CollatzResearch.WordTrace tailWord_1208104 prefixEnd_1208104 620338032619446521244037 := by
  unfold tailWord_1208104
  simp only [CollatzResearch.WordTrace]
  refine ⟨22031586407626505290859683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29375448543502007054479577 22031586407626505290859683)
  ·
    refine ⟨33047379611439757936289525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22031586407626505290859683 33047379611439757936289525)
    ·
      refine ⟨3098191838572477306527143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33047379611439757936289525 3098191838572477306527143)
      ·
        refine ⟨4647287757858715959790715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3098191838572477306527143 4647287757858715959790715)
        ·
          refine ⟨6970931636788073939686073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4647287757858715959790715 6970931636788073939686073)
          ·
            refine ⟨5228198727591055454764555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6970931636788073939686073 5228198727591055454764555)
            ·
              refine ⟨7842298091386583182146833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5228198727591055454764555 7842298091386583182146833)
              ·
                refine ⟨5881723568539937386610125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7842298091386583182146833 5881723568539937386610125)
                ·
                  refine ⟨2205646338202476519978797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5881723568539937386610125 2205646338202476519978797)
                  ·
                    refine ⟨827117376825928694992049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2205646338202476519978797 827117376825928694992049)
                    ·
                      refine ⟨620338032619446521244037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 827117376825928694992049 620338032619446521244037)
                      ·
                        rfl

theorem cell23_1208104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_1208104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208104 prefixEnd_1208104 := by exact prefixLift 1208104
  have htrace : WordTrace (prefixWord ++ tailWord_1208104) baseStart_1208104 baseEnd_1208104 := by
    simpa [prefixWord, tailWord_1208104, baseEnd_1208104] using wordTrace_append hprefix tailTrace_1208104
  have hstable : (prefixWord ++ tailWord_1208104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208104).length < 2 ^ (prefixWord ++ tailWord_1208104).sum := by decide
  have hdescent : baseEnd_1208104 < baseStart_1208104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208151 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 4, 2, 2]
def baseStart_1208151 : Nat := 118140960795 + 1208151 * 2 ^ 59
def prefixEnd_1208151 : Nat := 4983230072969 + 3 ^ 40 * 1208151 * 2
def baseEnd_1208151 : Nat := 620362166210207837356321

theorem tailTrace_1208151 : CollatzResearch.WordTrace tailWord_1208151 prefixEnd_1208151 620362166210207837356321 := by
  unfold tailWord_1208151
  simp only [CollatzResearch.WordTrace]
  refine ⟨44064887046082737608680307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29376591364055158405786871 44064887046082737608680307)
  ·
    refine ⟨66097330569124106413020461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44064887046082737608680307 66097330569124106413020461)
    ·
      refine ⟨24786498963421539904882673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66097330569124106413020461 24786498963421539904882673)
      ·
        refine ⟨18589874222566154928662005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24786498963421539904882673 18589874222566154928662005)
        ·
          refine ⟨1742800708365577024562063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18589874222566154928662005 1742800708365577024562063)
          ·
            refine ⟨2614201062548365536843095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1742800708365577024562063 2614201062548365536843095)
            ·
              refine ⟨3921301593822548305264643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2614201062548365536843095 3921301593822548305264643)
              ·
                refine ⟨5881952390733822457896965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3921301593822548305264643 5881952390733822457896965)
                ·
                  refine ⟨1102866073262591710855681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5881952390733822457896965 1102866073262591710855681)
                  ·
                    refine ⟨827149554946943783141761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1102866073262591710855681 827149554946943783141761)
                    ·
                      refine ⟨620362166210207837356321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 827149554946943783141761 620362166210207837356321)
                      ·
                        rfl

theorem cell23_1208151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_1208151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208151 prefixEnd_1208151 := by exact prefixLift 1208151
  have htrace : WordTrace (prefixWord ++ tailWord_1208151) baseStart_1208151 baseEnd_1208151 := by
    simpa [prefixWord, tailWord_1208151, baseEnd_1208151] using wordTrace_append hprefix tailTrace_1208151
  have hstable : (prefixWord ++ tailWord_1208151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208151).length < 2 ^ (prefixWord ++ tailWord_1208151).sum := by decide
  have hdescent : baseEnd_1208151 < baseStart_1208151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208167 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_1208167 : Nat := 118140960795 + 1208167 * 2 ^ 59
def prefixEnd_1208167 : Nat := 4983230072969 + 3 ^ 40 * 1208167 * 2
def baseEnd_1208167 : Nat := 620370381900679774756247

theorem tailTrace_1208167 : CollatzResearch.WordTrace tailWord_1208167 prefixEnd_1208167 620370381900679774756247 := by
  unfold tailWord_1208167
  simp only [CollatzResearch.WordTrace]
  refine ⟨44065470614024772341262755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29376980409349848227508503 44065470614024772341262755)
  ·
    refine ⟨66098205921037158511894133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44065470614024772341262755 66098205921037158511894133)
    ·
      refine ⟨6196706805097233610490075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66098205921037158511894133 6196706805097233610490075)
      ·
        refine ⟨9295060207645850415735113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6196706805097233610490075 9295060207645850415735113)
        ·
          refine ⟨6971295155734387811801335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9295060207645850415735113 6971295155734387811801335)
          ·
            refine ⟨10456942733601581717702003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6971295155734387811801335 10456942733601581717702003)
            ·
              refine ⟨15685414100402372576553005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10456942733601581717702003 15685414100402372576553005)
              ·
                refine ⟨5882030287650889716207377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15685414100402372576553005 5882030287650889716207377)
                ·
                  refine ⟨4411522715738167287155533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5882030287650889716207377 4411522715738167287155533)
                  ·
                    refine ⟨1654321018401812732683325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4411522715738167287155533 1654321018401812732683325)
                    ·
                      refine ⟨620370381900679774756247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1654321018401812732683325 620370381900679774756247)
                      ·
                        rfl

theorem cell23_1208167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_1208167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208167 prefixEnd_1208167 := by exact prefixLift 1208167
  have htrace : WordTrace (prefixWord ++ tailWord_1208167) baseStart_1208167 baseEnd_1208167 := by
    simpa [prefixWord, tailWord_1208167, baseEnd_1208167] using wordTrace_append hprefix tailTrace_1208167
  have hstable : (prefixWord ++ tailWord_1208167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208167).length < 2 ^ (prefixWord ++ tailWord_1208167).sum := by decide
  have hdescent : baseEnd_1208167 < baseStart_1208167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208168 : List Nat := [2, 1, 4, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_1208168 : Nat := 118140960795 + 1208168 * 2 ^ 59
def prefixEnd_1208168 : Nat := 4983230072969 + 3 ^ 40 * 1208168 * 2
def baseEnd_1208168 : Nat := 620370895381334270843743

theorem tailTrace_1208168 : CollatzResearch.WordTrace tailWord_1208168 prefixEnd_1208168 620370895381334270843743 := by
  unfold tailWord_1208168
  simp only [CollatzResearch.WordTrace]
  refine ⟨22032753543510574756024579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29377004724680766341366105 22032753543510574756024579)
  ·
    refine ⟨33049130315265862134036869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22032753543510574756024579 33049130315265862134036869)
    ·
      refine ⟨6196711934112349150131913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33049130315265862134036869 6196711934112349150131913)
      ·
        refine ⟨4647533950584261862598935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6196711934112349150131913 4647533950584261862598935)
        ·
          refine ⟨6971300925876392793898403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4647533950584261862598935 6971300925876392793898403)
          ·
            refine ⟨10456951388814589190847605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6971300925876392793898403 10456951388814589190847605)
            ·
              refine ⟨980339192701367736641963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10456951388814589190847605 980339192701367736641963)
              ·
                refine ⟨1470508789052051604962945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 980339192701367736641963 1470508789052051604962945)
                ·
                  refine ⟨1102881591789038703722209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1470508789052051604962945 1102881591789038703722209)
                  ·
                    refine ⟨827161193841779027791657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1102881591789038703722209 827161193841779027791657)
                    ·
                      refine ⟨620370895381334270843743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 827161193841779027791657 620370895381334270843743)
                      ·
                        rfl

theorem cell23_1208168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_1208168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208168 prefixEnd_1208168 := by exact prefixLift 1208168
  have htrace : WordTrace (prefixWord ++ tailWord_1208168) baseStart_1208168 baseEnd_1208168 := by
    simpa [prefixWord, tailWord_1208168, baseEnd_1208168] using wordTrace_append hprefix tailTrace_1208168
  have hstable : (prefixWord ++ tailWord_1208168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208168).length < 2 ^ (prefixWord ++ tailWord_1208168).sum := by decide
  have hdescent : baseEnd_1208168 < baseStart_1208168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208227 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 3]
def baseStart_1208227 : Nat := 118140960795 + 1208227 * 2 ^ 59
def prefixEnd_1208227 : Nat := 4983230072969 + 3 ^ 40 * 1208227 * 2
def baseEnd_1208227 : Nat := 620401190739949540005971

theorem tailTrace_1208227 : CollatzResearch.WordTrace tailWord_1208227 prefixEnd_1208227 620401190739949540005971 := by
  unfold tailWord_1208227
  simp only [CollatzResearch.WordTrace]
  refine ⟨44067658993807402588446935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29378439329204935058964623 44067658993807402588446935)
  ·
    refine ⟨66101488490711103882670403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44067658993807402588446935 66101488490711103882670403)
    ·
      refine ⟨99152232736066655824005605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66101488490711103882670403 99152232736066655824005605)
      ·
        refine ⟨18591043638012497967001051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99152232736066655824005605 18591043638012497967001051)
        ·
          refine ⟨27886565457018746950501577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18591043638012497967001051 27886565457018746950501577)
          ·
            refine ⟨20914924092764060212876183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27886565457018746950501577 20914924092764060212876183)
            ·
              refine ⟨31372386139146090319314275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20914924092764060212876183 31372386139146090319314275)
              ·
                refine ⟨47058579208719135478971413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31372386139146090319314275 47058579208719135478971413)
                ·
                  refine ⟨2205870900408709475576785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47058579208719135478971413 2205870900408709475576785)
                  ·
                    refine ⟨1654403175306532106682589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2205870900408709475576785 1654403175306532106682589)
                    ·
                      refine ⟨620401190739949540005971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1654403175306532106682589 620401190739949540005971)
                      ·
                        rfl

theorem cell23_1208227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_1208227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208227 prefixEnd_1208227 := by exact prefixLift 1208227
  have htrace : WordTrace (prefixWord ++ tailWord_1208227) baseStart_1208227 baseEnd_1208227 := by
    simpa [prefixWord, tailWord_1208227, baseEnd_1208227] using wordTrace_append hprefix tailTrace_1208227
  have hstable : (prefixWord ++ tailWord_1208227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208227).length < 2 ^ (prefixWord ++ tailWord_1208227).sum := by decide
  have hdescent : baseEnd_1208227 < baseStart_1208227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208264 : List Nat := [2, 1, 3, 1, 4, 2, 2, 2, 6]
def baseStart_1208264 : Nat := 118140960795 + 1208264 * 2 ^ 59
def prefixEnd_1208264 : Nat := 4983230072969 + 3 ^ 40 * 1208264 * 2
def baseEnd_1208264 : Nat := 68935576613796210582589

theorem tailTrace_1208264 : CollatzResearch.WordTrace tailWord_1208264 prefixEnd_1208264 68935576613796210582589 := by
  unfold tailWord_1208264
  simp only [CollatzResearch.WordTrace]
  refine ⟨22034504247336678953771923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29379338996448905271695897 22034504247336678953771923)
  ·
    refine ⟨33051756371005018430657885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22034504247336678953771923 33051756371005018430657885)
    ·
      refine ⟨12394408639126881911496707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33051756371005018430657885 12394408639126881911496707)
      ·
        refine ⟨18591612958690322867245061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12394408639126881911496707 18591612958690322867245061)
        ·
          refine ⟨3485927429754435537608449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18591612958690322867245061 3485927429754435537608449)
          ·
            refine ⟨2614445572315826653206337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3485927429754435537608449 2614445572315826653206337)
            ·
              refine ⟨1960834179236869989904753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2614445572315826653206337 1960834179236869989904753)
              ·
                refine ⟨1470625634427652492428565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1960834179236869989904753 1470625634427652492428565)
                ·
                  refine ⟨68935576613796210582589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1470625634427652492428565 68935576613796210582589)
                  ·
                    rfl

theorem cell23_1208264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 6].length) (baseStart_1208264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208264 prefixEnd_1208264 := by exact prefixLift 1208264
  have htrace : WordTrace (prefixWord ++ tailWord_1208264) baseStart_1208264 baseEnd_1208264 := by
    simpa [prefixWord, tailWord_1208264, baseEnd_1208264] using wordTrace_append hprefix tailTrace_1208264
  have hstable : (prefixWord ++ tailWord_1208264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208264).length < 2 ^ (prefixWord ++ tailWord_1208264).sum := by decide
  have hdescent : baseEnd_1208264 < baseStart_1208264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208268 : List Nat := [2, 2, 1, 4, 1, 2, 4, 2, 1, 4]
def baseStart_1208268 : Nat := 118140960795 + 1208268 * 2 ^ 59
def prefixEnd_1208268 : Nat := 4983230072969 + 3 ^ 40 * 1208268 * 2
def baseEnd_1208268 : Nat := 206807414482261293197761

theorem tailTrace_1208268 : CollatzResearch.WordTrace tailWord_1208268 prefixEnd_1208268 206807414482261293197761 := by
  unfold tailWord_1208268
  simp only [CollatzResearch.WordTrace]
  refine ⟨22034577193329433295344729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29379436257772577727126305 22034577193329433295344729)
  ·
    refine ⟨16525932894997074971508547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22034577193329433295344729 16525932894997074971508547)
    ·
      refine ⟨24788899342495612457262821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16525932894997074971508547 24788899342495612457262821)
      ·
        refine ⟨4647918626717927335736779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24788899342495612457262821 4647918626717927335736779)
        ·
          refine ⟨6971877940076891003605169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4647918626717927335736779 6971877940076891003605169)
          ·
            refine ⟨5228908455057668252703877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6971877940076891003605169 5228908455057668252703877)
            ·
              refine ⟨980420335323312797381977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5228908455057668252703877 980420335323312797381977)
              ·
                refine ⟨735315251492484598036483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 980420335323312797381977 735315251492484598036483)
                ·
                  refine ⟨1102972877238726897054725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735315251492484598036483 1102972877238726897054725)
                  ·
                    refine ⟨206807414482261293197761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1102972877238726897054725 206807414482261293197761)
                    ·
                      rfl

theorem cell23_1208268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_1208268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208268 prefixEnd_1208268 := by exact prefixLift 1208268
  have htrace : WordTrace (prefixWord ++ tailWord_1208268) baseStart_1208268 baseEnd_1208268 := by
    simpa [prefixWord, tailWord_1208268, baseEnd_1208268] using wordTrace_append hprefix tailTrace_1208268
  have hstable : (prefixWord ++ tailWord_1208268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208268).length < 2 ^ (prefixWord ++ tailWord_1208268).sum := by decide
  have hdescent : baseEnd_1208268 < baseStart_1208268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208291 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 3, 1, 3]
def baseStart_1208291 : Nat := 118140960795 + 1208291 * 2 ^ 59
def prefixEnd_1208291 : Nat := 4983230072969 + 3 ^ 40 * 1208291 * 2
def baseEnd_1208291 : Nat := 620434053501837289605677

theorem tailTrace_1208291 : CollatzResearch.WordTrace tailWord_1208291 prefixEnd_1208291 620434053501837289605677 := by
  unfold tailWord_1208291
  simp only [CollatzResearch.WordTrace]
  refine ⟨44069993265575541518776727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29379995510383694345851151 44069993265575541518776727)
  ·
    refine ⟨66104989898363312278165091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44069993265575541518776727 66104989898363312278165091)
    ·
      refine ⟨99157484847544968417247637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66104989898363312278165091 99157484847544968417247637)
      ·
        refine ⟨4648007102228670394558483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99157484847544968417247637 4648007102228670394558483)
        ·
          refine ⟨6972010653343005591837725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4648007102228670394558483 6972010653343005591837725)
          ·
            refine ⟨2614503995003627096939147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6972010653343005591837725 2614503995003627096939147)
            ·
              refine ⟨3921755992505440645408721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2614503995003627096939147 3921755992505440645408721)
              ·
                refine ⟨2941316994379080484056541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3921755992505440645408721 2941316994379080484056541)
                ·
                  refine ⟨1102993872892155181521203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2941316994379080484056541 1102993872892155181521203)
                  ·
                    refine ⟨1654490809338232772281805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1102993872892155181521203 1654490809338232772281805)
                    ·
                      refine ⟨620434053501837289605677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1654490809338232772281805 620434053501837289605677)
                      ·
                        rfl

theorem cell23_1208291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_1208291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208291 prefixEnd_1208291 := by exact prefixLift 1208291
  have htrace : WordTrace (prefixWord ++ tailWord_1208291) baseStart_1208291 baseEnd_1208291 := by
    simpa [prefixWord, tailWord_1208291, baseEnd_1208291] using wordTrace_append hprefix tailTrace_1208291
  have hstable : (prefixWord ++ tailWord_1208291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208291).length < 2 ^ (prefixWord ++ tailWord_1208291).sum := by decide
  have hdescent : baseEnd_1208291 < baseStart_1208291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208334 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_1208334 : Nat := 118140960795 + 1208334 * 2 ^ 59
def prefixEnd_1208334 : Nat := 4983230072969 + 3 ^ 40 * 1208334 * 2
def baseEnd_1208334 : Nat := 620456133169980621367979

theorem tailTrace_1208334 : CollatzResearch.WordTrace tailWord_1208334 prefixEnd_1208334 620456133169980621367979 := by
  unfold tailWord_1208334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5508945200552469982824007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29381041069613173241728037 5508945200552469982824007)
  ·
    refine ⟨8263417800828704974236011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5508945200552469982824007 8263417800828704974236011)
    ·
      refine ⟨12395126701243057461354017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8263417800828704974236011 12395126701243057461354017)
      ·
        refine ⟨9296345025932293096015513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12395126701243057461354017 9296345025932293096015513)
        ·
          refine ⟨6972258769449219822011635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9296345025932293096015513 6972258769449219822011635)
          ·
            refine ⟨10458388154173829733017453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6972258769449219822011635 10458388154173829733017453)
            ·
              refine ⟨3921895557815186149881545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10458388154173829733017453 3921895557815186149881545)
              ·
                refine ⟨2941421668361389612411159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3921895557815186149881545 2941421668361389612411159)
                ·
                  refine ⟨4412132502542084418616739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2941421668361389612411159 4412132502542084418616739)
                  ·
                    refine ⟨6618198753813126627925109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4412132502542084418616739 6618198753813126627925109)
                    ·
                      refine ⟨620456133169980621367979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6618198753813126627925109 620456133169980621367979)
                      ·
                        rfl

theorem cell23_1208334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_1208334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208334 prefixEnd_1208334 := by exact prefixLift 1208334
  have htrace : WordTrace (prefixWord ++ tailWord_1208334) baseStart_1208334 baseEnd_1208334 := by
    simpa [prefixWord, tailWord_1208334, baseEnd_1208334] using wordTrace_append hprefix tailTrace_1208334
  have hstable : (prefixWord ++ tailWord_1208334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208334).length < 2 ^ (prefixWord ++ tailWord_1208334).sum := by decide
  have hdescent : baseEnd_1208334 < baseStart_1208334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208341 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 1, 6]
def baseStart_1208341 : Nat := 118140960795 + 1208341 * 2 ^ 59
def prefixEnd_1208341 : Nat := 4983230072969 + 3 ^ 40 * 1208341 * 2
def baseEnd_1208341 : Nat := 206819909178187364660149

theorem tailTrace_1208341 : CollatzResearch.WordTrace tailWord_1208341 prefixEnd_1208341 206819909178187364660149 := by
  unfold tailWord_1208341
  simp only [CollatzResearch.WordTrace]
  refine ⟨44071816915394400058096877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29381211276929600038731251 44071816915394400058096877)
  ·
    refine ⟨16526931343272900021786329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44071816915394400058096877 16526931343272900021786329)
    ·
      refine ⟨12395198507454675016339747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16526931343272900021786329 12395198507454675016339747)
      ·
        refine ⟨18592797761182012524509621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12395198507454675016339747 18592797761182012524509621)
        ·
          refine ⟨1743074790110813674172777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18592797761182012524509621 1743074790110813674172777)
          ·
            refine ⟨1307306092583110255629583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1743074790110813674172777 1307306092583110255629583)
            ·
              refine ⟨1960959138874665383444375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307306092583110255629583 1960959138874665383444375)
              ·
                refine ⟨2941438708311998075166563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960959138874665383444375 2941438708311998075166563)
                ·
                  refine ⟨4412158062467997112749845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2941438708311998075166563 4412158062467997112749845)
                  ·
                    refine ⟨206819909178187364660149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4412158062467997112749845 206819909178187364660149)
                    ·
                      rfl

theorem cell23_1208341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_1208341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208341 prefixEnd_1208341 := by exact prefixLift 1208341
  have htrace : WordTrace (prefixWord ++ tailWord_1208341) baseStart_1208341 baseEnd_1208341 := by
    simpa [prefixWord, tailWord_1208341, baseEnd_1208341] using wordTrace_append hprefix tailTrace_1208341
  have hstable : (prefixWord ++ tailWord_1208341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208341).length < 2 ^ (prefixWord ++ tailWord_1208341).sum := by decide
  have hdescent : baseEnd_1208341 < baseStart_1208341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208348 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_1208348 : Nat := 118140960795 + 1208348 * 2 ^ 59
def prefixEnd_1208348 : Nat := 4983230072969 + 3 ^ 40 * 1208348 * 2
def baseEnd_1208348 : Nat := 620463321899143566592915

theorem tailTrace_1208348 : CollatzResearch.WordTrace tailWord_1208348 prefixEnd_1208348 620463321899143566592915 := by
  unfold tailWord_1208348
  simp only [CollatzResearch.WordTrace]
  refine ⟨22036036113184520126800849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29381381484246026835734465 22036036113184520126800849)
  ·
    refine ⟨16527027084888390095100637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22036036113184520126800849 16527027084888390095100637)
    ·
      refine ⟨6197635156833146285662739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16527027084888390095100637 6197635156833146285662739)
      ·
        refine ⟨9296452735249719428494109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6197635156833146285662739 9296452735249719428494109)
        ·
          refine ⟨3486169775718644785685291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9296452735249719428494109 3486169775718644785685291)
          ·
            refine ⟨5229254663577967178527937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3486169775718644785685291 5229254663577967178527937)
            ·
              refine ⟨3921940997683475383895953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5229254663577967178527937 3921940997683475383895953)
              ·
                refine ⟨2941455748262606537921965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3921940997683475383895953 2941455748262606537921965)
                ·
                  refine ⟨1103045905598477451720737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2941455748262606537921965 1103045905598477451720737)
                  ·
                    refine ⟨827284429198858088790553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1103045905598477451720737 827284429198858088790553)
                    ·
                      refine ⟨620463321899143566592915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 827284429198858088790553 620463321899143566592915)
                      ·
                        rfl

theorem cell23_1208348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_1208348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208348 prefixEnd_1208348 := by exact prefixLift 1208348
  have htrace : WordTrace (prefixWord ++ tailWord_1208348) baseStart_1208348 baseEnd_1208348 := by
    simpa [prefixWord, tailWord_1208348, baseEnd_1208348] using wordTrace_append hprefix tailTrace_1208348
  have hstable : (prefixWord ++ tailWord_1208348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208348).length < 2 ^ (prefixWord ++ tailWord_1208348).sum := by decide
  have hdescent : baseEnd_1208348 < baseStart_1208348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208351 : List Nat := [1, 1, 2, 4, 1, 2, 4, 2, 1, 2, 3]
def baseStart_1208351 : Nat := 118140960795 + 1208351 * 2 ^ 59
def prefixEnd_1208351 : Nat := 4983230072969 + 3 ^ 40 * 1208351 * 2
def baseEnd_1208351 : Nat := 620464862341107054855401

theorem tailTrace_1208351 : CollatzResearch.WordTrace tailWord_1208351 prefixEnd_1208351 620464862341107054855401 := by
  unfold tailWord_1208351
  simp only [CollatzResearch.WordTrace]
  refine ⟨44072181645358171765960907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29381454430238781177307271 44072181645358171765960907)
  ·
    refine ⟨66108272468037257648941361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44072181645358171765960907 66108272468037257648941361)
    ·
      refine ⟨49581204351027943236706021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66108272468037257648941361 49581204351027943236706021)
      ·
        refine ⟨9296475815817739356882379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49581204351027943236706021 9296475815817739356882379)
        ·
          refine ⟨13944713723726609035323569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9296475815817739356882379 13944713723726609035323569)
          ·
            refine ⟨10458535292794956776492677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13944713723726609035323569 10458535292794956776492677)
            ·
              refine ⟨1960975367399054395592377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10458535292794956776492677 1960975367399054395592377)
              ·
                refine ⟨1470731525549290796694283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1960975367399054395592377 1470731525549290796694283)
                ·
                  refine ⟨2206097288323936195041425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1470731525549290796694283 2206097288323936195041425)
                  ·
                    refine ⟨1654572966242952146281069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2206097288323936195041425 1654572966242952146281069)
                    ·
                      refine ⟨620464862341107054855401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1654572966242952146281069 620464862341107054855401)
                      ·
                        rfl

theorem cell23_1208351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_1208351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208351 prefixEnd_1208351 := by exact prefixLift 1208351
  have htrace : WordTrace (prefixWord ++ tailWord_1208351) baseStart_1208351 baseEnd_1208351 := by
    simpa [prefixWord, tailWord_1208351, baseEnd_1208351] using wordTrace_append hprefix tailTrace_1208351
  have hstable : (prefixWord ++ tailWord_1208351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208351).length < 2 ^ (prefixWord ++ tailWord_1208351).sum := by decide
  have hdescent : baseEnd_1208351 < baseStart_1208351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208359 : List Nat := [1, 1, 7, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_1208359 : Nat := 118140960795 + 1208359 * 2 ^ 59
def prefixEnd_1208359 : Nat := 4983230072969 + 3 ^ 40 * 1208359 * 2
def baseEnd_1208359 : Nat := 620468970186343023555365

theorem tailTrace_1208359 : CollatzResearch.WordTrace tailWord_1208359 prefixEnd_1208359 620468970186343023555365 := by
  unfold tailWord_1208359
  simp only [CollatzResearch.WordTrace]
  refine ⟨44072473429329189132252131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29381648952886126088168087 44072473429329189132252131)
  ·
    refine ⟨66108710143993783698378197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44072473429329189132252131 66108710143993783698378197)
    ·
      refine ⟨1549422893999854305430739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 66108710143993783698378197 1549422893999854305430739)
      ·
        refine ⟨2324134340999781458146109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1549422893999854305430739 2324134340999781458146109)
        ·
          refine ⟨871550377874918046804791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2324134340999781458146109 871550377874918046804791)
          ·
            refine ⟨1307325566812377070207187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871550377874918046804791 1307325566812377070207187)
            ·
              refine ⟨1960988350218565605310781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307325566812377070207187 1960988350218565605310781)
              ·
                refine ⟨735370631331962101991543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1960988350218565605310781 735370631331962101991543)
                ·
                  refine ⟨1103055946997943152987315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735370631331962101991543 1103055946997943152987315)
                  ·
                    refine ⟨1654583920496914729480973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1103055946997943152987315 1654583920496914729480973)
                    ·
                      refine ⟨620468970186343023555365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1654583920496914729480973 620468970186343023555365)
                      ·
                        rfl

theorem cell23_1208359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_1208359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208359 prefixEnd_1208359 := by exact prefixLift 1208359
  have htrace : WordTrace (prefixWord ++ tailWord_1208359) baseStart_1208359 baseEnd_1208359 := by
    simpa [prefixWord, tailWord_1208359, baseEnd_1208359] using wordTrace_append hprefix tailTrace_1208359
  have hstable : (prefixWord ++ tailWord_1208359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208359).length < 2 ^ (prefixWord ++ tailWord_1208359).sum := by decide
  have hdescent : baseEnd_1208359 < baseStart_1208359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208381 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 4, 1, 3]
def baseStart_1208381 : Nat := 118140960795 + 1208381 * 2 ^ 59
def prefixEnd_1208381 : Nat := 4983230072969 + 3 ^ 40 * 1208381 * 2
def baseEnd_1208381 : Nat := 620480266760741937480263

theorem tailTrace_1208381 : CollatzResearch.WordTrace tailWord_1208381 prefixEnd_1208381 620480266760741937480263 := by
  unfold tailWord_1208381
  simp only [CollatzResearch.WordTrace]
  refine ⟨44073275835249486889552997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29382183890166324593035331 44073275835249486889552997)
  ·
    refine ⟨8263739219109278791791187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44073275835249486889552997 8263739219109278791791187)
    ·
      refine ⟨12395608828663918187686781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8263739219109278791791187 12395608828663918187686781)
      ·
        refine ⟨4648353310748969320382543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12395608828663918187686781 4648353310748969320382543)
        ·
          refine ⟨6972529966123453980573815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4648353310748969320382543 6972529966123453980573815)
          ·
            refine ⟨10458794949185180970860723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6972529966123453980573815 10458794949185180970860723)
            ·
              refine ⟨15688192423777771456291085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10458794949185180970860723 15688192423777771456291085)
              ·
                refine ⟨5883072158916664296109157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15688192423777771456291085 5883072158916664296109157)
                ·
                  refine ⟨1103076029796874555520467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5883072158916664296109157 1103076029796874555520467)
                  ·
                    refine ⟨1654614044695311833280701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1103076029796874555520467 1654614044695311833280701)
                    ·
                      refine ⟨620480266760741937480263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1654614044695311833280701 620480266760741937480263)
                      ·
                        rfl

theorem cell23_1208381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_1208381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208381 prefixEnd_1208381 := by exact prefixLift 1208381
  have htrace : WordTrace (prefixWord ++ tailWord_1208381) baseStart_1208381 baseEnd_1208381 := by
    simpa [prefixWord, tailWord_1208381, baseEnd_1208381] using wordTrace_append hprefix tailTrace_1208381
  have hstable : (prefixWord ++ tailWord_1208381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208381).length < 2 ^ (prefixWord ++ tailWord_1208381).sum := by decide
  have hdescent : baseEnd_1208381 < baseStart_1208381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208382 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_1208382 : Nat := 118140960795 + 1208382 * 2 ^ 59
def prefixEnd_1208382 : Nat := 4983230072969 + 3 ^ 40 * 1208382 * 2
def baseEnd_1208382 : Nat := 620480780241396433567759

theorem tailTrace_1208382 : CollatzResearch.WordTrace tailWord_1208382 prefixEnd_1208382 620480780241396433567759 := by
  unfold tailWord_1208382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5509164038530733007542425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29382208205497242706892933 5509164038530733007542425)
  ·
    refine ⟨4131873028898049755656819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5509164038530733007542425 4131873028898049755656819)
    ·
      refine ⟨6197809543347074633485229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4131873028898049755656819 6197809543347074633485229)
      ·
        refine ⟨2324178578755152987556961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6197809543347074633485229 2324178578755152987556961)
        ·
          refine ⟨1743133934066364740667721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2324178578755152987556961 1743133934066364740667721)
          ·
            refine ⟨1307350450549773555500791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1743133934066364740667721 1307350450549773555500791)
            ·
              refine ⟨1961025675824660333251187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307350450549773555500791 1961025675824660333251187)
              ·
                refine ⟨2941538513736990499876781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1961025675824660333251187 2941538513736990499876781)
                ·
                  refine ⟨1103076942651371437453793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2941538513736990499876781 1103076942651371437453793)
                  ·
                    refine ⟨827307706988528578090345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1103076942651371437453793 827307706988528578090345)
                    ·
                      refine ⟨620480780241396433567759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 827307706988528578090345 620480780241396433567759)
                      ·
                        rfl

theorem cell23_1208382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_1208382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208382 prefixEnd_1208382 := by exact prefixLift 1208382
  have htrace : WordTrace (prefixWord ++ tailWord_1208382) baseStart_1208382 baseEnd_1208382 := by
    simpa [prefixWord, tailWord_1208382, baseEnd_1208382] using wordTrace_append hprefix tailTrace_1208382
  have hstable : (prefixWord ++ tailWord_1208382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208382).length < 2 ^ (prefixWord ++ tailWord_1208382).sum := by decide
  have hdescent : baseEnd_1208382 < baseStart_1208382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208391 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 3, 3, 2]
def baseStart_1208391 : Nat := 118140960795 + 1208391 * 2 ^ 59
def prefixEnd_1208391 : Nat := 4983230072969 + 3 ^ 40 * 1208391 * 2
def baseEnd_1208391 : Nat := 620485401567286898355217

theorem tailTrace_1208391 : CollatzResearch.WordTrace tailWord_1208391 prefixEnd_1208391 620485401567286898355217 := by
  unfold tailWord_1208391
  simp only [CollatzResearch.WordTrace]
  refine ⟨44073640565213258597417027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29382427043475505731611351 44073640565213258597417027)
  ·
    refine ⟨66110460847819887896125541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44073640565213258597417027 66110460847819887896125541)
    ·
      refine ⟨12395711408966228980523539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66110460847819887896125541 12395711408966228980523539)
      ·
        refine ⟨18593567113449343470785309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12395711408966228980523539 18593567113449343470785309)
        ·
          refine ⟨6972587667543503801544491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18593567113449343470785309 6972587667543503801544491)
          ·
            refine ⟨10458881501315255702316737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6972587667543503801544491 10458881501315255702316737)
            ·
              refine ⟨7844161125986441776737553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10458881501315255702316737 7844161125986441776737553)
              ·
                refine ⟨5883120844489831332553165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7844161125986441776737553 5883120844489831332553165)
                ·
                  refine ⟨2206170316683686749707437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5883120844489831332553165 2206170316683686749707437)
                  ·
                    refine ⟨827313868756382531140289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2206170316683686749707437 827313868756382531140289)
                    ·
                      refine ⟨620485401567286898355217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 827313868756382531140289 620485401567286898355217)
                      ·
                        rfl

theorem cell23_1208391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_1208391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208391 prefixEnd_1208391 := by exact prefixLift 1208391
  have htrace : WordTrace (prefixWord ++ tailWord_1208391) baseStart_1208391 baseEnd_1208391 := by
    simpa [prefixWord, tailWord_1208391, baseEnd_1208391] using wordTrace_append hprefix tailTrace_1208391
  have hstable : (prefixWord ++ tailWord_1208391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208391).length < 2 ^ (prefixWord ++ tailWord_1208391).sum := by decide
  have hdescent : baseEnd_1208391 < baseStart_1208391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208398 : List Nat := [4, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3]
def baseStart_1208398 : Nat := 118140960795 + 1208398 * 2 ^ 59
def prefixEnd_1208398 : Nat := 4983230072969 + 3 ^ 40 * 1208398 * 2
def baseEnd_1208398 : Nat := 620488995931868370967685

theorem tailTrace_1208398 : CollatzResearch.WordTrace tailWord_1208398 prefixEnd_1208398 620488995931868370967685 := by
  unfold tailWord_1208398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5509236984523487349115231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29382597250791932528614565 5509236984523487349115231)
  ·
    refine ⟨8263855476785231023672847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5509236984523487349115231 8263855476785231023672847)
    ·
      refine ⟨12395783215177846535509271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8263855476785231023672847 12395783215177846535509271)
      ·
        refine ⟨18593674822766769803263907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12395783215177846535509271 18593674822766769803263907)
        ·
          refine ⟨27890512234150154704895861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18593674822766769803263907 27890512234150154704895861)
          ·
            refine ⟨2614735521951577003583987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27890512234150154704895861 2614735521951577003583987)
            ·
              refine ⟨3922103282927365505375981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2614735521951577003583987 3922103282927365505375981)
              ·
                refine ⟨1470788731097762064515993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3922103282927365505375981 1470788731097762064515993)
                ·
                  refine ⟨1103091548323321548386995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1470788731097762064515993 1103091548323321548386995)
                  ·
                    refine ⟨1654637322484982322580493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1103091548323321548386995 1654637322484982322580493)
                    ·
                      refine ⟨620488995931868370967685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1654637322484982322580493 620488995931868370967685)
                      ·
                        rfl

theorem cell23_1208398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_1208398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208398 prefixEnd_1208398 := by exact prefixLift 1208398
  have htrace : WordTrace (prefixWord ++ tailWord_1208398) baseStart_1208398 baseEnd_1208398 := by
    simpa [prefixWord, tailWord_1208398, baseEnd_1208398] using wordTrace_append hprefix tailTrace_1208398
  have hstable : (prefixWord ++ tailWord_1208398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208398).length < 2 ^ (prefixWord ++ tailWord_1208398).sum := by decide
  have hdescent : baseEnd_1208398 < baseStart_1208398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208408 : List Nat := [2, 1, 2, 2, 1, 4, 3, 2, 1, 3, 2]
def baseStart_1208408 : Nat := 118140960795 + 1208408 * 2 ^ 59
def prefixEnd_1208408 : Nat := 4983230072969 + 3 ^ 40 * 1208408 * 2
def baseEnd_1208408 : Nat := 620494130738413331842639

theorem tailTrace_1208408 : CollatzResearch.WordTrace tailWord_1208408 prefixEnd_1208408 620494130738413331842639 := by
  unfold tailWord_1208408
  simp only [CollatzResearch.WordTrace]
  refine ⟨22037130303075835250392939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29382840404101113667190585 22037130303075835250392939)
  ·
    refine ⟨33055695454613752875589409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22037130303075835250392939 33055695454613752875589409)
    ·
      refine ⟨24791771590960314656692057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33055695454613752875589409 24791771590960314656692057)
      ·
        refine ⟨18593828693220235992519043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24791771590960314656692057 18593828693220235992519043)
        ·
          refine ⟨27890743039830353988778565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18593828693220235992519043 27890743039830353988778565)
          ·
            refine ⟨5229514319968191372895981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27890743039830353988778565 5229514319968191372895981)
            ·
              refine ⟨1961067869988071764835993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5229514319968191372895981 1961067869988071764835993)
              ·
                refine ⟨1470800902491053823626995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1961067869988071764835993 1470800902491053823626995)
                ·
                  refine ⟨2206201353736580735440493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1470800902491053823626995 2206201353736580735440493)
                  ·
                    refine ⟨827325507651217775790185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2206201353736580735440493 827325507651217775790185)
                    ·
                      refine ⟨620494130738413331842639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 827325507651217775790185 620494130738413331842639)
                      ·
                        rfl

theorem cell23_1208408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_1208408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208408 prefixEnd_1208408 := by exact prefixLift 1208408
  have htrace : WordTrace (prefixWord ++ tailWord_1208408) baseStart_1208408 baseEnd_1208408 := by
    simpa [prefixWord, tailWord_1208408, baseEnd_1208408] using wordTrace_append hprefix tailTrace_1208408
  have hstable : (prefixWord ++ tailWord_1208408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208408).length < 2 ^ (prefixWord ++ tailWord_1208408).sum := by decide
  have hdescent : baseEnd_1208408 < baseStart_1208408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208421 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 3, 4, 2]
def baseStart_1208421 : Nat := 118140960795 + 1208421 * 2 ^ 59
def prefixEnd_1208421 : Nat := 4983230072969 + 3 ^ 40 * 1208421 * 2
def baseEnd_1208421 : Nat := 620500805986921780980079

theorem tailTrace_1208421 : CollatzResearch.WordTrace tailWord_1208421 prefixEnd_1208421 620500805986921780980079 := by
  unfold tailWord_1208421
  simp only [CollatzResearch.WordTrace]
  refine ⟨44074734755104573721009117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29383156503403049147339411 44074734755104573721009117)
  ·
    refine ⟨16528025533164215145378419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44074734755104573721009117 16528025533164215145378419)
    ·
      refine ⟨24792038299746322718067629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16528025533164215145378419 24792038299746322718067629)
      ·
        refine ⟨9297014362404871019275361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24792038299746322718067629 9297014362404871019275361)
        ·
          refine ⟨6972760771803653264456521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9297014362404871019275361 6972760771803653264456521)
          ·
            refine ⟨5229570578852739948342391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6972760771803653264456521 5229570578852739948342391)
            ·
              refine ⟨7844355868279109922513587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5229570578852739948342391 7844355868279109922513587)
              ·
                refine ⟨11766533802418664883770381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7844355868279109922513587 11766533802418664883770381)
                ·
                  refine ⟨4412450175906999331413893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11766533802418664883770381 4412450175906999331413893)
                  ·
                    refine ⟨827334407982562374640105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4412450175906999331413893 827334407982562374640105)
                    ·
                      refine ⟨620500805986921780980079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 827334407982562374640105 620500805986921780980079)
                      ·
                        rfl

theorem cell23_1208421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_1208421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208421 prefixEnd_1208421 := by exact prefixLift 1208421
  have htrace : WordTrace (prefixWord ++ tailWord_1208421) baseStart_1208421 baseEnd_1208421 := by
    simpa [prefixWord, tailWord_1208421, baseEnd_1208421] using wordTrace_append hprefix tailTrace_1208421
  have hstable : (prefixWord ++ tailWord_1208421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208421).length < 2 ^ (prefixWord ++ tailWord_1208421).sum := by decide
  have hdescent : baseEnd_1208421 < baseStart_1208421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208551 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 8]
def baseStart_1208551 : Nat := 118140960795 + 1208551 * 2 ^ 59
def prefixEnd_1208551 : Nat := 4983230072969 + 3 ^ 40 * 1208551 * 2
def baseEnd_1208551 : Nat := 68951950941334030261609

theorem tailTrace_1208551 : CollatzResearch.WordTrace tailWord_1208551 prefixEnd_1208551 68951950941334030261609 := by
  unfold tailWord_1208551
  simp only [CollatzResearch.WordTrace]
  refine ⟨44079476244633605923241507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29386317496422403948827671 44079476244633605923241507)
  ·
    refine ⟨66119214366950408884862261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44079476244633605923241507 66119214366950408884862261)
    ·
      refine ⟨6198676346901600832955837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66119214366950408884862261 6198676346901600832955837)
      ·
        refine ⟨2324503630088100312358439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6198676346901600832955837 2324503630088100312358439)
        ·
          refine ⟨3486755445132150468537659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324503630088100312358439 3486755445132150468537659)
          ·
            refine ⟨5230133167698225702806489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3486755445132150468537659 5230133167698225702806489)
            ·
              refine ⟨3922599875773669277104867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5230133167698225702806489 3922599875773669277104867)
              ·
                refine ⟨5883899813660503915657301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3922599875773669277104867 5883899813660503915657301)
                ·
                  refine ⟨68951950941334030261609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5883899813660503915657301 68951950941334030261609)
                  ·
                    rfl

theorem cell23_1208551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 8].length) (baseStart_1208551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208551 prefixEnd_1208551 := by exact prefixLift 1208551
  have htrace : WordTrace (prefixWord ++ tailWord_1208551) baseStart_1208551 baseEnd_1208551 := by
    simpa [prefixWord, tailWord_1208551, baseEnd_1208551] using wordTrace_append hprefix tailTrace_1208551
  have hstable : (prefixWord ++ tailWord_1208551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208551).length < 2 ^ (prefixWord ++ tailWord_1208551).sum := by decide
  have hdescent : baseEnd_1208551 < baseStart_1208551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208555 : List Nat := [1, 1, 1, 1, 2, 5, 5, 2, 1, 4]
def baseStart_1208555 : Nat := 118140960795 + 1208555 * 2 ^ 59
def prefixEnd_1208555 : Nat := 4983230072969 + 3 ^ 40 * 1208555 * 2
def baseEnd_1208555 : Nat := 206856537464874752234821

theorem tailTrace_1208555 : CollatzResearch.WordTrace tailWord_1208555 prefixEnd_1208555 206856537464874752234821 := by
  unfold tailWord_1208555
  simp only [CollatzResearch.WordTrace]
  refine ⟨44079622136619114606387119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29386414757746076404258079 44079622136619114606387119)
  ·
    refine ⟨66119433204928671909580679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44079622136619114606387119 66119433204928671909580679)
    ·
      refine ⟨99179149807393007864371019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66119433204928671909580679 99179149807393007864371019)
      ·
        refine ⟨148768724711089511796556529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99179149807393007864371019 148768724711089511796556529)
        ·
          refine ⟨111576543533317133847417397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148768724711089511796556529 111576543533317133847417397)
          ·
            refine ⟨10460300956248481298195381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111576543533317133847417397 10460300956248481298195381)
            ·
              refine ⟨980653214648295121705817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10460300956248481298195381 980653214648295121705817)
              ·
                refine ⟨735489910986221341279363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 980653214648295121705817 735489910986221341279363)
                ·
                  refine ⟨1103234866479332011919045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735489910986221341279363 1103234866479332011919045)
                  ·
                    refine ⟨206856537464874752234821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1103234866479332011919045 206856537464874752234821)
                    ·
                      rfl

theorem cell23_1208555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 1, 4].length) (baseStart_1208555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208555 prefixEnd_1208555 := by exact prefixLift 1208555
  have htrace : WordTrace (prefixWord ++ tailWord_1208555) baseStart_1208555 baseEnd_1208555 := by
    simpa [prefixWord, tailWord_1208555, baseEnd_1208555] using wordTrace_append hprefix tailTrace_1208555
  have hstable : (prefixWord ++ tailWord_1208555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208555).length < 2 ^ (prefixWord ++ tailWord_1208555).sum := by decide
  have hdescent : baseEnd_1208555 < baseStart_1208555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208581 : List Nat := [1, 3, 1, 1, 2, 1, 2, 6, 1, 5]
def baseStart_1208581 : Nat := 118140960795 + 1208581 * 2 ^ 59
def prefixEnd_1208581 : Nat := 4983230072969 + 3 ^ 40 * 1208581 * 2
def baseEnd_1208581 : Nat := 206860987630547051659781

theorem tailTrace_1208581 : CollatzResearch.WordTrace tailWord_1208581 prefixEnd_1208581 206860987630547051659781 := by
  unfold tailWord_1208581
  simp only [CollatzResearch.WordTrace]
  refine ⟨44080570434524921046833597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29387046956349947364555731 44080570434524921046833597)
  ·
    refine ⟨16530213912946845392562599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44080570434524921046833597 16530213912946845392562599)
    ·
      refine ⟨24795320869420268088843899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16530213912946845392562599 24795320869420268088843899)
      ·
        refine ⟨37192981304130402133265849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24795320869420268088843899 37192981304130402133265849)
        ·
          refine ⟨27894735978097801599949387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37192981304130402133265849 27894735978097801599949387)
          ·
            refine ⟨41842103967146702399924081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27894735978097801599949387 41842103967146702399924081)
            ·
              refine ⟨31381577975360026799943061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41842103967146702399924081 31381577975360026799943061)
              ·
                refine ⟨1471011467595001256247331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31381577975360026799943061 1471011467595001256247331)
                ·
                  refine ⟨2206517201392501884370997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471011467595001256247331 2206517201392501884370997)
                  ·
                    refine ⟨206860987630547051659781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2206517201392501884370997 206860987630547051659781)
                    ·
                      rfl

theorem cell23_1208581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_1208581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208581 prefixEnd_1208581 := by exact prefixLift 1208581
  have htrace : WordTrace (prefixWord ++ tailWord_1208581) baseStart_1208581 baseEnd_1208581 := by
    simpa [prefixWord, tailWord_1208581, baseEnd_1208581] using wordTrace_append hprefix tailTrace_1208581
  have hstable : (prefixWord ++ tailWord_1208581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208581).length < 2 ^ (prefixWord ++ tailWord_1208581).sum := by decide
  have hdescent : baseEnd_1208581 < baseStart_1208581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208606 : List Nat := [4, 3, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1208606 : Nat := 118140960795 + 1208606 * 2 ^ 59
def prefixEnd_1208606 : Nat := 4983230072969 + 3 ^ 40 * 1208606 * 2
def baseEnd_1208606 : Nat := 206865266636001185722243

theorem tailTrace_1208606 : CollatzResearch.WordTrace tailWord_1208606 prefixEnd_1208606 206865266636001185722243 := by
  unfold tailWord_1208606
  simp only [CollatzResearch.WordTrace]
  refine ⟨5510185282429293789561709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29387654839622900210995781 5510185282429293789561709)
  ·
    refine ⟨2066319480910985171085641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5510185282429293789561709 2066319480910985171085641)
    ·
      refine ⟨1549739610683238878314231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2066319480910985171085641 1549739610683238878314231)
      ·
        refine ⟨2324609416024858317471347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1549739610683238878314231 2324609416024858317471347)
        ·
          refine ⟨3486914124037287476207021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324609416024858317471347 3486914124037287476207021)
          ·
            refine ⟨1307592796513982803577633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3486914124037287476207021 1307592796513982803577633)
            ·
              refine ⟨980694597385487102683225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1307592796513982803577633 980694597385487102683225)
              ·
                refine ⟨735520948039115327012419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 980694597385487102683225 735520948039115327012419)
                ·
                  refine ⟨1103281422058672990518629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735520948039115327012419 1103281422058672990518629)
                  ·
                    refine ⟨206865266636001185722243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1103281422058672990518629 206865266636001185722243)
                    ·
                      rfl

theorem cell23_1208606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1208606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208606 prefixEnd_1208606 := by exact prefixLift 1208606
  have htrace : WordTrace (prefixWord ++ tailWord_1208606) baseStart_1208606 baseEnd_1208606 := by
    simpa [prefixWord, tailWord_1208606, baseEnd_1208606] using wordTrace_append hprefix tailTrace_1208606
  have hstable : (prefixWord ++ tailWord_1208606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208606).length < 2 ^ (prefixWord ++ tailWord_1208606).sum := by decide
  have hdescent : baseEnd_1208606 < baseStart_1208606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208612 : List Nat := [2, 3, 1, 3, 1, 3, 1, 4, 1, 1, 3]
def baseStart_1208612 : Nat := 118140960795 + 1208612 * 2 ^ 59
def prefixEnd_1208612 : Nat := 4983230072969 + 3 ^ 40 * 1208612 * 2
def baseEnd_1208612 : Nat := 620598880791930533691701

theorem tailTrace_1208612 : CollatzResearch.WordTrace tailWord_1208612 prefixEnd_1208612 620598880791930533691701 := by
  unfold tailWord_1208612
  simp only [CollatzResearch.WordTrace]
  refine ⟨22040850548706306670606045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29387800731608408894141393 22040850548706306670606045)
  ·
    refine ⟨8265318955764865001477267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22040850548706306670606045 8265318955764865001477267)
    ·
      refine ⟨12397978433647297502215901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8265318955764865001477267 12397978433647297502215901)
      ·
        refine ⟨4649241912617736563330963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12397978433647297502215901 4649241912617736563330963)
        ·
          refine ⟨6973862868926604844996445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4649241912617736563330963 6973862868926604844996445)
          ·
            refine ⟨2615198575847476816873667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6973862868926604844996445 2615198575847476816873667)
            ·
              refine ⟨3922797863771215225310501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615198575847476816873667 3922797863771215225310501)
              ·
                refine ⟨735524599457102854745719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3922797863771215225310501 735524599457102854745719)
                ·
                  refine ⟨1103286899185654282118579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735524599457102854745719 1103286899185654282118579)
                  ·
                    refine ⟨1654930348778481423177869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1103286899185654282118579 1654930348778481423177869)
                    ·
                      refine ⟨620598880791930533691701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1654930348778481423177869 620598880791930533691701)
                      ·
                        rfl

theorem cell23_1208612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_1208612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208612 prefixEnd_1208612 := by exact prefixLift 1208612
  have htrace : WordTrace (prefixWord ++ tailWord_1208612) baseStart_1208612 baseEnd_1208612 := by
    simpa [prefixWord, tailWord_1208612, baseEnd_1208612] using wordTrace_append hprefix tailTrace_1208612
  have hstable : (prefixWord ++ tailWord_1208612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208612).length < 2 ^ (prefixWord ++ tailWord_1208612).sum := by decide
  have hdescent : baseEnd_1208612 < baseStart_1208612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208624 : List Nat := [2, 1, 1, 1, 2, 2, 2, 12]
def baseStart_1208624 : Nat := 118140960795 + 1208624 * 2 ^ 59
def prefixEnd_1208624 : Nat := 4983230072969 + 3 ^ 40 * 1208624 * 2
def baseEnd_1208624 : Nat := 22985371946658684694135

theorem tailTrace_1208624 : CollatzResearch.WordTrace tailWord_1208624 prefixEnd_1208624 22985371946658684694135 := by
  unfold tailWord_1208624
  simp only [CollatzResearch.WordTrace]
  refine ⟨22041069386684569695324463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29388092515579426260432617 22041069386684569695324463)
  ·
    refine ⟨33061604080026854542986695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22041069386684569695324463 33061604080026854542986695)
    ·
      refine ⟨49592406120040281814480043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33061604080026854542986695 49592406120040281814480043)
      ·
        refine ⟨74388609180060422721720065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49592406120040281814480043 74388609180060422721720065)
        ·
          refine ⟨55791456885045317041290049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74388609180060422721720065 55791456885045317041290049)
          ·
            refine ⟨41843592663783987780967537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55791456885045317041290049 41843592663783987780967537)
            ·
              refine ⟨31382694497837990835725653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41843592663783987780967537 31382694497837990835725653)
              ·
                refine ⟨22985371946658684694135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 31382694497837990835725653 22985371946658684694135)
                ·
                  rfl

theorem cell23_1208624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 12].length) (baseStart_1208624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208624 prefixEnd_1208624 := by exact prefixLift 1208624
  have htrace : WordTrace (prefixWord ++ tailWord_1208624) baseStart_1208624 baseEnd_1208624 := by
    simpa [prefixWord, tailWord_1208624, baseEnd_1208624] using wordTrace_append hprefix tailTrace_1208624
  have hstable : (prefixWord ++ tailWord_1208624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208624).length < 2 ^ (prefixWord ++ tailWord_1208624).sum := by decide
  have hdescent : baseEnd_1208624 < baseStart_1208624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208628 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_1208628 : Nat := 118140960795 + 1208628 * 2 ^ 59
def prefixEnd_1208628 : Nat := 4983230072969 + 3 ^ 40 * 1208628 * 2
def baseEnd_1208628 : Nat := 206869032160800823697209

theorem tailTrace_1208628 : CollatzResearch.WordTrace tailWord_1208628 prefixEnd_1208628 206869032160800823697209 := by
  unfold tailWord_1208628
  simp only [CollatzResearch.WordTrace]
  refine ⟨22041142332677324036897269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29388189776903098715863025 22041142332677324036897269)
  ·
    refine ⟨2066357093688499128459119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22041142332677324036897269 2066357093688499128459119)
    ·
      refine ⟨3099535640532748692688679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2066357093688499128459119 3099535640532748692688679)
      ·
        refine ⟨4649303460799123039033019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3099535640532748692688679 4649303460799123039033019)
        ·
          refine ⟨6973955191198684558549529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4649303460799123039033019 6973955191198684558549529)
          ·
            refine ⟨5230466393399013418912147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6973955191198684558549529 5230466393399013418912147)
            ·
              refine ⟨7845699590098520128368221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5230466393399013418912147 7845699590098520128368221)
              ·
                refine ⟨2942137346286945048138083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7845699590098520128368221 2942137346286945048138083)
                ·
                  refine ⟨4413206019430417572207125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2942137346286945048138083 4413206019430417572207125)
                  ·
                    refine ⟨206869032160800823697209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4413206019430417572207125 206869032160800823697209)
                    ·
                      rfl

theorem cell23_1208628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_1208628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208628 prefixEnd_1208628 := by exact prefixLift 1208628
  have htrace : WordTrace (prefixWord ++ tailWord_1208628) baseStart_1208628 baseEnd_1208628 := by
    simpa [prefixWord, tailWord_1208628, baseEnd_1208628] using wordTrace_append hprefix tailTrace_1208628
  have hstable : (prefixWord ++ tailWord_1208628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208628).length < 2 ^ (prefixWord ++ tailWord_1208628).sum := by decide
  have hdescent : baseEnd_1208628 < baseStart_1208628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208651 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 3]
def baseStart_1208651 : Nat := 118140960795 + 1208651 * 2 ^ 59
def prefixEnd_1208651 : Nat := 4983230072969 + 3 ^ 40 * 1208651 * 2
def baseEnd_1208651 : Nat := 620618906537455881104021

theorem tailTrace_1208651 : CollatzResearch.WordTrace tailWord_1208651 prefixEnd_1208651 620618906537455881104021 := by
  unfold tailWord_1208651
  simp only [CollatzResearch.WordTrace]
  refine ⟨44083123544271323001881807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29388749029514215334587871 44083123544271323001881807)
  ·
    refine ⟨66124685316406984502822711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44083123544271323001881807 66124685316406984502822711)
    ·
      refine ⟨99187027974610476754234067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66124685316406984502822711 99187027974610476754234067)
      ·
        refine ⟨148780541961915715131351101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99187027974610476754234067 148780541961915715131351101)
        ·
          refine ⟨55792703235718393174256663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148780541961915715131351101 55792703235718393174256663)
          ·
            refine ⟨83689054853577589761384995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55792703235718393174256663 83689054853577589761384995)
            ·
              refine ⟨125533582280366384642077493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83689054853577589761384995 125533582280366384642077493)
              ·
                refine ⟨11768773338784348560194765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125533582280366384642077493 11768773338784348560194765)
                ·
                  refine ⟨4413290002044130710073037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11768773338784348560194765 4413290002044130710073037)
                  ·
                    refine ⟨1654983750766549016277389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4413290002044130710073037 1654983750766549016277389)
                    ·
                      refine ⟨620618906537455881104021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1654983750766549016277389 620618906537455881104021)
                      ·
                        rfl

theorem cell23_1208651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 3].length) (baseStart_1208651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208651 prefixEnd_1208651 := by exact prefixLift 1208651
  have htrace : WordTrace (prefixWord ++ tailWord_1208651) baseStart_1208651 baseEnd_1208651 := by
    simpa [prefixWord, tailWord_1208651, baseEnd_1208651] using wordTrace_append hprefix tailTrace_1208651
  have hstable : (prefixWord ++ tailWord_1208651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208651).length < 2 ^ (prefixWord ++ tailWord_1208651).sum := by decide
  have hdescent : baseEnd_1208651 < baseStart_1208651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208738 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1208738 : Nat := 118140960795 + 1208738 * 2 ^ 59
def prefixEnd_1208738 : Nat := 4983230072969 + 3 ^ 40 * 1208738 * 2
def baseEnd_1208738 : Nat := 620663579354397040716121

theorem tailTrace_1208738 : CollatzResearch.WordTrace tailWord_1208738 prefixEnd_1208738 620663579354397040716121 := by
  unfold tailWord_1208738
  simp only [CollatzResearch.WordTrace]
  refine ⟨11021574173739034215074717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29390864463304091240199245 11021574173739034215074717)
  ·
    refine ⟨4133090315152137830653019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11021574173739034215074717 4133090315152137830653019)
    ·
      refine ⟨6199635472728206745979529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4133090315152137830653019 6199635472728206745979529)
      ·
        refine ⟨4649726604546155059484647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6199635472728206745979529 4649726604546155059484647)
        ·
          refine ⟨6974589906819232589226971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4649726604546155059484647 6974589906819232589226971)
          ·
            refine ⟨10461884860228848883840457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6974589906819232589226971 10461884860228848883840457)
            ·
              refine ⟨7846413645171636662880343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10461884860228848883840457 7846413645171636662880343)
              ·
                refine ⟨11769620467757454994320515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7846413645171636662880343 11769620467757454994320515)
                ·
                  refine ⟨17654430701636182491480773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11769620467757454994320515 17654430701636182491480773)
                  ·
                    refine ⟨3310205756556784217152645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17654430701636182491480773 3310205756556784217152645)
                    ·
                      refine ⟨620663579354397040716121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3310205756556784217152645 620663579354397040716121)
                      ·
                        rfl

theorem cell23_1208738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1208738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208738 prefixEnd_1208738 := by exact prefixLift 1208738
  have htrace : WordTrace (prefixWord ++ tailWord_1208738) baseStart_1208738 baseEnd_1208738 := by
    simpa [prefixWord, tailWord_1208738, baseEnd_1208738] using wordTrace_append hprefix tailTrace_1208738
  have hstable : (prefixWord ++ tailWord_1208738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208738).length < 2 ^ (prefixWord ++ tailWord_1208738).sum := by decide
  have hdescent : baseEnd_1208738 < baseStart_1208738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208746 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_1208746 : Nat := 118140960795 + 1208746 * 2 ^ 59
def prefixEnd_1208746 : Nat := 4983230072969 + 3 ^ 40 * 1208746 * 2
def baseEnd_1208746 : Nat := 620667687199633009416085

theorem tailTrace_1208746 : CollatzResearch.WordTrace tailWord_1208746 prefixEnd_1208746 620667687199633009416085 := by
  unfold tailWord_1208746
  simp only [CollatzResearch.WordTrace]
  refine ⟨11021647119731788556647523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29391058985951436151060061 11021647119731788556647523)
  ·
    refine ⟨16532470679597682834971285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11021647119731788556647523 16532470679597682834971285)
    ·
      refine ⟨774959563106141382889279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16532470679597682834971285 774959563106141382889279)
      ·
        refine ⟨1162439344659212074333919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774959563106141382889279 1162439344659212074333919)
        ·
          refine ⟨1743659016988818111500879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162439344659212074333919 1743659016988818111500879)
          ·
            refine ⟨2615488525483227167251319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743659016988818111500879 2615488525483227167251319)
            ·
              refine ⟨3923232788224840750876979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615488525483227167251319 3923232788224840750876979)
              ·
                refine ⟨5884849182337261126315469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923232788224840750876979 5884849182337261126315469)
                ·
                  refine ⟨2206818443376472922368301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5884849182337261126315469 2206818443376472922368301)
                  ·
                    refine ⟨827556916266177345888113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2206818443376472922368301 827556916266177345888113)
                    ·
                      refine ⟨620667687199633009416085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 827556916266177345888113 620667687199633009416085)
                      ·
                        rfl

theorem cell23_1208746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_1208746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208746 prefixEnd_1208746 := by exact prefixLift 1208746
  have htrace : WordTrace (prefixWord ++ tailWord_1208746) baseStart_1208746 baseEnd_1208746 := by
    simpa [prefixWord, tailWord_1208746, baseEnd_1208746] using wordTrace_append hprefix tailTrace_1208746
  have hstable : (prefixWord ++ tailWord_1208746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208746).length < 2 ^ (prefixWord ++ tailWord_1208746).sum := by decide
  have hdescent : baseEnd_1208746 < baseStart_1208746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208778 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 2, 5]
def baseStart_1208778 : Nat := 118140960795 + 1208778 * 2 ^ 59
def prefixEnd_1208778 : Nat := 4983230072969 + 3 ^ 40 * 1208778 * 2
def baseEnd_1208778 : Nat := 206894706193525628071979

theorem tailTrace_1208778 : CollatzResearch.WordTrace tailWord_1208778 prefixEnd_1208778 206894706193525628071979 := by
  unfold tailWord_1208778
  simp only [CollatzResearch.WordTrace]
  refine ⟨11021938903702805922938747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29391837076540815794503325 11021938903702805922938747)
  ·
    refine ⟨16532908355554208884408121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11021938903702805922938747 16532908355554208884408121)
    ·
      refine ⟨12399681266665656663306091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16532908355554208884408121 12399681266665656663306091)
      ·
        refine ⟨18599521899998484994959137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12399681266665656663306091 18599521899998484994959137)
        ·
          refine ⟨13949641424998863746219353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18599521899998484994959137 13949641424998863746219353)
          ·
            refine ⟨10462231068749147809664515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13949641424998863746219353 10462231068749147809664515)
            ·
              refine ⟨15693346603123721714496773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10462231068749147809664515 15693346603123721714496773)
              ·
                refine ⟨2942502488085697821468145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15693346603123721714496773 2942502488085697821468145)
                ·
                  refine ⟨2206876866064273366101109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2942502488085697821468145 2206876866064273366101109)
                  ·
                    refine ⟨206894706193525628071979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2206876866064273366101109 206894706193525628071979)
                    ·
                      rfl

theorem cell23_1208778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_1208778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208778 prefixEnd_1208778 := by exact prefixLift 1208778
  have htrace : WordTrace (prefixWord ++ tailWord_1208778) baseStart_1208778 baseEnd_1208778 := by
    simpa [prefixWord, tailWord_1208778, baseEnd_1208778] using wordTrace_append hprefix tailTrace_1208778
  have hstable : (prefixWord ++ tailWord_1208778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208778).length < 2 ^ (prefixWord ++ tailWord_1208778).sum := by decide
  have hdescent : baseEnd_1208778 < baseStart_1208778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208791 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 4, 8]
def baseStart_1208791 : Nat := 118140960795 + 1208791 * 2 ^ 59
def prefixEnd_1208791 : Nat := 4983230072969 + 3 ^ 40 * 1208791 * 2
def baseEnd_1208791 : Nat := 206896931276361777784459

theorem tailTrace_1208791 : CollatzResearch.WordTrace tailWord_1208791 prefixEnd_1208791 206896931276361777784459 := by
  unfold tailWord_1208791
  simp only [CollatzResearch.WordTrace]
  refine ⟨44088229763764126911978227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29392153175842751274652151 44088229763764126911978227)
  ·
    refine ⟨66132344645646190367967341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44088229763764126911978227 66132344645646190367967341)
    ·
      refine ⟨24799629242117321387987753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66132344645646190367967341 24799629242117321387987753)
      ·
        refine ⟨18599721931587991040990815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24799629242117321387987753 18599721931587991040990815)
        ·
          refine ⟨27899582897381986561486223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18599721931587991040990815 27899582897381986561486223)
          ·
            refine ⟨41849374346072979842229335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27899582897381986561486223 41849374346072979842229335)
            ·
              refine ⟨62774061519109469763344003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41849374346072979842229335 62774061519109469763344003)
              ·
                refine ⟨94161092278664204645016005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62774061519109469763344003 94161092278664204645016005)
                ·
                  refine ⟨17655204802249538370940501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94161092278664204645016005 17655204802249538370940501)
                  ·
                    refine ⟨206896931276361777784459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17655204802249538370940501 206896931276361777784459)
                    ·
                      rfl

theorem cell23_1208791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_1208791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208791 prefixEnd_1208791 := by exact prefixLift 1208791
  have htrace : WordTrace (prefixWord ++ tailWord_1208791) baseStart_1208791 baseEnd_1208791 := by
    simpa [prefixWord, tailWord_1208791, baseEnd_1208791] using wordTrace_append hprefix tailTrace_1208791
  have hstable : (prefixWord ++ tailWord_1208791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208791).length < 2 ^ (prefixWord ++ tailWord_1208791).sum := by decide
  have hdescent : baseEnd_1208791 < baseStart_1208791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208842 : List Nat := [3, 1, 2, 2, 2, 1, 1, 6, 1, 4]
def baseStart_1208842 : Nat := 118140960795 + 1208842 * 2 ^ 59
def prefixEnd_1208842 : Nat := 4983230072969 + 3 ^ 40 * 1208842 * 2
def baseEnd_1208842 : Nat := 206905660447488211271881

theorem tailTrace_1208842 : CollatzResearch.WordTrace tailWord_1208842 prefixEnd_1208842 206905660447488211271881 := by
  unfold tailWord_1208842
  simp only [CollatzResearch.WordTrace]
  refine ⟨11022522471644840655521195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29393393257719575081389853 11022522471644840655521195)
  ·
    refine ⟨16533783707467260983281793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11022522471644840655521195 16533783707467260983281793)
    ·
      refine ⟨12400337780600445737461345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16533783707467260983281793 12400337780600445737461345)
      ·
        refine ⟨9300253335450334303096009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12400337780600445737461345 9300253335450334303096009)
        ·
          refine ⟨6975190001587750727322007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9300253335450334303096009 6975190001587750727322007)
          ·
            refine ⟨10462785002381626090983011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6975190001587750727322007 10462785002381626090983011)
            ·
              refine ⟨15694177503572439136474517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10462785002381626090983011 15694177503572439136474517)
              ·
                refine ⟨735664570479958084522243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15694177503572439136474517 735664570479958084522243)
                ·
                  refine ⟨1103496855719937126783365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735664570479958084522243 1103496855719937126783365)
                  ·
                    refine ⟨206905660447488211271881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1103496855719937126783365 206905660447488211271881)
                    ·
                      rfl

theorem cell23_1208842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_1208842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208842 prefixEnd_1208842 := by exact prefixLift 1208842
  have htrace : WordTrace (prefixWord ++ tailWord_1208842) baseStart_1208842 baseEnd_1208842 := by
    simpa [prefixWord, tailWord_1208842, baseEnd_1208842] using wordTrace_append hprefix tailTrace_1208842
  have hstable : (prefixWord ++ tailWord_1208842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208842).length < 2 ^ (prefixWord ++ tailWord_1208842).sum := by decide
  have hdescent : baseEnd_1208842 < baseStart_1208842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208852 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1208852 : Nat := 118140960795 + 1208852 * 2 ^ 59
def prefixEnd_1208852 : Nat := 4983230072969 + 3 ^ 40 * 1208852 * 2
def baseEnd_1208852 : Nat := 620722116149009594690597

theorem tailTrace_1208852 : CollatzResearch.WordTrace tailWord_1208852 prefixEnd_1208852 620722116149009594690597 := by
  unfold tailWord_1208852
  simp only [CollatzResearch.WordTrace]
  refine ⟨22045227308271567164974405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29393636411028756219965873 22045227308271567164974405)
  ·
    refine ⟨4133480120300918843432701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22045227308271567164974405 4133480120300918843432701)
    ·
      refine ⟨1550055045112844566287263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4133480120300918843432701 1550055045112844566287263)
      ·
        refine ⟨2325082567669266849430895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550055045112844566287263 2325082567669266849430895)
        ·
          refine ⟨3487623851503900274146343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325082567669266849430895 3487623851503900274146343)
          ·
            refine ⟨5231435777255850411219515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3487623851503900274146343 5231435777255850411219515)
            ·
              refine ⟨7847153665883775616829273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5231435777255850411219515 7847153665883775616829273)
              ·
                refine ⟨5885365249412831712621955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7847153665883775616829273 5885365249412831712621955)
                ·
                  refine ⟨8828047874119247568932933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5885365249412831712621955 8828047874119247568932933)
                  ·
                    refine ⟨1655258976397358919174925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8828047874119247568932933 1655258976397358919174925)
                    ·
                      refine ⟨620722116149009594690597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1655258976397358919174925 620722116149009594690597)
                      ·
                        rfl

theorem cell23_1208852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1208852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208852 prefixEnd_1208852 := by exact prefixLift 1208852
  have htrace : WordTrace (prefixWord ++ tailWord_1208852) baseStart_1208852 baseEnd_1208852 := by
    simpa [prefixWord, tailWord_1208852, baseEnd_1208852] using wordTrace_append hprefix tailTrace_1208852
  have hstable : (prefixWord ++ tailWord_1208852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208852).length < 2 ^ (prefixWord ++ tailWord_1208852).sum := by decide
  have hdescent : baseEnd_1208852 < baseStart_1208852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208875 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 6, 3, 2]
def baseStart_1208875 : Nat := 118140960795 + 1208875 * 2 ^ 59
def prefixEnd_1208875 : Nat := 4983230072969 + 3 ^ 40 * 1208875 * 2
def baseEnd_1208875 : Nat := 620733926204063004702991

theorem tailTrace_1208875 : CollatzResearch.WordTrace tailWord_1208875 prefixEnd_1208875 620733926204063004702991 := by
  unfold tailWord_1208875
  simp only [CollatzResearch.WordTrace]
  refine ⟨44091293495459809258036079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29394195663639872838690719 44091293495459809258036079)
  ·
    refine ⟨66136940243189713887054119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44091293495459809258036079 66136940243189713887054119)
    ·
      refine ⟨99205410364784570830581179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66136940243189713887054119 99205410364784570830581179)
      ·
        refine ⟨148808115547176856245871769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99205410364784570830581179 148808115547176856245871769)
        ·
          refine ⟨111606086660382642184403827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148808115547176856245871769 111606086660382642184403827)
          ·
            refine ⟨167409129990573963276605741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111606086660382642184403827 167409129990573963276605741)
            ·
              refine ⟨62778423746465236228727153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167409129990573963276605741 62778423746465236228727153)
              ·
                refine ⟨47083817809848927171545365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62778423746465236228727153 47083817809848927171545365)
                ·
                  refine ⟨2207053959836668461166189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47083817809848927171545365 2207053959836668461166189)
                  ·
                    refine ⟨827645234938750672937321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2207053959836668461166189 827645234938750672937321)
                    ·
                      refine ⟨620733926204063004702991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 827645234938750672937321 620733926204063004702991)
                      ·
                        rfl

theorem cell23_1208875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 3, 2].length) (baseStart_1208875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208875 prefixEnd_1208875 := by exact prefixLift 1208875
  have htrace : WordTrace (prefixWord ++ tailWord_1208875) baseStart_1208875 baseEnd_1208875 := by
    simpa [prefixWord, tailWord_1208875, baseEnd_1208875] using wordTrace_append hprefix tailTrace_1208875
  have hstable : (prefixWord ++ tailWord_1208875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208875).length < 2 ^ (prefixWord ++ tailWord_1208875).sum := by decide
  have hdescent : baseEnd_1208875 < baseStart_1208875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208885 : List Nat := [1, 3, 3, 1, 1, 2, 1, 5, 1, 5]
def baseStart_1208885 : Nat := 118140960795 + 1208885 * 2 ^ 59
def prefixEnd_1208885 : Nat := 4983230072969 + 3 ^ 40 * 1208885 * 2
def baseEnd_1208885 : Nat := 206913020336869321859315

theorem tailTrace_1208885 : CollatzResearch.WordTrace tailWord_1208885 prefixEnd_1208885 206913020336869321859315 := by
  unfold tailWord_1208885
  simp only [CollatzResearch.WordTrace]
  refine ⟨44091658225423580965900109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29394438816949053977266739 44091658225423580965900109)
  ·
    refine ⟨16534371834533842862212541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44091658225423580965900109 16534371834533842862212541)
    ·
      refine ⟨6200389437950191073329703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16534371834533842862212541 6200389437950191073329703)
      ·
        refine ⟨9300584156925286609994555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6200389437950191073329703 9300584156925286609994555)
        ·
          refine ⟨13950876235387929914991833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9300584156925286609994555 13950876235387929914991833)
          ·
            refine ⟨10463157176540947436243875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13950876235387929914991833 10463157176540947436243875)
            ·
              refine ⟨15694735764811421154365813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10463157176540947436243875 15694735764811421154365813)
              ·
                refine ⟨1471381477951070733221795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15694735764811421154365813 1471381477951070733221795)
                ·
                  refine ⟨2207072216926606099832693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471381477951070733221795 2207072216926606099832693)
                  ·
                    refine ⟨206913020336869321859315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2207072216926606099832693 206913020336869321859315)
                    ·
                      rfl

theorem cell23_1208885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_1208885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208885 prefixEnd_1208885 := by exact prefixLift 1208885
  have htrace : WordTrace (prefixWord ++ tailWord_1208885) baseStart_1208885 baseEnd_1208885 := by
    simpa [prefixWord, tailWord_1208885, baseEnd_1208885] using wordTrace_append hprefix tailTrace_1208885
  have hstable : (prefixWord ++ tailWord_1208885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208885).length < 2 ^ (prefixWord ++ tailWord_1208885).sum := by decide
  have hdescent : baseEnd_1208885 < baseStart_1208885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208892 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 4, 3, 2]
def baseStart_1208892 : Nat := 118140960795 + 1208892 * 2 ^ 59
def prefixEnd_1208892 : Nat := 4983230072969 + 3 ^ 40 * 1208892 * 2
def baseEnd_1208892 : Nat := 620742655375189438190413

theorem tailTrace_1208892 : CollatzResearch.WordTrace tailWord_1208892 prefixEnd_1208892 620742655375189438190413 := by
  unfold tailWord_1208892
  simp only [CollatzResearch.WordTrace]
  refine ⟨22045956768199110580702465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29394609024265480774269953 22045956768199110580702465)
  ·
    refine ⟨16534467576149332935526849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22045956768199110580702465 16534467576149332935526849)
    ·
      refine ⟨12400850682111999701645137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16534467576149332935526849 12400850682111999701645137)
      ·
        refine ⟨9300638011583999776233853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12400850682111999701645137 9300638011583999776233853)
        ·
          refine ⟨3487739254343999916087695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9300638011583999776233853 3487739254343999916087695)
          ·
            refine ⟨5231608881515999874131543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3487739254343999916087695 5231608881515999874131543)
            ·
              refine ⟨7847413322273999811197315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5231608881515999874131543 7847413322273999811197315)
              ·
                refine ⟨11771119983410999716795973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7847413322273999811197315 11771119983410999716795973)
                ·
                  refine ⟨2207084996889562446899245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11771119983410999716795973 2207084996889562446899245)
                  ·
                    refine ⟨827656873833585917587217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2207084996889562446899245 827656873833585917587217)
                    ·
                      refine ⟨620742655375189438190413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 827656873833585917587217 620742655375189438190413)
                      ·
                        rfl

theorem cell23_1208892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_1208892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208892 prefixEnd_1208892 := by exact prefixLift 1208892
  have htrace : WordTrace (prefixWord ++ tailWord_1208892) baseStart_1208892 baseEnd_1208892 := by
    simpa [prefixWord, tailWord_1208892, baseEnd_1208892] using wordTrace_append hprefix tailTrace_1208892
  have hstable : (prefixWord ++ tailWord_1208892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208892).length < 2 ^ (prefixWord ++ tailWord_1208892).sum := by decide
  have hdescent : baseEnd_1208892 < baseStart_1208892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208928 : List Nat := [2, 1, 1, 3, 2, 1, 4, 9]
def baseStart_1208928 : Nat := 118140960795 + 1208928 * 2 ^ 59
def prefixEnd_1208928 : Nat := 4983230072969 + 3 ^ 40 * 1208928 * 2
def baseEnd_1208928 : Nat := 22991153358472270271861

theorem tailTrace_1208928 : CollatzResearch.WordTrace tailWord_1208928 prefixEnd_1208928 22991153358472270271861 := by
  unfold tailWord_1208928
  simp only [CollatzResearch.WordTrace]
  refine ⟨22046613282133899654857719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29395484376178532873143625 22046613282133899654857719)
  ·
    refine ⟨33069919923200849482286579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22046613282133899654857719 33069919923200849482286579)
    ·
      refine ⟨49604879884801274223429869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33069919923200849482286579 49604879884801274223429869)
      ·
        refine ⟨18601829956800477833786201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49604879884801274223429869 18601829956800477833786201)
        ·
          refine ⟨13951372467600358375339651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18601829956800477833786201 13951372467600358375339651)
          ·
            refine ⟨20927058701400537563009477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13951372467600358375339651 20927058701400537563009477)
            ·
              refine ⟨3923823506512600793064277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20927058701400537563009477 3923823506512600793064277)
              ·
                refine ⟨22991153358472270271861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3923823506512600793064277 22991153358472270271861)
                ·
                  rfl

theorem cell23_1208928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 9].length) (baseStart_1208928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208928 prefixEnd_1208928 := by exact prefixLift 1208928
  have htrace : WordTrace (prefixWord ++ tailWord_1208928) baseStart_1208928 baseEnd_1208928 := by
    simpa [prefixWord, tailWord_1208928, baseEnd_1208928] using wordTrace_append hprefix tailTrace_1208928
  have hstable : (prefixWord ++ tailWord_1208928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208928).length < 2 ^ (prefixWord ++ tailWord_1208928).sum := by decide
  have hdescent : baseEnd_1208928 < baseStart_1208928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208942 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_1208942 : Nat := 118140960795 + 1208942 * 2 ^ 59
def prefixEnd_1208942 : Nat := 4983230072969 + 3 ^ 40 * 1208942 * 2
def baseEnd_1208942 : Nat := 620768329407914242565183

theorem tailTrace_1208942 : CollatzResearch.WordTrace tailWord_1208942 prefixEnd_1208942 620768329407914242565183 := by
  unfold tailWord_1208942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5511717148277134962590635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29395824790811386467150053 5511717148277134962590635)
  ·
    refine ⟨8267575722415702443885953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5511717148277134962590635 8267575722415702443885953)
    ·
      refine ⟨6200681791811776832914465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8267575722415702443885953 6200681791811776832914465)
      ·
        refine ⟨4650511343858832624685849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6200681791811776832914465 4650511343858832624685849)
        ·
          refine ⟨3487883507894124468514387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4650511343858832624685849 3487883507894124468514387)
          ·
            refine ⟨5231825261841186702771581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3487883507894124468514387 5231825261841186702771581)
            ·
              refine ⟨1961934473190445013539343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5231825261841186702771581 1961934473190445013539343)
              ·
                refine ⟨2942901709785667520309015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1961934473190445013539343 2942901709785667520309015)
                ·
                  refine ⟨4414352564678501280463523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2942901709785667520309015 4414352564678501280463523)
                  ·
                    refine ⟨6621528847017751920695285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4414352564678501280463523 6621528847017751920695285)
                    ·
                      refine ⟨620768329407914242565183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6621528847017751920695285 620768329407914242565183)
                      ·
                        rfl

theorem cell23_1208942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_1208942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208942 prefixEnd_1208942 := by exact prefixLift 1208942
  have htrace : WordTrace (prefixWord ++ tailWord_1208942) baseStart_1208942 baseEnd_1208942 := by
    simpa [prefixWord, tailWord_1208942, baseEnd_1208942] using wordTrace_append hprefix tailTrace_1208942
  have hstable : (prefixWord ++ tailWord_1208942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208942).length < 2 ^ (prefixWord ++ tailWord_1208942).sum := by decide
  have hdescent : baseEnd_1208942 < baseStart_1208942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208950 : List Nat := [5, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3]
def baseStart_1208950 : Nat := 118140960795 + 1208950 * 2 ^ 59
def prefixEnd_1208950 : Nat := 4983230072969 + 3 ^ 40 * 1208950 * 2
def baseEnd_1208950 : Nat := 620772437253150211265147

theorem tailTrace_1208950 : CollatzResearch.WordTrace tailWord_1208950 prefixEnd_1208950 620772437253150211265147 := by
  unfold tailWord_1208950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2755876810636756066688519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29396019313458731378010869 2755876810636756066688519)
  ·
    refine ⟨4133815215955134100032779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2755876810636756066688519 4133815215955134100032779)
    ·
      refine ⟨6200722823932701150049169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4133815215955134100032779 6200722823932701150049169)
      ·
        refine ⟨4650542117949525862536877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6200722823932701150049169 4650542117949525862536877)
        ·
          refine ⟨1743953294231072198451329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4650542117949525862536877 1743953294231072198451329)
          ·
            refine ⟨1307964970673304148838497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1743953294231072198451329 1307964970673304148838497)
            ·
              refine ⟨980973728004978111628873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1307964970673304148838497 980973728004978111628873)
              ·
                refine ⟨735730296003733583721655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 980973728004978111628873 735730296003733583721655)
                ·
                  refine ⟨1103595444005600375582483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735730296003733583721655 1103595444005600375582483)
                  ·
                    refine ⟨1655393166008400563373725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1103595444005600375582483 1655393166008400563373725)
                    ·
                      refine ⟨620772437253150211265147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1655393166008400563373725 620772437253150211265147)
                      ·
                        rfl

theorem cell23_1208950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_1208950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208950 prefixEnd_1208950 := by exact prefixLift 1208950
  have htrace : WordTrace (prefixWord ++ tailWord_1208950) baseStart_1208950 baseEnd_1208950 := by
    simpa [prefixWord, tailWord_1208950, baseEnd_1208950] using wordTrace_append hprefix tailTrace_1208950
  have hstable : (prefixWord ++ tailWord_1208950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208950).length < 2 ^ (prefixWord ++ tailWord_1208950).sum := by decide
  have hdescent : baseEnd_1208950 < baseStart_1208950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208993 : List Nat := [1, 2, 3, 3, 4, 1, 2, 1, 1, 2, 3]
def baseStart_1208993 : Nat := 118140960795 + 1208993 * 2 ^ 59
def prefixEnd_1208993 : Nat := 4983230072969 + 3 ^ 40 * 1208993 * 2
def baseEnd_1208993 : Nat := 620794516921293543027449

theorem tailTrace_1208993 : CollatzResearch.WordTrace tailWord_1208993 prefixEnd_1208993 620794516921293543027449 := by
  unfold tailWord_1208993
  simp only [CollatzResearch.WordTrace]
  refine ⟨44095597309032315410831633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29397064872688210273887755 44095597309032315410831633)
  ·
    refine ⟨33071697981774236558123725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44095597309032315410831633 33071697981774236558123725)
    ·
      refine ⟨12401886743165338709296397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33071697981774236558123725 12401886743165338709296397)
      ·
        refine ⟨4650707528687002015986149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12401886743165338709296397 4650707528687002015986149)
        ·
          refine ⟨872007661628812877997403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4650707528687002015986149 872007661628812877997403)
          ·
            refine ⟨1308011492443219316996105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872007661628812877997403 1308011492443219316996105)
            ·
              refine ⟨981008619332414487747079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1308011492443219316996105 981008619332414487747079)
              ·
                refine ⟨1471512928998621731620619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981008619332414487747079 1471512928998621731620619)
                ·
                  refine ⟨2207269393497932597430929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471512928998621731620619 2207269393497932597430929)
                  ·
                    refine ⟨1655452045123449448073197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2207269393497932597430929 1655452045123449448073197)
                    ·
                      refine ⟨620794516921293543027449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1655452045123449448073197 620794516921293543027449)
                      ·
                        rfl

theorem cell23_1208993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_1208993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1208993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1208993 prefixEnd_1208993 := by exact prefixLift 1208993
  have htrace : WordTrace (prefixWord ++ tailWord_1208993) baseStart_1208993 baseEnd_1208993 := by
    simpa [prefixWord, tailWord_1208993, baseEnd_1208993] using wordTrace_append hprefix tailTrace_1208993
  have hstable : (prefixWord ++ tailWord_1208993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208993).length < 2 ^ (prefixWord ++ tailWord_1208993).sum := by decide
  have hdescent : baseEnd_1208993 < baseStart_1208993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209006 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1209006 : Nat := 118140960795 + 1209006 * 2 ^ 59
def prefixEnd_1209006 : Nat := 4983230072969 + 3 ^ 40 * 1209006 * 2
def baseEnd_1209006 : Nat := 620801192169801992164889

theorem tailTrace_1209006 : CollatzResearch.WordTrace tailWord_1209006 prefixEnd_1209006 620801192169801992164889 := by
  unfold tailWord_1209006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5512008932248152328881859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29397380971990145754036581 5512008932248152328881859)
  ·
    refine ⟨8268013398372228493322789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5512008932248152328881859 8268013398372228493322789)
    ·
      refine ⟨1550252512194792842498023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8268013398372228493322789 1550252512194792842498023)
      ·
        refine ⟨2325378768292189263747035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550252512194792842498023 2325378768292189263747035)
        ·
          refine ⟨3488068152438283895620553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325378768292189263747035 3488068152438283895620553)
          ·
            refine ⟨2616051114328712921715415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3488068152438283895620553 2616051114328712921715415)
            ·
              refine ⟨3924076671493069382573123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616051114328712921715415 3924076671493069382573123)
              ·
                refine ⟨5886115007239604073859685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3924076671493069382573123 5886115007239604073859685)
                ·
                  refine ⟨1103646563857425763848691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5886115007239604073859685 1103646563857425763848691)
                  ·
                    refine ⟨1655469845786138645773037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1103646563857425763848691 1655469845786138645773037)
                    ·
                      refine ⟨620801192169801992164889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1655469845786138645773037 620801192169801992164889)
                      ·
                        rfl

theorem cell23_1209006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1209006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209006 prefixEnd_1209006 := by exact prefixLift 1209006
  have htrace : WordTrace (prefixWord ++ tailWord_1209006) baseStart_1209006 baseEnd_1209006 := by
    simpa [prefixWord, tailWord_1209006, baseEnd_1209006] using wordTrace_append hprefix tailTrace_1209006
  have hstable : (prefixWord ++ tailWord_1209006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209006).length < 2 ^ (prefixWord ++ tailWord_1209006).sum := by decide
  have hdescent : baseEnd_1209006 < baseStart_1209006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209065 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 4, 5]
def baseStart_1209065 : Nat := 118140960795 + 1209065 * 2 ^ 59
def prefixEnd_1209065 : Nat := 4983230072969 + 3 ^ 40 * 1209065 * 2
def baseEnd_1209065 : Nat := 206943829176139087109039

theorem tailTrace_1209065 : CollatzResearch.WordTrace tailWord_1209065 prefixEnd_1209065 206943829176139087109039 := by
  unfold tailWord_1209065
  simp only [CollatzResearch.WordTrace]
  refine ⟨44098223364771471707452649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29398815576514314471635099 44098223364771471707452649)
  ·
    refine ⟨33073667523578603780589487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44098223364771471707452649 33073667523578603780589487)
    ·
      refine ⟨49610501285367905670884231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33073667523578603780589487 49610501285367905670884231)
      ·
        refine ⟨74415751928051858506326347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49610501285367905670884231 74415751928051858506326347)
        ·
          refine ⟨111623627892077787759489521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74415751928051858506326347 111623627892077787759489521)
          ·
            refine ⟨83717720919058340819617141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111623627892077787759489521 83717720919058340819617141)
            ·
              refine ⟨7848536336161719451839107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83717720919058340819617141 7848536336161719451839107)
              ·
                refine ⟨11772804504242579177758661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7848536336161719451839107 11772804504242579177758661)
                ·
                  refine ⟨2207400844545483595829749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11772804504242579177758661 2207400844545483595829749)
                  ·
                    refine ⟨206943829176139087109039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2207400844545483595829749 206943829176139087109039)
                    ·
                      rfl

theorem cell23_1209065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 5].length) (baseStart_1209065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209065 prefixEnd_1209065 := by exact prefixLift 1209065
  have htrace : WordTrace (prefixWord ++ tailWord_1209065) baseStart_1209065 baseEnd_1209065 := by
    simpa [prefixWord, tailWord_1209065, baseEnd_1209065] using wordTrace_append hprefix tailTrace_1209065
  have hstable : (prefixWord ++ tailWord_1209065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209065).length < 2 ^ (prefixWord ++ tailWord_1209065).sum := by decide
  have hdescent : baseEnd_1209065 < baseStart_1209065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209072 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 2, 5, 2]
def baseStart_1209072 : Nat := 118140960795 + 1209072 * 2 ^ 59
def prefixEnd_1209072 : Nat := 4983230072969 + 3 ^ 40 * 1209072 * 2
def baseEnd_1209072 : Nat := 620835081892998733939585

theorem tailTrace_1209072 : CollatzResearch.WordTrace tailWord_1209072 prefixEnd_1209072 620835081892998733939585 := by
  unfold tailWord_1209072
  simp only [CollatzResearch.WordTrace]
  refine ⟨22049239337873055951478735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29398985783830741268638313 22049239337873055951478735)
  ·
    refine ⟨33073859006809583927218103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22049239337873055951478735 33073859006809583927218103)
    ·
      refine ⟨49610788510214375890827155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33073859006809583927218103 49610788510214375890827155)
      ·
        refine ⟨74416182765321563836240733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49610788510214375890827155 74416182765321563836240733)
        ·
          refine ⟨27906068536995586438590275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74416182765321563836240733 27906068536995586438590275)
          ·
            refine ⟨41859102805493379657885413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27906068536995586438590275 41859102805493379657885413)
            ·
              refine ⟨7848581776030008685853515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41859102805493379657885413 7848581776030008685853515)
              ·
                refine ⟨11772872664045013028780273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7848581776030008685853515 11772872664045013028780273)
                ·
                  refine ⟨8829654498033759771585205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11772872664045013028780273 8829654498033759771585205)
                  ·
                    refine ⟨827780109190664978586113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8829654498033759771585205 827780109190664978586113)
                    ·
                      refine ⟨620835081892998733939585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 827780109190664978586113 620835081892998733939585)
                      ·
                        rfl

theorem cell23_1209072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 2, 5, 2].length) (baseStart_1209072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209072 prefixEnd_1209072 := by exact prefixLift 1209072
  have htrace : WordTrace (prefixWord ++ tailWord_1209072) baseStart_1209072 baseEnd_1209072 := by
    simpa [prefixWord, tailWord_1209072, baseEnd_1209072] using wordTrace_append hprefix tailTrace_1209072
  have hstable : (prefixWord ++ tailWord_1209072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209072).length < 2 ^ (prefixWord ++ tailWord_1209072).sum := by decide
  have hdescent : baseEnd_1209072 < baseStart_1209072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209129 : List Nat := [1, 2, 1, 1, 1, 1, 1, 10, 1, 4]
def baseStart_1209129 : Nat := 118140960795 + 1209129 * 2 ^ 59
def prefixEnd_1209129 : Nat := 4983230072969 + 3 ^ 40 * 1209129 * 2
def baseEnd_1209129 : Nat := 206954783430101670308941

theorem tailTrace_1209129 : CollatzResearch.WordTrace tailWord_1209129 prefixEnd_1209129 206954783430101670308941 := by
  unfold tailWord_1209129
  simp only [CollatzResearch.WordTrace]
  refine ⟨44100557636539610637782441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29400371757693073758521627 44100557636539610637782441)
  ·
    refine ⟨33075418227404707978336831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44100557636539610637782441 33075418227404707978336831)
    ·
      refine ⟨49613127341107061967505247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33075418227404707978336831 49613127341107061967505247)
      ·
        refine ⟨74419691011660592951257871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49613127341107061967505247 74419691011660592951257871)
        ·
          refine ⟨111629536517490889426886807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74419691011660592951257871 111629536517490889426886807)
          ·
            refine ⟨167444304776236334140330211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111629536517490889426886807 167444304776236334140330211)
            ·
              refine ⟨251166457164354501210495317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167444304776236334140330211 251166457164354501210495317)
              ·
                refine ⟨735839229973694827765123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 251166457164354501210495317 735839229973694827765123)
                ·
                  refine ⟨1103758844960542241647685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 735839229973694827765123 1103758844960542241647685)
                  ·
                    refine ⟨206954783430101670308941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1103758844960542241647685 206954783430101670308941)
                    ·
                      rfl

theorem cell23_1209129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 1, 4].length) (baseStart_1209129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209129 prefixEnd_1209129 := by exact prefixLift 1209129
  have htrace : WordTrace (prefixWord ++ tailWord_1209129) baseStart_1209129 baseEnd_1209129 := by
    simpa [prefixWord, tailWord_1209129, baseEnd_1209129] using wordTrace_append hprefix tailTrace_1209129
  have hstable : (prefixWord ++ tailWord_1209129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209129).length < 2 ^ (prefixWord ++ tailWord_1209129).sum := by decide
  have hdescent : baseEnd_1209129 < baseStart_1209129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209153 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1209153 : Nat := 118140960795 + 1209153 * 2 ^ 59
def prefixEnd_1209153 : Nat := 4983230072969 + 3 ^ 40 * 1209153 * 2
def baseEnd_1209153 : Nat := 620876673826012917026713

theorem tailTrace_1209153 : CollatzResearch.WordTrace tailWord_1209153 prefixEnd_1209153 620876673826012917026713 := by
  unfold tailWord_1209153
  simp only [CollatzResearch.WordTrace]
  refine ⟨44101432988452662736656113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29400955325635108491104075 44101432988452662736656113)
  ·
    refine ⟨33076074741339497052492085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44101432988452662736656113 33076074741339497052492085)
    ·
      refine ⟨3100882007000577848671133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33076074741339497052492085 3100882007000577848671133)
      ·
        refine ⟨1162830752625216693251675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3100882007000577848671133 1162830752625216693251675)
        ·
          refine ⟨1744246128937825039877513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162830752625216693251675 1744246128937825039877513)
          ·
            refine ⟨1308184596703368779908135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1744246128937825039877513 1308184596703368779908135)
            ·
              refine ⟨1962276895055053169862203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308184596703368779908135 1962276895055053169862203)
              ·
                refine ⟨2943415342582579754793305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1962276895055053169862203 2943415342582579754793305)
                ·
                  refine ⟨2207561506936934816094979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2943415342582579754793305 2207561506936934816094979)
                  ·
                    refine ⟨3311342260405402224142469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2207561506936934816094979 3311342260405402224142469)
                    ·
                      refine ⟨620876673826012917026713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3311342260405402224142469 620876673826012917026713)
                      ·
                        rfl

theorem cell23_1209153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1209153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209153 prefixEnd_1209153 := by exact prefixLift 1209153
  have htrace : WordTrace (prefixWord ++ tailWord_1209153) baseStart_1209153 baseEnd_1209153 := by
    simpa [prefixWord, tailWord_1209153, baseEnd_1209153] using wordTrace_append hprefix tailTrace_1209153
  have hstable : (prefixWord ++ tailWord_1209153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209153).length < 2 ^ (prefixWord ++ tailWord_1209153).sum := by decide
  have hdescent : baseEnd_1209153 < baseStart_1209153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209206 : List Nat := [5, 1, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_1209206 : Nat := 118140960795 + 1209206 * 2 ^ 59
def prefixEnd_1209206 : Nat := 4983230072969 + 3 ^ 40 * 1209206 * 2
def baseEnd_1209206 : Nat := 206967962766900403221323

theorem tailTrace_1209206 : CollatzResearch.WordTrace tailWord_1209206 prefixEnd_1209206 206967962766900403221323 := by
  unfold tailWord_1209206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2756460378578790799270967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29402244038173768525556981 2756460378578790799270967)
  ·
    refine ⟨4134690567868186198906451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2756460378578790799270967 4134690567868186198906451)
    ·
      refine ⟨6202035851802279298359677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4134690567868186198906451 6202035851802279298359677)
      ·
        refine ⟨2325763444425854736884879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6202035851802279298359677 2325763444425854736884879)
        ·
          refine ⟨3488645166638782105327319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325763444425854736884879 3488645166638782105327319)
          ·
            refine ⟨5232967749958173157990979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3488645166638782105327319 5232967749958173157990979)
            ·
              refine ⟨7849451624937259736986469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5232967749958173157990979 7849451624937259736986469)
              ·
                refine ⟨1471772179675736200684963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7849451624937259736986469 1471772179675736200684963)
                ·
                  refine ⟨2207658269513604301027445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471772179675736200684963 2207658269513604301027445)
                  ·
                    refine ⟨206967962766900403221323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2207658269513604301027445 206967962766900403221323)
                    ·
                      rfl

theorem cell23_1209206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_1209206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209206 prefixEnd_1209206 := by exact prefixLift 1209206
  have htrace : WordTrace (prefixWord ++ tailWord_1209206) baseStart_1209206 baseEnd_1209206 := by
    simpa [prefixWord, tailWord_1209206, baseEnd_1209206] using wordTrace_append hprefix tailTrace_1209206
  have hstable : (prefixWord ++ tailWord_1209206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209206).length < 2 ^ (prefixWord ++ tailWord_1209206).sum := by decide
  have hdescent : baseEnd_1209206 < baseStart_1209206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209209 : List Nat := [1, 2, 1, 3, 2, 3, 1, 4, 1, 1, 4]
def baseStart_1209209 : Nat := 118140960795 + 1209209 * 2 ^ 59
def prefixEnd_1209209 : Nat := 4983230072969 + 3 ^ 40 * 1209209 * 2
def baseEnd_1209209 : Nat := 620905428742664697926455

theorem tailTrace_1209209 : CollatzResearch.WordTrace tailWord_1209209 prefixEnd_1209209 620905428742664697926455 := by
  unfold tailWord_1209209
  simp only [CollatzResearch.WordTrace]
  refine ⟨44103475476249784300694681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29402316984166522867129787 44103475476249784300694681)
  ·
    refine ⟨33077606607187338225521011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44103475476249784300694681 33077606607187338225521011)
    ·
      refine ⟨49616409910781007338281517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33077606607187338225521011 49616409910781007338281517)
      ·
        refine ⟨18606153716542877751855569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49616409910781007338281517 18606153716542877751855569)
        ·
          refine ⟨13954615287407158313891677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18606153716542877751855569 13954615287407158313891677)
          ·
            refine ⟨5232980732777684367709379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13954615287407158313891677 5232980732777684367709379)
            ·
              refine ⟨7849471099166526551564069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5232980732777684367709379 7849471099166526551564069)
              ·
                refine ⟨1471775831093723728418263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7849471099166526551564069 1471775831093723728418263)
                ·
                  refine ⟨2207663746640585592627395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471775831093723728418263 2207663746640585592627395)
                  ·
                    refine ⟨3311495619960878388941093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2207663746640585592627395 3311495619960878388941093)
                    ·
                      refine ⟨620905428742664697926455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3311495619960878388941093 620905428742664697926455)
                      ·
                        rfl

theorem cell23_1209209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_1209209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209209 prefixEnd_1209209 := by exact prefixLift 1209209
  have htrace : WordTrace (prefixWord ++ tailWord_1209209) baseStart_1209209 baseEnd_1209209 := by
    simpa [prefixWord, tailWord_1209209, baseEnd_1209209] using wordTrace_append hprefix tailTrace_1209209
  have hstable : (prefixWord ++ tailWord_1209209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209209).length < 2 ^ (prefixWord ++ tailWord_1209209).sum := by decide
  have hdescent : baseEnd_1209209 < baseStart_1209209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209212 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_1209212 : Nat := 118140960795 + 1209212 * 2 ^ 59
def prefixEnd_1209212 : Nat := 4983230072969 + 3 ^ 40 * 1209212 * 2
def baseEnd_1209212 : Nat := 620906969184628186188941

theorem tailTrace_1209212 : CollatzResearch.WordTrace tailWord_1209212 prefixEnd_1209212 620906969184628186188941 := by
  unfold tailWord_1209212
  simp only [CollatzResearch.WordTrace]
  refine ⟨22051792447619457906526945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29402389930159277208702593 22051792447619457906526945)
  ·
    refine ⟨16538844335714593429895209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22051792447619457906526945 16538844335714593429895209)
    ·
      refine ⟨12404133251785945072421407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16538844335714593429895209 12404133251785945072421407)
      ·
        refine ⟨18606199877678917608632111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12404133251785945072421407 18606199877678917608632111)
        ·
          refine ⟨27909299816518376412948167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18606199877678917608632111 27909299816518376412948167)
          ·
            refine ⟨41863949724777564619422251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27909299816518376412948167 41863949724777564619422251)
            ·
              refine ⟨62795924587166346929133377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41863949724777564619422251 62795924587166346929133377)
              ·
                refine ⟨47096943440374760196850033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62795924587166346929133377 47096943440374760196850033)
                ·
                  refine ⟨35322707580281070147637525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47096943440374760196850033 35322707580281070147637525)
                  ·
                    refine ⟨1655751917825675163170509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35322707580281070147637525 1655751917825675163170509)
                    ·
                      refine ⟨620906969184628186188941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1655751917825675163170509 620906969184628186188941)
                      ·
                        rfl

theorem cell23_1209212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_1209212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209212 prefixEnd_1209212 := by exact prefixLift 1209212
  have htrace : WordTrace (prefixWord ++ tailWord_1209212) baseStart_1209212 baseEnd_1209212 := by
    simpa [prefixWord, tailWord_1209212, baseEnd_1209212] using wordTrace_append hprefix tailTrace_1209212
  have hstable : (prefixWord ++ tailWord_1209212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209212).length < 2 ^ (prefixWord ++ tailWord_1209212).sum := by decide
  have hdescent : baseEnd_1209212 < baseStart_1209212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209226 : List Nat := [3, 1, 2, 4, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1209226 : Nat := 118140960795 + 1209226 * 2 ^ 59
def prefixEnd_1209226 : Nat := 4983230072969 + 3 ^ 40 * 1209226 * 2
def baseEnd_1209226 : Nat := 620914157913791131413877

theorem tailTrace_1209226 : CollatzResearch.WordTrace tailWord_1209226 prefixEnd_1209226 620914157913791131413877 := by
  unfold tailWord_1209226
  simp only [CollatzResearch.WordTrace]
  refine ⟨11026023879297049051015883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29402730344792130802709021 11026023879297049051015883)
  ·
    refine ⟨16539035818945573576523825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11026023879297049051015883 16539035818945573576523825)
    ·
      refine ⟨12404276864209180182392869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16539035818945573576523825 12404276864209180182392869)
      ·
        refine ⟨2325801912039221284198663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12404276864209180182392869 2325801912039221284198663)
        ·
          refine ⟨3488702868058831926297995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325801912039221284198663 3488702868058831926297995)
          ·
            refine ⟨5233054302088247889446993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3488702868058831926297995 5233054302088247889446993)
            ·
              refine ⟨3924790726566185917085245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5233054302088247889446993 3924790726566185917085245)
              ·
                refine ⟨1471796522462319718906967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3924790726566185917085245 1471796522462319718906967)
                ·
                  refine ⟨2207694783693479578360451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471796522462319718906967 2207694783693479578360451)
                  ·
                    refine ⟨3311542175540219367540677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2207694783693479578360451 3311542175540219367540677)
                    ·
                      refine ⟨620914157913791131413877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3311542175540219367540677 620914157913791131413877)
                      ·
                        rfl

theorem cell23_1209226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1209226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209226 prefixEnd_1209226 := by exact prefixLift 1209226
  have htrace : WordTrace (prefixWord ++ tailWord_1209226) baseStart_1209226 baseEnd_1209226 := by
    simpa [prefixWord, tailWord_1209226, baseEnd_1209226] using wordTrace_append hprefix tailTrace_1209226
  have hstable : (prefixWord ++ tailWord_1209226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209226).length < 2 ^ (prefixWord ++ tailWord_1209226).sum := by decide
  have hdescent : baseEnd_1209226 < baseStart_1209226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209236 : List Nat := [2, 4, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1209236 : Nat := 118140960795 + 1209236 * 2 ^ 59
def prefixEnd_1209236 : Nat := 4983230072969 + 3 ^ 40 * 1209236 * 2
def baseEnd_1209236 : Nat := 206973097573445364096277

theorem tailTrace_1209236 : CollatzResearch.WordTrace tailWord_1209236 prefixEnd_1209236 206973097573445364096277 := by
  unfold tailWord_1209236
  simp only [CollatzResearch.WordTrace]
  refine ⟨22052230123575983955963781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29402973498101311941285041 22052230123575983955963781)
  ·
    refine ⟨4134793148170496991743209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22052230123575983955963781 4134793148170496991743209)
    ·
      refine ⟨3101094861127872743807407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4134793148170496991743209 3101094861127872743807407)
      ·
        refine ⟨4651642291691809115711111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101094861127872743807407 4651642291691809115711111)
        ·
          refine ⟨6977463437537713673566667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4651642291691809115711111 6977463437537713673566667)
          ·
            refine ⟨10466195156306570510350001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6977463437537713673566667 10466195156306570510350001)
            ·
              refine ⟨7849646367229927882762501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10466195156306570510350001 7849646367229927882762501)
              ·
                refine ⟨1471808693855611478017969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7849646367229927882762501 1471808693855611478017969)
                ·
                  refine ⟨1103856520391708608513477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1471808693855611478017969 1103856520391708608513477)
                  ·
                    refine ⟨206973097573445364096277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1103856520391708608513477 206973097573445364096277)
                    ·
                      rfl

theorem cell23_1209236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1209236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209236 prefixEnd_1209236 := by exact prefixLift 1209236
  have htrace : WordTrace (prefixWord ++ tailWord_1209236) baseStart_1209236 baseEnd_1209236 := by
    simpa [prefixWord, tailWord_1209236, baseEnd_1209236] using wordTrace_append hprefix tailTrace_1209236
  have hstable : (prefixWord ++ tailWord_1209236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209236).length < 2 ^ (prefixWord ++ tailWord_1209236).sum := by decide
  have hdescent : baseEnd_1209236 < baseStart_1209236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209249 : List Nat := [1, 2, 3, 4, 1, 2, 2, 8]
def baseStart_1209249 : Nat := 118140960795 + 1209249 * 2 ^ 59
def prefixEnd_1209249 : Nat := 4983230072969 + 3 ^ 40 * 1209249 * 2
def baseEnd_1209249 : Nat := 22997258072920168200973

theorem tailTrace_1209249 : CollatzResearch.WordTrace tailWord_1209249 prefixEnd_1209249 22997258072920168200973 := by
  unfold tailWord_1209249
  simp only [CollatzResearch.WordTrace]
  refine ⟨44104934396104871132150801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29403289597403247421433867 44104934396104871132150801)
  ·
    refine ⟨33078700797078653349113101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44104934396104871132150801 33078700797078653349113101)
    ·
      refine ⟨12404512798904495005917413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33078700797078653349113101 12404512798904495005917413)
      ·
        refine ⟨2325846149794592813609515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12404512798904495005917413 2325846149794592813609515)
        ·
          refine ⟨3488769224691889220414273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325846149794592813609515 3488769224691889220414273)
          ·
            refine ⟨2616576918518916915310705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3488769224691889220414273 2616576918518916915310705)
            ·
              refine ⟨1962432688889187686483029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2616576918518916915310705 1962432688889187686483029)
              ·
                refine ⟨22997258072920168200973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1962432688889187686483029 22997258072920168200973)
                ·
                  rfl

theorem cell23_1209249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 8].length) (baseStart_1209249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209249 prefixEnd_1209249 := by exact prefixLift 1209249
  have htrace : WordTrace (prefixWord ++ tailWord_1209249) baseStart_1209249 baseEnd_1209249 := by
    simpa [prefixWord, tailWord_1209249, baseEnd_1209249] using wordTrace_append hprefix tailTrace_1209249
  have hstable : (prefixWord ++ tailWord_1209249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209249).length < 2 ^ (prefixWord ++ tailWord_1209249).sum := by decide
  have hdescent : baseEnd_1209249 < baseStart_1209249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209252 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_1209252 : Nat := 118140960795 + 1209252 * 2 ^ 59
def prefixEnd_1209252 : Nat := 4983230072969 + 3 ^ 40 * 1209252 * 2
def baseEnd_1209252 : Nat := 620927508410808029688757

theorem tailTrace_1209252 : CollatzResearch.WordTrace tailWord_1209252 prefixEnd_1209252 620927508410808029688757 := by
  unfold tailWord_1209252
  simp only [CollatzResearch.WordTrace]
  refine ⟨22052521907547001322255005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29403362543396001763006673 22052521907547001322255005)
  ·
    refine ⟨8269695715330125495845627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22052521907547001322255005 8269695715330125495845627)
    ·
      refine ⟨12404543572995188243768441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8269695715330125495845627 12404543572995188243768441)
      ·
        refine ⟨9303407679746391182826331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12404543572995188243768441 9303407679746391182826331)
        ·
          refine ⟨13955111519619586774239497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9303407679746391182826331 13955111519619586774239497)
          ·
            refine ⟨10466333639714690080679623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13955111519619586774239497 10466333639714690080679623)
            ·
              refine ⟨15699500459572035121019435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10466333639714690080679623 15699500459572035121019435)
              ·
                refine ⟨23549250689358052681529153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15699500459572035121019435 23549250689358052681529153)
                ·
                  refine ⟨17661938017018539511146865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23549250689358052681529153 17661938017018539511146865)
                  ·
                    refine ⟨13246453512763904633360149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17661938017018539511146865 13246453512763904633360149)
                    ·
                      refine ⟨620927508410808029688757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13246453512763904633360149 620927508410808029688757)
                      ·
                        rfl

theorem cell23_1209252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_1209252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209252 prefixEnd_1209252 := by exact prefixLift 1209252
  have htrace : WordTrace (prefixWord ++ tailWord_1209252) baseStart_1209252 baseEnd_1209252 := by
    simpa [prefixWord, tailWord_1209252, baseEnd_1209252] using wordTrace_append hprefix tailTrace_1209252
  have hstable : (prefixWord ++ tailWord_1209252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209252).length < 2 ^ (prefixWord ++ tailWord_1209252).sum := by decide
  have hdescent : baseEnd_1209252 < baseStart_1209252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209270 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1209270 : Nat := 118140960795 + 1209270 * 2 ^ 59
def prefixEnd_1209270 : Nat := 4983230072969 + 3 ^ 40 * 1209270 * 2
def baseEnd_1209270 : Nat := 206978917020862986421225

theorem tailTrace_1209270 : CollatzResearch.WordTrace tailWord_1209270 prefixEnd_1209270 206978917020862986421225 := by
  unfold tailWord_1209270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2756606270564299482416579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29403800219352527812443509 2756606270564299482416579)
  ·
    refine ⟨4134909405846449223624869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2756606270564299482416579 4134909405846449223624869)
    ·
      refine ⟨775295513596209229429663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4134909405846449223624869 775295513596209229429663)
      ·
        refine ⟨1162943270394313844144495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 775295513596209229429663 1162943270394313844144495)
        ·
          refine ⟨1744414905591470766216743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162943270394313844144495 1744414905591470766216743)
          ·
            refine ⟨2616622358387206149325115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1744414905591470766216743 2616622358387206149325115)
            ·
              refine ⟨3924933537580809223987673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616622358387206149325115 3924933537580809223987673)
              ·
                refine ⟨2943700153185606917990755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3924933537580809223987673 2943700153185606917990755)
                ·
                  refine ⟨4415550229778410376986133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943700153185606917990755 4415550229778410376986133)
                  ·
                    refine ⟨206978917020862986421225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4415550229778410376986133 206978917020862986421225)
                    ·
                      rfl

theorem cell23_1209270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1209270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209270 prefixEnd_1209270 := by exact prefixLift 1209270
  have htrace : WordTrace (prefixWord ++ tailWord_1209270) baseStart_1209270 baseEnd_1209270 := by
    simpa [prefixWord, tailWord_1209270, baseEnd_1209270] using wordTrace_append hprefix tailTrace_1209270
  have hstable : (prefixWord ++ tailWord_1209270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209270).length < 2 ^ (prefixWord ++ tailWord_1209270).sum := by decide
  have hdescent : baseEnd_1209270 < baseStart_1209270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209309 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1209309 : Nat := 118140960795 + 1209309 * 2 ^ 59
def prefixEnd_1209309 : Nat := 4983230072969 + 3 ^ 40 * 1209309 * 2
def baseEnd_1209309 : Nat := 206985592269371435558665

theorem tailTrace_1209309 : CollatzResearch.WordTrace tailWord_1209309 prefixEnd_1209309 206985592269371435558665 := by
  unfold tailWord_1209309
  simp only [CollatzResearch.WordTrace]
  refine ⟨44107122775887501379334981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29404748517258334252889987 44107122775887501379334981)
  ·
    refine ⟨8270085520478906508625309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44107122775887501379334981 8270085520478906508625309)
    ·
      refine ⟨3101282070179589940734491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8270085520478906508625309 3101282070179589940734491)
      ·
        refine ⟨4651923105269384911101737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101282070179589940734491 4651923105269384911101737)
        ·
          refine ⟨3488942328952038683326303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4651923105269384911101737 3488942328952038683326303)
          ·
            refine ⟨5233413493428058024989455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3488942328952038683326303 5233413493428058024989455)
            ·
              refine ⟨7850120240142087037484183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5233413493428058024989455 7850120240142087037484183)
              ·
                refine ⟨11775180360213130556226275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7850120240142087037484183 11775180360213130556226275)
                ·
                  refine ⟨17662770540319695834339413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11775180360213130556226275 17662770540319695834339413)
                  ·
                    refine ⟨206985592269371435558665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17662770540319695834339413 206985592269371435558665)
                    ·
                      rfl

theorem cell23_1209309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1209309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209309 prefixEnd_1209309 := by exact prefixLift 1209309
  have htrace : WordTrace (prefixWord ++ tailWord_1209309) baseStart_1209309 baseEnd_1209309 := by
    simpa [prefixWord, tailWord_1209309, baseEnd_1209309] using wordTrace_append hprefix tailTrace_1209309
  have hstable : (prefixWord ++ tailWord_1209309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209309).length < 2 ^ (prefixWord ++ tailWord_1209309).sum := by decide
  have hdescent : baseEnd_1209309 < baseStart_1209309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209349 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 4, 3, 3]
def baseStart_1209349 : Nat := 118140960795 + 1209349 * 2 ^ 59
def prefixEnd_1209349 : Nat := 4983230072969 + 3 ^ 40 * 1209349 * 2
def baseEnd_1209349 : Nat := 620977316034294150175811

theorem tailTrace_1209349 : CollatzResearch.WordTrace tailWord_1209349 prefixEnd_1209349 620977316034294150175811 := by
  unfold tailWord_1209349
  simp only [CollatzResearch.WordTrace]
  refine ⟨44108581695742588210791101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29405721130495058807194067 44108581695742588210791101)
  ·
    refine ⟨16540718135903470579046663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44108581695742588210791101 16540718135903470579046663)
    ·
      refine ⟨24811077203855205868569995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16540718135903470579046663 24811077203855205868569995)
      ·
        refine ⟨37216615805782808802854993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24811077203855205868569995 37216615805782808802854993)
        ·
          refine ⟨27912461854337106602141245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37216615805782808802854993 27912461854337106602141245)
          ·
            refine ⟨10467173195376414975802967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27912461854337106602141245 10467173195376414975802967)
            ·
              refine ⟨15700759793064622463704451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10467173195376414975802967 15700759793064622463704451)
              ·
                refine ⟨23551139689596933695556677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15700759793064622463704451 23551139689596933695556677)
                ·
                  refine ⟨4415838691799425067916877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23551139689596933695556677 4415838691799425067916877)
                  ·
                    refine ⟨1655939509424784400468829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4415838691799425067916877 1655939509424784400468829)
                    ·
                      refine ⟨620977316034294150175811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1655939509424784400468829 620977316034294150175811)
                      ·
                        rfl

theorem cell23_1209349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_1209349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209349 prefixEnd_1209349 := by exact prefixLift 1209349
  have htrace : WordTrace (prefixWord ++ tailWord_1209349) baseStart_1209349 baseEnd_1209349 := by
    simpa [prefixWord, tailWord_1209349, baseEnd_1209349] using wordTrace_append hprefix tailTrace_1209349
  have hstable : (prefixWord ++ tailWord_1209349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209349).length < 2 ^ (prefixWord ++ tailWord_1209349).sum := by decide
  have hdescent : baseEnd_1209349 < baseStart_1209349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209356 : List Nat := [2, 2, 1, 2, 3, 2, 2, 4, 5]
def baseStart_1209356 : Nat := 118140960795 + 1209356 * 2 ^ 59
def prefixEnd_1209356 : Nat := 4983230072969 + 3 ^ 40 * 1209356 * 2
def baseEnd_1209356 : Nat := 68997878933208402532031

theorem tailTrace_1209356 : CollatzResearch.WordTrace tailWord_1209356 prefixEnd_1209356 68997878933208402532031 := by
  unfold tailWord_1209356
  simp only [CollatzResearch.WordTrace]
  refine ⟨22054418503358614203147961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29405891337811485604197281 22054418503358614203147961)
  ·
    refine ⟨16540813877518960652360971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22054418503358614203147961 16540813877518960652360971)
    ·
      refine ⟨24811220816278440978541457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16540813877518960652360971 24811220816278440978541457)
      ·
        refine ⟨18608415612208830733906093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24811220816278440978541457 18608415612208830733906093)
        ·
          refine ⟨6978155854578311525214785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18608415612208830733906093 6978155854578311525214785)
          ·
            refine ⟨5233616890933733643911089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6978155854578311525214785 5233616890933733643911089)
            ·
              refine ⟨3925212668200300232933317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5233616890933733643911089 3925212668200300232933317)
              ·
                refine ⟨735977375287556293674997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3925212668200300232933317 735977375287556293674997)
                ·
                  refine ⟨68997878933208402532031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 735977375287556293674997 68997878933208402532031)
                  ·
                    rfl

theorem cell23_1209356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 5].length) (baseStart_1209356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209356 prefixEnd_1209356 := by exact prefixLift 1209356
  have htrace : WordTrace (prefixWord ++ tailWord_1209356) baseStart_1209356 baseEnd_1209356 := by
    simpa [prefixWord, tailWord_1209356, baseEnd_1209356] using wordTrace_append hprefix tailTrace_1209356
  have hstable : (prefixWord ++ tailWord_1209356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209356).length < 2 ^ (prefixWord ++ tailWord_1209356).sum := by decide
  have hdescent : baseEnd_1209356 < baseStart_1209356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209367 : List Nat := [1, 1, 3, 5, 1, 2, 3, 1, 2, 2, 2]
def baseStart_1209367 : Nat := 118140960795 + 1209367 * 2 ^ 59
def prefixEnd_1209367 : Nat := 4983230072969 + 3 ^ 40 * 1209367 * 2
def baseEnd_1209367 : Nat := 620986558686075079750729

theorem tailTrace_1209367 : CollatzResearch.WordTrace tailWord_1209367 prefixEnd_1209367 620986558686075079750729 := by
  unfold tailWord_1209367
  simp only [CollatzResearch.WordTrace]
  refine ⟨44109238209677377284946355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29406158806451584856630903 44109238209677377284946355)
  ·
    refine ⟨66163857314516065927419533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44109238209677377284946355 66163857314516065927419533)
    ·
      refine ⟨24811446492943524722782325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66163857314516065927419533 24811446492943524722782325)
      ·
        refine ⟨2326073108713455442760843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24811446492943524722782325 2326073108713455442760843)
        ·
          refine ⟨3489109663070183164141265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326073108713455442760843 3489109663070183164141265)
          ·
            refine ⟨2616832247302637373105949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3489109663070183164141265 2616832247302637373105949)
            ·
              refine ⟨981312092738489014914731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2616832247302637373105949 981312092738489014914731)
              ·
                refine ⟨1471968139107733522372097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981312092738489014914731 1471968139107733522372097)
                ·
                  refine ⟨1103976104330800141779073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1471968139107733522372097 1103976104330800141779073)
                  ·
                    refine ⟨827982078248100106334305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1103976104330800141779073 827982078248100106334305)
                    ·
                      refine ⟨620986558686075079750729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 827982078248100106334305 620986558686075079750729)
                      ·
                        rfl

theorem cell23_1209367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_1209367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209367 prefixEnd_1209367 := by exact prefixLift 1209367
  have htrace : WordTrace (prefixWord ++ tailWord_1209367) baseStart_1209367 baseEnd_1209367 := by
    simpa [prefixWord, tailWord_1209367, baseEnd_1209367] using wordTrace_append hprefix tailTrace_1209367
  have hstable : (prefixWord ++ tailWord_1209367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209367).length < 2 ^ (prefixWord ++ tailWord_1209367).sum := by decide
  have hdescent : baseEnd_1209367 < baseStart_1209367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209476 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_1209476 : Nat := 118140960795 + 1209476 * 2 ^ 59
def prefixEnd_1209476 : Nat := 4983230072969 + 3 ^ 40 * 1209476 * 2
def baseEnd_1209476 : Nat := 207014176025805051095909

theorem tailTrace_1209476 : CollatzResearch.WordTrace tailWord_1209476 prefixEnd_1209476 207014176025805051095909 := by
  unfold tailWord_1209476
  simp only [CollatzResearch.WordTrace]
  refine ⟨22056606883141244450332141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29408809177521659267109521 22056606883141244450332141)
  ·
    refine ⟨8271227581177966668874553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22056606883141244450332141 8271227581177966668874553)
    ·
      refine ⟨6203420685883475001655915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8271227581177966668874553 6203420685883475001655915)
      ·
        refine ⟨9305131028825212502483873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6203420685883475001655915 9305131028825212502483873)
        ·
          refine ⟨6978848271618909376862905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9305131028825212502483873 6978848271618909376862905)
          ·
            refine ⟨5234136203714182032647179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6978848271618909376862905 5234136203714182032647179)
            ·
              refine ⟨7851204305571273048970769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5234136203714182032647179 7851204305571273048970769)
              ·
                refine ⟨5888403229178454786728077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7851204305571273048970769 5888403229178454786728077)
                ·
                  refine ⟨2208151210941920545023029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5888403229178454786728077 2208151210941920545023029)
                  ·
                    refine ⟨207014176025805051095909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2208151210941920545023029 207014176025805051095909)
                    ·
                      rfl

theorem cell23_1209476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_1209476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209476 prefixEnd_1209476 := by exact prefixLift 1209476
  have htrace : WordTrace (prefixWord ++ tailWord_1209476) baseStart_1209476 baseEnd_1209476 := by
    simpa [prefixWord, tailWord_1209476, baseEnd_1209476] using wordTrace_append hprefix tailTrace_1209476
  have hstable : (prefixWord ++ tailWord_1209476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209476).length < 2 ^ (prefixWord ++ tailWord_1209476).sum := by decide
  have hdescent : baseEnd_1209476 < baseStart_1209476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209490 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_1209490 : Nat := 118140960795 + 1209490 * 2 ^ 59
def prefixEnd_1209490 : Nat := 4983230072969 + 3 ^ 40 * 1209490 * 2
def baseEnd_1209490 : Nat := 621049716806578098512663

theorem tailTrace_1209490 : CollatzResearch.WordTrace tailWord_1209490 prefixEnd_1209490 621049716806578098512663 := by
  unfold tailWord_1209490
  simp only [CollatzResearch.WordTrace]
  refine ⟨11028431097057942322918481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29409149592154512861115949 11028431097057942322918481)
  ·
    refine ⟨8271323322793456742188861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11028431097057942322918481 8271323322793456742188861)
    ·
      refine ⟨3101746246047546278320823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8271323322793456742188861 3101746246047546278320823)
      ·
        refine ⟨4652619369071319417481235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101746246047546278320823 4652619369071319417481235)
        ·
          refine ⟨6978929053606979126221853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4652619369071319417481235 6978929053606979126221853)
          ·
            refine ⟨2617098395102617172333195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6978929053606979126221853 2617098395102617172333195)
            ·
              refine ⟨3925647592653925758499793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2617098395102617172333195 3925647592653925758499793)
              ·
                refine ⟨2944235694490444318874845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3925647592653925758499793 2944235694490444318874845)
                ·
                  refine ⟨1104088385433916619578067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2944235694490444318874845 1104088385433916619578067)
                  ·
                    refine ⟨1656132578150874929367101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1104088385433916619578067 1656132578150874929367101)
                    ·
                      refine ⟨621049716806578098512663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1656132578150874929367101 621049716806578098512663)
                      ·
                        rfl

theorem cell23_1209490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_1209490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209490 prefixEnd_1209490 := by exact prefixLift 1209490
  have htrace : WordTrace (prefixWord ++ tailWord_1209490) baseStart_1209490 baseEnd_1209490 := by
    simpa [prefixWord, tailWord_1209490, baseEnd_1209490] using wordTrace_append hprefix tailTrace_1209490
  have hstable : (prefixWord ++ tailWord_1209490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209490).length < 2 ^ (prefixWord ++ tailWord_1209490).sum := by decide
  have hdescent : baseEnd_1209490 < baseStart_1209490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209500 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_1209500 : Nat := 118140960795 + 1209500 * 2 ^ 59
def prefixEnd_1209500 : Nat := 4983230072969 + 3 ^ 40 * 1209500 * 2
def baseEnd_1209500 : Nat := 621054851613123059387617

theorem tailTrace_1209500 : CollatzResearch.WordTrace tailWord_1209500 prefixEnd_1209500 621054851613123059387617 := by
  unfold tailWord_1209500
  simp only [CollatzResearch.WordTrace]
  refine ⟨22057044559097770499768977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29409392745463693999691969 22057044559097770499768977)
  ·
    refine ⟨16542783419323327874826733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22057044559097770499768977 16542783419323327874826733)
    ·
      refine ⟨6203543782246247953060025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16542783419323327874826733 6203543782246247953060025)
      ·
        refine ⟨4652657836684685964795019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6203543782246247953060025 4652657836684685964795019)
        ·
          refine ⟨6978986755027028947192529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4652657836684685964795019 6978986755027028947192529)
          ·
            refine ⟨5234240066270271710394397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6978986755027028947192529 5234240066270271710394397)
            ·
              refine ⟨1962840024851351891397899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5234240066270271710394397 1962840024851351891397899)
              ·
                refine ⟨2944260037277027837096849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1962840024851351891397899 2944260037277027837096849)
                ·
                  refine ⟨2208195027957770877822637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2944260037277027837096849 2208195027957770877822637)
                  ·
                    refine ⟨828073135484164079183489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2208195027957770877822637 828073135484164079183489)
                    ·
                      refine ⟨621054851613123059387617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 828073135484164079183489 621054851613123059387617)
                      ·
                        rfl

theorem cell23_1209500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_1209500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209500 prefixEnd_1209500 := by exact prefixLift 1209500
  have htrace : WordTrace (prefixWord ++ tailWord_1209500) baseStart_1209500 baseEnd_1209500 := by
    simpa [prefixWord, tailWord_1209500, baseEnd_1209500] using wordTrace_append hprefix tailTrace_1209500
  have hstable : (prefixWord ++ tailWord_1209500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209500).length < 2 ^ (prefixWord ++ tailWord_1209500).sum := by decide
  have hdescent : baseEnd_1209500 < baseStart_1209500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209516 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 3]
def baseStart_1209516 : Nat := 118140960795 + 1209516 * 2 ^ 59
def prefixEnd_1209516 : Nat := 4983230072969 + 3 ^ 40 * 1209516 * 2
def baseEnd_1209516 : Nat := 621063067303594996787543

theorem tailTrace_1209516 : CollatzResearch.WordTrace tailWord_1209516 prefixEnd_1209516 621063067303594996787543 := by
  unfold tailWord_1209516
  simp only [CollatzResearch.WordTrace]
  refine ⟨22057336343068787866060201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29409781790758383821413601 22057336343068787866060201)
  ·
    refine ⟨16543002257301590899545151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22057336343068787866060201 16543002257301590899545151)
    ·
      refine ⟨24814503385952386349317727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16543002257301590899545151 24814503385952386349317727)
      ·
        refine ⟨37221755078928579523976591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24814503385952386349317727 37221755078928579523976591)
        ·
          refine ⟨55832632618392869285964887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37221755078928579523976591 55832632618392869285964887)
          ·
            refine ⟨83748948927589303928947331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55832632618392869285964887 83748948927589303928947331)
            ·
              refine ⟨125623423391383955893420997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83748948927589303928947331 125623423391383955893420997)
              ·
                refine ⟨23554391885884491730016437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125623423391383955893420997 23554391885884491730016437)
                ·
                  refine ⟨2208224239301671099689041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23554391885884491730016437 2208224239301671099689041)
                  ·
                    refine ⟨1656168179476253324766781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2208224239301671099689041 1656168179476253324766781)
                    ·
                      refine ⟨621063067303594996787543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1656168179476253324766781 621063067303594996787543)
                      ·
                        rfl

theorem cell23_1209516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_1209516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209516 prefixEnd_1209516 := by exact prefixLift 1209516
  have htrace : WordTrace (prefixWord ++ tailWord_1209516) baseStart_1209516 baseEnd_1209516 := by
    simpa [prefixWord, tailWord_1209516, baseEnd_1209516] using wordTrace_append hprefix tailTrace_1209516
  have hstable : (prefixWord ++ tailWord_1209516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209516).length < 2 ^ (prefixWord ++ tailWord_1209516).sum := by decide
  have hdescent : baseEnd_1209516 < baseStart_1209516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209523 : List Nat := [1, 1, 1, 2, 3, 2, 5, 2, 2, 4]
def baseStart_1209523 : Nat := 118140960795 + 1209523 * 2 ^ 59
def prefixEnd_1209523 : Nat := 4983230072969 + 3 ^ 40 * 1209523 * 2
def baseEnd_1209523 : Nat := 207022220556058823133337

theorem tailTrace_1209523 : CollatzResearch.WordTrace tailWord_1209523 prefixEnd_1209523 207022220556058823133337 := by
  unfold tailWord_1209523
  simp only [CollatzResearch.WordTrace]
  refine ⟨44114927997112215927625223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29409951998074810618416815 44114927997112215927625223)
  ·
    refine ⟨66172391995668323891437835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44114927997112215927625223 66172391995668323891437835)
    ·
      refine ⟨99258587993502485837156753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66172391995668323891437835 99258587993502485837156753)
      ·
        refine ⟨74443940995126864377867565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99258587993502485837156753 74443940995126864377867565)
        ·
          refine ⟨27916477873172574141700337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74443940995126864377867565 27916477873172574141700337)
          ·
            refine ⟨20937358404879430606275253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27916477873172574141700337 20937358404879430606275253)
            ·
              refine ⟨1962877350457446619338305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20937358404879430606275253 1962877350457446619338305)
              ·
                refine ⟨1472158012843084964503729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1962877350457446619338305 1472158012843084964503729)
                ·
                  refine ⟨1104118509632313723377797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1472158012843084964503729 1104118509632313723377797)
                  ·
                    refine ⟨207022220556058823133337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1104118509632313723377797 207022220556058823133337)
                    ·
                      rfl

theorem cell23_1209523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 4].length) (baseStart_1209523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209523 prefixEnd_1209523 := by exact prefixLift 1209523
  have htrace : WordTrace (prefixWord ++ tailWord_1209523) baseStart_1209523 baseEnd_1209523 := by
    simpa [prefixWord, tailWord_1209523, baseEnd_1209523] using wordTrace_append hprefix tailTrace_1209523
  have hstable : (prefixWord ++ tailWord_1209523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209523).length < 2 ^ (prefixWord ++ tailWord_1209523).sum := by decide
  have hdescent : baseEnd_1209523 < baseStart_1209523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209539 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 6]
def baseStart_1209539 : Nat := 118140960795 + 1209539 * 2 ^ 59
def prefixEnd_1209539 : Nat := 4983230072969 + 3 ^ 40 * 1209539 * 2
def baseEnd_1209539 : Nat := 621074877358648406799937

theorem tailTrace_1209539 : CollatzResearch.WordTrace tailWord_1209539 prefixEnd_1209539 621074877358648406799937 := by
  unfold tailWord_1209539
  simp only [CollatzResearch.WordTrace]
  refine ⟨44115511565054250660207671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29410341043369500440138447 44115511565054250660207671)
  ·
    refine ⟨66173267347581375990311507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44115511565054250660207671 66173267347581375990311507)
    ·
      refine ⟨99259901021372063985467261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66173267347581375990311507 99259901021372063985467261)
      ·
        refine ⟨37222462883014523994550223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99259901021372063985467261 37222462883014523994550223)
        ·
          refine ⟨55833694324521785991825335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37222462883014523994550223 55833694324521785991825335)
          ·
            refine ⟨83750541486782678987738003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55833694324521785991825335 83750541486782678987738003)
            ·
              refine ⟨125625812230174018481607005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83750541486782678987738003 125625812230174018481607005)
              ·
                refine ⟨47109679586315256930602627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125625812230174018481607005 47109679586315256930602627)
                ·
                  refine ⟨70664519379472885395903941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47109679586315256930602627 70664519379472885395903941)
                  ·
                    refine ⟨13249597383651166011731989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70664519379472885395903941 13249597383651166011731989)
                    ·
                      refine ⟨621074877358648406799937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13249597383651166011731989 621074877358648406799937)
                      ·
                        rfl

theorem cell23_1209539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_1209539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209539 prefixEnd_1209539 := by exact prefixLift 1209539
  have htrace : WordTrace (prefixWord ++ tailWord_1209539) baseStart_1209539 baseEnd_1209539 := by
    simpa [prefixWord, tailWord_1209539, baseEnd_1209539] using wordTrace_append hprefix tailTrace_1209539
  have hstable : (prefixWord ++ tailWord_1209539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209539).length < 2 ^ (prefixWord ++ tailWord_1209539).sum := by decide
  have hdescent : baseEnd_1209539 < baseStart_1209539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209540 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_1209540 : Nat := 118140960795 + 1209540 * 2 ^ 59
def prefixEnd_1209540 : Nat := 4983230072969 + 3 ^ 40 * 1209540 * 2
def baseEnd_1209540 : Nat := 207025130279767634295811

theorem tailTrace_1209540 : CollatzResearch.WordTrace tailWord_1209540 prefixEnd_1209540 207025130279767634295811 := by
  unfold tailWord_1209540
  simp only [CollatzResearch.WordTrace]
  refine ⟨22057774019025313915497037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29410365358700418553996049 22057774019025313915497037)
  ·
    refine ⟨8271665257134492718311389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22057774019025313915497037 8271665257134492718311389)
    ·
      refine ⟨3101874471425434769366771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8271665257134492718311389 3101874471425434769366771)
      ·
        refine ⟨4652811707138152154050157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101874471425434769366771 4652811707138152154050157)
        ·
          refine ⟨1744804390176807057768809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4652811707138152154050157 1744804390176807057768809)
          ·
            refine ⟨1308603292632605293326607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1744804390176807057768809 1308603292632605293326607)
            ·
              refine ⟨1962904938948907939989911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308603292632605293326607 1962904938948907939989911)
              ·
                refine ⟨2944357408423361909984867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1962904938948907939989911 2944357408423361909984867)
                ·
                  refine ⟨4416536112635042864977301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2944357408423361909984867 4416536112635042864977301)
                  ·
                    refine ⟨207025130279767634295811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4416536112635042864977301 207025130279767634295811)
                    ·
                      rfl

theorem cell23_1209540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_1209540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209540 prefixEnd_1209540 := by exact prefixLift 1209540
  have htrace : WordTrace (prefixWord ++ tailWord_1209540) baseStart_1209540 baseEnd_1209540 := by
    simpa [prefixWord, tailWord_1209540, baseEnd_1209540] using wordTrace_append hprefix tailTrace_1209540
  have hstable : (prefixWord ++ tailWord_1209540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209540).length < 2 ^ (prefixWord ++ tailWord_1209540).sum := by decide
  have hdescent : baseEnd_1209540 < baseStart_1209540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209558 : List Nat := [5, 2, 1, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_1209558 : Nat := 118140960795 + 1209558 * 2 ^ 59
def prefixEnd_1209558 : Nat := 4983230072969 + 3 ^ 40 * 1209558 * 2
def baseEnd_1209558 : Nat := 621084633491083832462351

theorem tailTrace_1209558 : CollatzResearch.WordTrace tailWord_1209558 prefixEnd_1209558 621084633491083832462351 := by
  unfold tailWord_1209558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2757262784499088556571833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29410803034656944603432885 2757262784499088556571833)
  ·
    refine ⟨2067947088374316417428875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2757262784499088556571833 2067947088374316417428875)
    ·
      refine ⟨3101920632561474626143313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2067947088374316417428875 3101920632561474626143313)
      ·
        refine ⟨2326440474421105969607485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3101920632561474626143313 2326440474421105969607485)
        ·
          refine ⟨872415177907914738602807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2326440474421105969607485 872415177907914738602807)
          ·
            refine ⟨1308622766861872107904211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872415177907914738602807 1308622766861872107904211)
            ·
              refine ⟨1962934150292808161856317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1308622766861872107904211 1962934150292808161856317)
              ·
                refine ⟨736100306359803060696119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1962934150292808161856317 736100306359803060696119)
                ·
                  refine ⟨1104150459539704591044179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736100306359803060696119 1104150459539704591044179)
                  ·
                    refine ⟨1656225689309556886566269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1104150459539704591044179 1656225689309556886566269)
                    ·
                      refine ⟨621084633491083832462351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1656225689309556886566269 621084633491083832462351)
                      ·
                        rfl

theorem cell23_1209558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_1209558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209558 prefixEnd_1209558 := by exact prefixLift 1209558
  have htrace : WordTrace (prefixWord ++ tailWord_1209558) baseStart_1209558 baseEnd_1209558 := by
    simpa [prefixWord, tailWord_1209558, baseEnd_1209558] using wordTrace_append hprefix tailTrace_1209558
  have hstable : (prefixWord ++ tailWord_1209558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209558).length < 2 ^ (prefixWord ++ tailWord_1209558).sum := by decide
  have hdescent : baseEnd_1209558 < baseStart_1209558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209576 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1209576 : Nat := 118140960795 + 1209576 * 2 ^ 59
def prefixEnd_1209576 : Nat := 4983230072969 + 3 ^ 40 * 1209576 * 2
def baseEnd_1209576 : Nat := 621093876142864762037267

theorem tailTrace_1209576 : CollatzResearch.WordTrace tailWord_1209576 prefixEnd_1209576 621093876142864762037267 := by
  unfold tailWord_1209576
  simp only [CollatzResearch.WordTrace]
  refine ⟨22058430532960102989652291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29411240710613470652869721 22058430532960102989652291)
  ·
    refine ⟨33087645799440154484478437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22058430532960102989652291 33087645799440154484478437)
    ·
      refine ⟨6203933587395028965839707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33087645799440154484478437 6203933587395028965839707)
      ·
        refine ⟨9305900381092543448759561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6203933587395028965839707 9305900381092543448759561)
        ·
          refine ⟨6979425285819407586569671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9305900381092543448759561 6979425285819407586569671)
          ·
            refine ⟨10469137928729111379854507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6979425285819407586569671 10469137928729111379854507)
            ·
              refine ⟨15703706893093667069781761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10469137928729111379854507 15703706893093667069781761)
              ·
                refine ⟨11777780169820250302336321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15703706893093667069781761 11777780169820250302336321)
                ·
                  refine ⟨8833335127365187726752241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11777780169820250302336321 8833335127365187726752241)
                  ·
                    refine ⟨6625001345523890795064181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8833335127365187726752241 6625001345523890795064181)
                    ·
                      refine ⟨621093876142864762037267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6625001345523890795064181 621093876142864762037267)
                      ·
                        rfl

theorem cell23_1209576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1209576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209576 prefixEnd_1209576 := by exact prefixLift 1209576
  have htrace : WordTrace (prefixWord ++ tailWord_1209576) baseStart_1209576 baseEnd_1209576 := by
    simpa [prefixWord, tailWord_1209576, baseEnd_1209576] using wordTrace_append hprefix tailTrace_1209576
  have hstable : (prefixWord ++ tailWord_1209576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209576).length < 2 ^ (prefixWord ++ tailWord_1209576).sum := by decide
  have hdescent : baseEnd_1209576 < baseStart_1209576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209581 : List Nat := [1, 5, 1, 2, 2, 2, 3, 2, 1, 2, 2]
def baseStart_1209581 : Nat := 118140960795 + 1209581 * 2 ^ 59
def prefixEnd_1209581 : Nat := 4983230072969 + 3 ^ 40 * 1209581 * 2
def baseEnd_1209581 : Nat := 621096443546137242474745

theorem tailTrace_1209581 : CollatzResearch.WordTrace tailWord_1209581 prefixEnd_1209581 621096443546137242474745 := by
  unfold tailWord_1209581
  simp only [CollatzResearch.WordTrace]
  refine ⟨44117043430902091833236597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29411362287268061222157731 44117043430902091833236597)
  ·
    refine ⟨4135972821647071109365931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44117043430902091833236597 4135972821647071109365931)
    ·
      refine ⟨6203959232470606664048897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4135972821647071109365931 6203959232470606664048897)
      ·
        refine ⟨4652969424352954998036673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6203959232470606664048897 4652969424352954998036673)
        ·
          refine ⟨3489727068264716248527505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4652969424352954998036673 3489727068264716248527505)
          ·
            refine ⟨2617295301198537186395629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3489727068264716248527505 2617295301198537186395629)
            ·
              refine ⟨981485737949451444898361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2617295301198537186395629 981485737949451444898361)
              ·
                refine ⟨736114303462088583673771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 981485737949451444898361 736114303462088583673771)
                ·
                  refine ⟨1104171455193132875510657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736114303462088583673771 1104171455193132875510657)
                  ·
                    refine ⟨828128591394849656632993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1104171455193132875510657 828128591394849656632993)
                    ·
                      refine ⟨621096443546137242474745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 828128591394849656632993 621096443546137242474745)
                      ·
                        rfl

theorem cell23_1209581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_1209581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209581 prefixEnd_1209581 := by exact prefixLift 1209581
  have htrace : WordTrace (prefixWord ++ tailWord_1209581) baseStart_1209581 baseEnd_1209581 := by
    simpa [prefixWord, tailWord_1209581, baseEnd_1209581] using wordTrace_append hprefix tailTrace_1209581
  have hstable : (prefixWord ++ tailWord_1209581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209581).length < 2 ^ (prefixWord ++ tailWord_1209581).sum := by decide
  have hdescent : baseEnd_1209581 < baseStart_1209581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209590 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_1209590 : Nat := 118140960795 + 1209590 * 2 ^ 59
def prefixEnd_1209590 : Nat := 4983230072969 + 3 ^ 40 * 1209590 * 2
def baseEnd_1209590 : Nat := 621101064872027707262203

theorem tailTrace_1209590 : CollatzResearch.WordTrace tailWord_1209590 prefixEnd_1209590 621101064872027707262203 := by
  unfold tailWord_1209590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2757335730491842898144639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29411581125246324246876149 2757335730491842898144639)
  ·
    refine ⟨4136003595737764347216959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2757335730491842898144639 4136003595737764347216959)
    ·
      refine ⟨6204005393606646520825439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4136003595737764347216959 6204005393606646520825439)
      ·
        refine ⟨9306008090409969781238159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6204005393606646520825439 9306008090409969781238159)
        ·
          refine ⟨13959012135614954671857239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9306008090409969781238159 13959012135614954671857239)
          ·
            refine ⟨20938518203422432007785859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13959012135614954671857239 20938518203422432007785859)
            ·
              refine ⟨31407777305133648011678789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20938518203422432007785859 31407777305133648011678789)
              ·
                refine ⟨5888958244712559002189773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31407777305133648011678789 5888958244712559002189773)
                ·
                  refine ⟨2208359341767209625821165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5888958244712559002189773 2208359341767209625821165)
                  ·
                    refine ⟨828134753162703609682937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2208359341767209625821165 828134753162703609682937)
                    ·
                      refine ⟨621101064872027707262203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 828134753162703609682937 621101064872027707262203)
                      ·
                        rfl

theorem cell23_1209590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_1209590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209590 prefixEnd_1209590 := by exact prefixLift 1209590
  have htrace : WordTrace (prefixWord ++ tailWord_1209590) baseStart_1209590 baseEnd_1209590 := by
    simpa [prefixWord, tailWord_1209590, baseEnd_1209590] using wordTrace_append hprefix tailTrace_1209590
  have hstable : (prefixWord ++ tailWord_1209590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209590).length < 2 ^ (prefixWord ++ tailWord_1209590).sum := by decide
  have hdescent : baseEnd_1209590 < baseStart_1209590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209637 : List Nat := [1, 3, 1, 2, 4, 1, 1, 4, 2, 2, 2]
def baseStart_1209637 : Nat := 118140960795 + 1209637 * 2 ^ 59
def prefixEnd_1209637 : Nat := 4983230072969 + 3 ^ 40 * 1209637 * 2
def baseEnd_1209637 : Nat := 621125198462789023374487

theorem tailTrace_1209637 : CollatzResearch.WordTrace tailWord_1209637 prefixEnd_1209637 621125198462789023374487 := by
  unfold tailWord_1209637
  simp only [CollatzResearch.WordTrace]
  refine ⟨44119085918699213397275165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29412723945799475598183443 44119085918699213397275165)
  ·
    refine ⟨16544657219512205023978187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44119085918699213397275165 16544657219512205023978187)
    ·
      refine ⟨24816985829268307535967281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16544657219512205023978187 24816985829268307535967281)
      ·
        refine ⟨18612739371951230651975461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24816985829268307535967281 18612739371951230651975461)
        ·
          refine ⟨3489888632240855747245399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18612739371951230651975461 3489888632240855747245399)
          ·
            refine ⟨5234832948361283620868099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489888632240855747245399 5234832948361283620868099)
            ·
              refine ⟨7852249422541925431302149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5234832948361283620868099 7852249422541925431302149)
              ·
                refine ⟨1472296766726611018369153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7852249422541925431302149 1472296766726611018369153)
                ·
                  refine ⟨1104222575044958263776865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1472296766726611018369153 1104222575044958263776865)
                  ·
                    refine ⟨828166931283718697832649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1104222575044958263776865 828166931283718697832649)
                    ·
                      refine ⟨621125198462789023374487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 828166931283718697832649 621125198462789023374487)
                      ·
                        rfl

theorem cell23_1209637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_1209637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209637 prefixEnd_1209637 := by exact prefixLift 1209637
  have htrace : WordTrace (prefixWord ++ tailWord_1209637) baseStart_1209637 baseEnd_1209637 := by
    simpa [prefixWord, tailWord_1209637, baseEnd_1209637] using wordTrace_append hprefix tailTrace_1209637
  have hstable : (prefixWord ++ tailWord_1209637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209637).length < 2 ^ (prefixWord ++ tailWord_1209637).sum := by decide
  have hdescent : baseEnd_1209637 < baseStart_1209637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209653 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_1209653 : Nat := 118140960795 + 1209653 * 2 ^ 59
def prefixEnd_1209653 : Nat := 4983230072969 + 3 ^ 40 * 1209653 * 2
def baseEnd_1209653 : Nat := 621133414153260960774413

theorem tailTrace_1209653 : CollatzResearch.WordTrace tailWord_1209653 prefixEnd_1209653 621133414153260960774413 := by
  unfold tailWord_1209653
  simp only [CollatzResearch.WordTrace]
  refine ⟨44119669486641248129857613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29413112991094165419905075 44119669486641248129857613)
  ·
    refine ⟨16544876057490468048696605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44119669486641248129857613 16544876057490468048696605)
    ·
      refine ⟨6204328521558925518261227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16544876057490468048696605 6204328521558925518261227)
      ·
        refine ⟨9306492782338388277391841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6204328521558925518261227 9306492782338388277391841)
        ·
          refine ⟨6979869586753791208043881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9306492782338388277391841 6979869586753791208043881)
          ·
            refine ⟨5234902190065343406032911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6979869586753791208043881 5234902190065343406032911)
            ·
              refine ⟨7852353285098015109049367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5234902190065343406032911 7852353285098015109049367)
              ·
                refine ⟨11778529927647022663574051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7852353285098015109049367 11778529927647022663574051)
                ·
                  refine ⟨17667794891470533995361077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11778529927647022663574051 17667794891470533995361077)
                  ·
                    refine ⟨1656355771075362562065101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17667794891470533995361077 1656355771075362562065101)
                    ·
                      refine ⟨621133414153260960774413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1656355771075362562065101 621133414153260960774413)
                      ·
                        rfl

theorem cell23_1209653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_1209653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209653 prefixEnd_1209653 := by exact prefixLift 1209653
  have htrace : WordTrace (prefixWord ++ tailWord_1209653) baseStart_1209653 baseEnd_1209653 := by
    simpa [prefixWord, tailWord_1209653, baseEnd_1209653] using wordTrace_append hprefix tailTrace_1209653
  have hstable : (prefixWord ++ tailWord_1209653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209653).length < 2 ^ (prefixWord ++ tailWord_1209653).sum := by decide
  have hdescent : baseEnd_1209653 < baseStart_1209653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209656 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 1, 7]
def baseStart_1209656 : Nat := 118140960795 + 1209656 * 2 ^ 59
def prefixEnd_1209656 : Nat := 4983230072969 + 3 ^ 40 * 1209656 * 2
def baseEnd_1209656 : Nat := 207044984865074816345633

theorem tailTrace_1209656 : CollatzResearch.WordTrace tailWord_1209656 prefixEnd_1209656 207044984865074816345633 := by
  unfold tailWord_1209656
  simp only [CollatzResearch.WordTrace]
  refine ⟨22059889452815189821108411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29413185937086919761477881 22059889452815189821108411)
  ·
    refine ⟨33089834179222784731662617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22059889452815189821108411 33089834179222784731662617)
    ·
      refine ⟨24817375634417088548746963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33089834179222784731662617 24817375634417088548746963)
      ·
        refine ⟨37226063451625632823120445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24817375634417088548746963 37226063451625632823120445)
        ·
          refine ⟨13959773794359612308670167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37226063451625632823120445 13959773794359612308670167)
          ·
            refine ⟨20939660691539418463005251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13959773794359612308670167 20939660691539418463005251)
            ·
              refine ⟨31409491037309127694507877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20939660691539418463005251 31409491037309127694507877)
              ·
                refine ⟨5889279569495461442720227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31409491037309127694507877 5889279569495461442720227)
                ·
                  refine ⟨8833919354243192164080341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5889279569495461442720227 8833919354243192164080341)
                  ·
                    refine ⟨207044984865074816345633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8833919354243192164080341 207044984865074816345633)
                    ·
                      rfl

theorem cell23_1209656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_1209656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209656 prefixEnd_1209656 := by exact prefixLift 1209656
  have htrace : WordTrace (prefixWord ++ tailWord_1209656) baseStart_1209656 baseEnd_1209656 := by
    simpa [prefixWord, tailWord_1209656, baseEnd_1209656] using wordTrace_append hprefix tailTrace_1209656
  have hstable : (prefixWord ++ tailWord_1209656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209656).length < 2 ^ (prefixWord ++ tailWord_1209656).sum := by decide
  have hdescent : baseEnd_1209656 < baseStart_1209656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209673 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 2, 5]
def baseStart_1209673 : Nat := 118140960795 + 1209673 * 2 ^ 59
def prefixEnd_1209673 : Nat := 4983230072969 + 3 ^ 40 * 1209673 * 2
def baseEnd_1209673 : Nat := 207047894588783627508107

theorem tailTrace_1209673 : CollatzResearch.WordTrace tailWord_1209673 prefixEnd_1209673 207047894588783627508107 := by
  unfold tailWord_1209673
  simp only [CollatzResearch.WordTrace]
  refine ⟨44120398946568791545585673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29413599297712527697057115 44120398946568791545585673)
  ·
    refine ⟨33090299209926593659189255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44120398946568791545585673 33090299209926593659189255)
    ·
      refine ⟨49635448814889890488783883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33090299209926593659189255 49635448814889890488783883)
      ·
        refine ⟨74453173222334835733175825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49635448814889890488783883 74453173222334835733175825)
        ·
          refine ⟨55839879916751126799881869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74453173222334835733175825 55839879916751126799881869)
          ·
            refine ⟨20939954968781672549955701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55839879916751126799881869 20939954968781672549955701)
            ·
              refine ⟨1963120778323281801558347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20939954968781672549955701 1963120778323281801558347)
              ·
                refine ⟨2944681167484922702337521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1963120778323281801558347 2944681167484922702337521)
                ·
                  refine ⟨2208510875613692026753141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2944681167484922702337521 2208510875613692026753141)
                  ·
                    refine ⟨207047894588783627508107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2208510875613692026753141 207047894588783627508107)
                    ·
                      rfl

theorem cell23_1209673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 5].length) (baseStart_1209673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209673 prefixEnd_1209673 := by exact prefixLift 1209673
  have htrace : WordTrace (prefixWord ++ tailWord_1209673) baseStart_1209673 baseEnd_1209673 := by
    simpa [prefixWord, tailWord_1209673, baseEnd_1209673] using wordTrace_append hprefix tailTrace_1209673
  have hstable : (prefixWord ++ tailWord_1209673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209673).length < 2 ^ (prefixWord ++ tailWord_1209673).sum := by decide
  have hdescent : baseEnd_1209673 < baseStart_1209673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209713 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 1, 4, 3]
def baseStart_1209713 : Nat := 118140960795 + 1209713 * 2 ^ 59
def prefixEnd_1209713 : Nat := 4983230072969 + 3 ^ 40 * 1209713 * 2
def baseEnd_1209713 : Nat := 621164222992530726024137

theorem tailTrace_1209713 : CollatzResearch.WordTrace tailWord_1209713 prefixEnd_1209713 621164222992530726024137 := by
  unfold tailWord_1209713
  simp only [CollatzResearch.WordTrace]
  refine ⟨44121857866423878377041793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29414571910949252251361195 44121857866423878377041793)
  ·
    refine ⟨33091393399817908782781345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44121857866423878377041793 33091393399817908782781345)
    ·
      refine ⟨24818545049863431587086009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33091393399817908782781345 24818545049863431587086009)
      ·
        refine ⟨18613908787397573690314507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24818545049863431587086009 18613908787397573690314507)
        ·
          refine ⟨27920863181096360535471761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18613908787397573690314507 27920863181096360535471761)
          ·
            refine ⟨20940647385822270401603821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27920863181096360535471761 20940647385822270401603821)
            ·
              refine ⟨7852742769683351400601433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20940647385822270401603821 7852742769683351400601433)
              ·
                refine ⟨5889557077262513550451075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7852742769683351400601433 5889557077262513550451075)
                ·
                  refine ⟨8834335615893770325676613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5889557077262513550451075 8834335615893770325676613)
                  ·
                    refine ⟨1656437927980081936064365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8834335615893770325676613 1656437927980081936064365)
                    ·
                      refine ⟨621164222992530726024137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1656437927980081936064365 621164222992530726024137)
                      ·
                        rfl

theorem cell23_1209713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_1209713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209713 prefixEnd_1209713 := by exact prefixLift 1209713
  have htrace : WordTrace (prefixWord ++ tailWord_1209713) baseStart_1209713 baseEnd_1209713 := by
    simpa [prefixWord, tailWord_1209713, baseEnd_1209713] using wordTrace_append hprefix tailTrace_1209713
  have hstable : (prefixWord ++ tailWord_1209713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209713).length < 2 ^ (prefixWord ++ tailWord_1209713).sum := by decide
  have hdescent : baseEnd_1209713 < baseStart_1209713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209754 : List Nat := [3, 1, 1, 4, 1, 1, 5, 2, 1, 4]
def baseStart_1209754 : Nat := 118140960795 + 1209754 * 2 ^ 59
def prefixEnd_1209754 : Nat := 4983230072969 + 3 ^ 40 * 1209754 * 2
def baseEnd_1209754 : Nat := 207061758566455021870483

theorem tailTrace_1209754 : CollatzResearch.WordTrace tailWord_1209754 prefixEnd_1209754 207061758566455021870483 := by
  unfold tailWord_1209754
  simp only [CollatzResearch.WordTrace]
  refine ⟨11030838314818835594821079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29415568839516894919522877 11030838314818835594821079)
  ·
    refine ⟨16546257472228253392231619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11030838314818835594821079 16546257472228253392231619)
    ·
      refine ⟨24819386208342380088347429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16546257472228253392231619 24819386208342380088347429)
      ·
        refine ⟨4653634914064196266565143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24819386208342380088347429 4653634914064196266565143)
        ·
          refine ⟨6980452371096294399847715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4653634914064196266565143 6980452371096294399847715)
          ·
            refine ⟨10470678556644441599771573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6980452371096294399847715 10470678556644441599771573)
            ·
              refine ⟨981626114685416399978585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10470678556644441599771573 981626114685416399978585)
              ·
                refine ⟨736219586014062299983939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 981626114685416399978585 736219586014062299983939)
                ·
                  refine ⟨1104329379021093449975909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736219586014062299983939 1104329379021093449975909)
                  ·
                    refine ⟨207061758566455021870483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1104329379021093449975909 207061758566455021870483)
                    ·
                      rfl

theorem cell23_1209754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_1209754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209754 prefixEnd_1209754 := by exact prefixLift 1209754
  have htrace : WordTrace (prefixWord ++ tailWord_1209754) baseStart_1209754 baseEnd_1209754 := by
    simpa [prefixWord, tailWord_1209754, baseEnd_1209754] using wordTrace_append hprefix tailTrace_1209754
  have hstable : (prefixWord ++ tailWord_1209754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209754).length < 2 ^ (prefixWord ++ tailWord_1209754).sum := by decide
  have hdescent : baseEnd_1209754 < baseStart_1209754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209763 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 3, 5]
def baseStart_1209763 : Nat := 118140960795 + 1209763 * 2 ^ 59
def prefixEnd_1209763 : Nat := 4983230072969 + 3 ^ 40 * 1209763 * 2
def baseEnd_1209763 : Nat := 207063299008418510132969

theorem tailTrace_1209763 : CollatzResearch.WordTrace tailWord_1209763 prefixEnd_1209763 207063299008418510132969 := by
  unfold tailWord_1209763
  simp only [CollatzResearch.WordTrace]
  refine ⟨44123681516242736916361943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29415787677495157944241295 44123681516242736916361943)
  ·
    refine ⟨66185522274364105374542915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44123681516242736916361943 66185522274364105374542915)
    ·
      refine ⟨99278283411546158061814373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66185522274364105374542915 99278283411546158061814373)
      ·
        refine ⟨18614678139664904636590195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99278283411546158061814373 18614678139664904636590195)
        ·
          refine ⟨27922017209497356954885293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18614678139664904636590195 27922017209497356954885293)
          ·
            refine ⟨10470756453561508858081985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27922017209497356954885293 10470756453561508858081985)
            ·
              refine ⟨7853067340171131643561489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10470756453561508858081985 7853067340171131643561489)
              ·
                refine ⟨5889800505128348732671117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7853067340171131643561489 5889800505128348732671117)
                ·
                  refine ⟨2208675189423130774751669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5889800505128348732671117 2208675189423130774751669)
                  ·
                    refine ⟨207063299008418510132969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2208675189423130774751669 207063299008418510132969)
                    ·
                      rfl

theorem cell23_1209763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 5].length) (baseStart_1209763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209763 prefixEnd_1209763 := by exact prefixLift 1209763
  have htrace : WordTrace (prefixWord ++ tailWord_1209763) baseStart_1209763 baseEnd_1209763 := by
    simpa [prefixWord, tailWord_1209763, baseEnd_1209763] using wordTrace_append hprefix tailTrace_1209763
  have hstable : (prefixWord ++ tailWord_1209763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209763).length < 2 ^ (prefixWord ++ tailWord_1209763).sum := by decide
  have hdescent : baseEnd_1209763 < baseStart_1209763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209827 : List Nat := [1, 1, 1, 6, 2, 1, 2, 3, 2, 4]
def baseStart_1209827 : Nat := 118140960795 + 1209827 * 2 ^ 59
def prefixEnd_1209827 : Nat := 4983230072969 + 3 ^ 40 * 1209827 * 2
def baseEnd_1209827 : Nat := 207074253262381093332871

theorem tailTrace_1209827 : CollatzResearch.WordTrace tailWord_1209827 prefixEnd_1209827 207074253262381093332871 := by
  unfold tailWord_1209827
  simp only [CollatzResearch.WordTrace]
  refine ⟨44126015788010875846691735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29417343858673917231127823 44126015788010875846691735)
  ·
    refine ⟨66189023682016313770037603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44126015788010875846691735 66189023682016313770037603)
    ·
      refine ⟨99283535523024470655056405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66189023682016313770037603 99283535523024470655056405)
      ·
        refine ⟨4653915727641772061955769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99283535523024470655056405 4653915727641772061955769)
        ·
          refine ⟨3490436795731329046466827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4653915727641772061955769 3490436795731329046466827)
          ·
            refine ⟨5235655193596993569700241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3490436795731329046466827 5235655193596993569700241)
            ·
              refine ⟨3926741395197745177275181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5235655193596993569700241 3926741395197745177275181)
              ·
                refine ⟨1472528023199154441478193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3926741395197745177275181 1472528023199154441478193)
                ·
                  refine ⟨1104396017399365831108645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1472528023199154441478193 1104396017399365831108645)
                  ·
                    refine ⟨207074253262381093332871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1104396017399365831108645 207074253262381093332871)
                    ·
                      rfl

theorem cell23_1209827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 4].length) (baseStart_1209827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209827 prefixEnd_1209827 := by exact prefixLift 1209827
  have htrace : WordTrace (prefixWord ++ tailWord_1209827) baseStart_1209827 baseEnd_1209827 := by
    simpa [prefixWord, tailWord_1209827, baseEnd_1209827] using wordTrace_append hprefix tailTrace_1209827
  have hstable : (prefixWord ++ tailWord_1209827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209827).length < 2 ^ (prefixWord ++ tailWord_1209827).sum := by decide
  have hdescent : baseEnd_1209827 < baseStart_1209827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209840 : List Nat := [2, 1, 1, 1, 3, 5, 3, 7]
def baseStart_1209840 : Nat := 118140960795 + 1209840 * 2 ^ 59
def prefixEnd_1209840 : Nat := 4983230072969 + 3 ^ 40 * 1209840 * 2
def baseEnd_1209840 : Nat := 23008497593913027005039

theorem tailTrace_1209840 : CollatzResearch.WordTrace tailWord_1209840 prefixEnd_1209840 23008497593913027005039 := by
  unfold tailWord_1209840
  simp only [CollatzResearch.WordTrace]
  refine ⟨22063244968481889533457487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29417659957975852711276649 22063244968481889533457487)
  ·
    refine ⟨33094867452722834300186231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22063244968481889533457487 33094867452722834300186231)
    ·
      refine ⟨49642301179084251450279347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33094867452722834300186231 49642301179084251450279347)
      ·
        refine ⟨74463451768626377175419021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49642301179084251450279347 74463451768626377175419021)
        ·
          refine ⟨27923794413234891440782133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74463451768626377175419021 27923794413234891440782133)
          ·
            refine ⟨2617855726240771072573325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27923794413234891440782133 2617855726240771072573325)
            ·
              refine ⟨981695897340289152214997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2617855726240771072573325 981695897340289152214997)
              ·
                refine ⟨23008497593913027005039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 981695897340289152214997 23008497593913027005039)
                ·
                  rfl

theorem cell23_1209840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 7].length) (baseStart_1209840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209840 prefixEnd_1209840 := by exact prefixLift 1209840
  have htrace : WordTrace (prefixWord ++ tailWord_1209840) baseStart_1209840 baseEnd_1209840 := by
    simpa [prefixWord, tailWord_1209840, baseEnd_1209840] using wordTrace_append hprefix tailTrace_1209840
  have hstable : (prefixWord ++ tailWord_1209840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209840).length < 2 ^ (prefixWord ++ tailWord_1209840).sum := by decide
  have hdescent : baseEnd_1209840 < baseStart_1209840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209850 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3]
def baseStart_1209850 : Nat := 118140960795 + 1209850 * 2 ^ 59
def prefixEnd_1209850 : Nat := 4983230072969 + 3 ^ 40 * 1209850 * 2
def baseEnd_1209850 : Nat := 621234569842196690011007

theorem tailTrace_1209850 : CollatzResearch.WordTrace tailWord_1209850 prefixEnd_1209850 621234569842196690011007 := by
  unfold tailWord_1209850
  simp only [CollatzResearch.WordTrace]
  refine ⟨11031713666731887693694751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29417903111285033849852669 11031713666731887693694751)
  ·
    refine ⟨16547570500097831540542127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11031713666731887693694751 16547570500097831540542127)
    ·
      refine ⟨24821355750146747310813191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16547570500097831540542127 24821355750146747310813191)
      ·
        refine ⟨37232033625220120966219787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24821355750146747310813191 37232033625220120966219787)
        ·
          refine ⟨55848050437830181449329681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37232033625220120966219787 55848050437830181449329681)
          ·
            refine ⟨41886037828372636086997261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55848050437830181449329681 41886037828372636086997261)
            ·
              refine ⟨15707264185639738532623973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41886037828372636086997261 15707264185639738532623973)
              ·
                refine ⟨2945112034807450974866995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15707264185639738532623973 2945112034807450974866995)
                ·
                  refine ⟨4417668052211176462300493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2945112034807450974866995 4417668052211176462300493)
                  ·
                    refine ⟨1656625519579191173362685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4417668052211176462300493 1656625519579191173362685)
                    ·
                      refine ⟨621234569842196690011007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1656625519579191173362685 621234569842196690011007)
                      ·
                        rfl

theorem cell23_1209850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_1209850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209850 prefixEnd_1209850 := by exact prefixLift 1209850
  have htrace : WordTrace (prefixWord ++ tailWord_1209850) baseStart_1209850 baseEnd_1209850 := by
    simpa [prefixWord, tailWord_1209850, baseEnd_1209850] using wordTrace_append hprefix tailTrace_1209850
  have hstable : (prefixWord ++ tailWord_1209850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209850).length < 2 ^ (prefixWord ++ tailWord_1209850).sum := by decide
  have hdescent : baseEnd_1209850 < baseStart_1209850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209890 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1209890 : Nat := 118140960795 + 1209890 * 2 ^ 59
def prefixEnd_1209890 : Nat := 4983230072969 + 3 ^ 40 * 1209890 * 2
def baseEnd_1209890 : Nat := 621255109068376533510823

theorem tailTrace_1209890 : CollatzResearch.WordTrace tailWord_1209890 prefixEnd_1209890 621255109068376533510823 := by
  unfold tailWord_1209890
  simp only [CollatzResearch.WordTrace]
  refine ⟨11032078396695659401558781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29418875724521758404156749 11032078396695659401558781)
  ·
    refine ⟨4137029398760872275584543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11032078396695659401558781 4137029398760872275584543)
    ·
      refine ⟨6205544098141308413376815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4137029398760872275584543 6205544098141308413376815)
      ·
        refine ⟨9308316147211962620065223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6205544098141308413376815 9308316147211962620065223)
        ·
          refine ⟨13962474220817943930097835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9308316147211962620065223 13962474220817943930097835)
          ·
            refine ⟨20943711331226915895146753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13962474220817943930097835 20943711331226915895146753)
            ·
              refine ⟨15707783498420186921360065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20943711331226915895146753 15707783498420186921360065)
              ·
                refine ⟨11780837623815140191020049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15707783498420186921360065 11780837623815140191020049)
                ·
                  refine ⟨8835628217861355143265037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11780837623815140191020049 8835628217861355143265037)
                  ·
                    refine ⟨3313360581698008178724389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8835628217861355143265037 3313360581698008178724389)
                    ·
                      refine ⟨621255109068376533510823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3313360581698008178724389 621255109068376533510823)
                      ·
                        rfl

theorem cell23_1209890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1209890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209890 prefixEnd_1209890 := by exact prefixLift 1209890
  have htrace : WordTrace (prefixWord ++ tailWord_1209890) baseStart_1209890 baseEnd_1209890 := by
    simpa [prefixWord, tailWord_1209890, baseEnd_1209890] using wordTrace_append hprefix tailTrace_1209890
  have hstable : (prefixWord ++ tailWord_1209890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209890).length < 2 ^ (prefixWord ++ tailWord_1209890).sum := by decide
  have hdescent : baseEnd_1209890 < baseStart_1209890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209980 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_1209980 : Nat := 118140960795 + 1209980 * 2 ^ 59
def prefixEnd_1209980 : Nat := 4983230072969 + 3 ^ 40 * 1209980 * 2
def baseEnd_1209980 : Nat := 621301322327281181385409

theorem tailTrace_1209980 : CollatzResearch.WordTrace tailWord_1209980 prefixEnd_1209980 621301322327281181385409 := by
  unfold tailWord_1209980
  simp only [CollatzResearch.WordTrace]
  refine ⟨22065798078228291488505697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29421064104304388651340929 22065798078228291488505697)
  ·
    refine ⟨16549348558671218616379273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22065798078228291488505697 16549348558671218616379273)
    ·
      refine ⟨12412011419003413962284455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16549348558671218616379273 12412011419003413962284455)
      ·
        refine ⟨18618017128505120943426683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12412011419003413962284455 18618017128505120943426683)
        ·
          refine ⟨27927025692757681415140025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18618017128505120943426683 27927025692757681415140025)
          ·
            refine ⟨20945269269568261061355019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27927025692757681415140025 20945269269568261061355019)
            ·
              refine ⟨31417903904352391592032529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20945269269568261061355019 31417903904352391592032529)
              ·
                refine ⟨23563427928264293694024397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31417903904352391592032529 23563427928264293694024397)
                ·
                  refine ⟨8836285473099110135259149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23563427928264293694024397 8836285473099110135259149)
                  ·
                    refine ⟨3313607052412166300722181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8836285473099110135259149 3313607052412166300722181)
                    ·
                      refine ⟨621301322327281181385409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3313607052412166300722181 621301322327281181385409)
                      ·
                        rfl

theorem cell23_1209980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_1209980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209980 prefixEnd_1209980 := by exact prefixLift 1209980
  have htrace : WordTrace (prefixWord ++ tailWord_1209980) baseStart_1209980 baseEnd_1209980 := by
    simpa [prefixWord, tailWord_1209980, baseEnd_1209980] using wordTrace_append hprefix tailTrace_1209980
  have hstable : (prefixWord ++ tailWord_1209980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209980).length < 2 ^ (prefixWord ++ tailWord_1209980).sum := by decide
  have hdescent : baseEnd_1209980 < baseStart_1209980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209981 : List Nat := [1, 4, 1, 1, 4, 3, 2, 2, 5]
def baseStart_1209981 : Nat := 118140960795 + 1209981 * 2 ^ 59
def prefixEnd_1209981 : Nat := 4983230072969 + 3 ^ 40 * 1209981 * 2
def baseEnd_1209981 : Nat := 69033537311992853052545

theorem tailTrace_1209981 : CollatzResearch.WordTrace tailWord_1209981 prefixEnd_1209981 69033537311992853052545 := by
  unfold tailWord_1209981
  simp only [CollatzResearch.WordTrace]
  refine ⟨44131632629452960147797797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29421088419635306765198531 44131632629452960147797797)
  ·
    refine ⟨8274681118022430027712087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44131632629452960147797797 8274681118022430027712087)
    ·
      refine ⟨12412021677033645041568131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8274681118022430027712087 12412021677033645041568131)
      ·
        refine ⟨18618032515550467562352197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12412021677033645041568131 18618032515550467562352197)
        ·
          refine ⟨3490881096665712667941037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18618032515550467562352197 3490881096665712667941037)
          ·
            refine ⟨1309080411249642250477889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3490881096665712667941037 1309080411249642250477889)
            ·
              refine ⟨981810308437231687858417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1309080411249642250477889 981810308437231687858417)
              ·
                refine ⟨736357731327923765893813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 981810308437231687858417 736357731327923765893813)
                ·
                  refine ⟨69033537311992853052545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 736357731327923765893813 69033537311992853052545)
                  ·
                    rfl

theorem cell23_1209981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_1209981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1209981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1209981 prefixEnd_1209981 := by exact prefixLift 1209981
  have htrace : WordTrace (prefixWord ++ tailWord_1209981) baseStart_1209981 baseEnd_1209981 := by
    simpa [prefixWord, tailWord_1209981, baseEnd_1209981] using wordTrace_append hprefix tailTrace_1209981
  have hstable : (prefixWord ++ tailWord_1209981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209981).length < 2 ^ (prefixWord ++ tailWord_1209981).sum := by decide
  have hdescent : baseEnd_1209981 < baseStart_1209981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210007 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 5, 4]
def baseStart_1210007 : Nat := 118140960795 + 1210007 * 2 ^ 59
def prefixEnd_1210007 : Nat := 4983230072969 + 3 ^ 40 * 1210007 * 2
def baseEnd_1210007 : Nat := 207105062101650858582595

theorem tailTrace_1210007 : CollatzResearch.WordTrace tailWord_1210007 prefixEnd_1210007 207105062101650858582595 := by
  unfold tailWord_1210007
  simp only [CollatzResearch.WordTrace]
  refine ⟨44132580927358766588244275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29421720618239177725496183 44132580927358766588244275)
  ·
    refine ⟨66198871391038149882366413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44132580927358766588244275 66198871391038149882366413)
    ·
      refine ⟨24824576771639306205887405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66198871391038149882366413 24824576771639306205887405)
      ·
        refine ⟨9309216289364739827207777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24824576771639306205887405 9309216289364739827207777)
        ·
          refine ⟨6981912217023554870405833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9309216289364739827207777 6981912217023554870405833)
          ·
            refine ⟨5236434162767666152804375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6981912217023554870405833 5236434162767666152804375)
            ·
              refine ⟨7854651244151499229206563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5236434162767666152804375 7854651244151499229206563)
              ·
                refine ⟨11781976866227248843809845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7854651244151499229206563 11781976866227248843809845)
                ·
                  refine ⟨1104560331208804579107173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11781976866227248843809845 1104560331208804579107173)
                  ·
                    refine ⟨207105062101650858582595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1104560331208804579107173 207105062101650858582595)
                    ·
                      rfl

theorem cell23_1210007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_1210007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210007 prefixEnd_1210007 := by exact prefixLift 1210007
  have htrace : WordTrace (prefixWord ++ tailWord_1210007) baseStart_1210007 baseEnd_1210007 := by
    simpa [prefixWord, tailWord_1210007, baseEnd_1210007] using wordTrace_append hprefix tailTrace_1210007
  have hstable : (prefixWord ++ tailWord_1210007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210007).length < 2 ^ (prefixWord ++ tailWord_1210007).sum := by decide
  have hdescent : baseEnd_1210007 < baseStart_1210007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210014 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1210014 : Nat := 118140960795 + 1210014 * 2 ^ 59
def prefixEnd_1210014 : Nat := 4983230072969 + 3 ^ 40 * 1210014 * 2
def baseEnd_1210014 : Nat := 621318780669534048360253

theorem tailTrace_1210014 : CollatzResearch.WordTrace tailWord_1210014 prefixEnd_1210014 621318780669534048360253 := by
  unfold tailWord_1210014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5516604529791675847968637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29421890825555604522499397 5516604529791675847968637)
  ·
    refine ⟨2068726698671878442988239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5516604529791675847968637 2068726698671878442988239)
    ·
      refine ⟨3103090048007817664482359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2068726698671878442988239 3103090048007817664482359)
      ·
        refine ⟨4654635072011726496723539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3103090048007817664482359 4654635072011726496723539)
        ·
          refine ⟨6981952608017589745085309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4654635072011726496723539 6981952608017589745085309)
          ·
            refine ⟨2618232228006596154406991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6981952608017589745085309 2618232228006596154406991)
            ·
              refine ⟨3927348342009894231610487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2618232228006596154406991 3927348342009894231610487)
              ·
                refine ⟨5891022513014841347415731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3927348342009894231610487 5891022513014841347415731)
                ·
                  refine ⟨8836533769522262021123597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5891022513014841347415731 8836533769522262021123597)
                  ·
                    refine ⟨3313700163570848257921349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8836533769522262021123597 3313700163570848257921349)
                    ·
                      refine ⟨621318780669534048360253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3313700163570848257921349 621318780669534048360253)
                      ·
                        rfl

theorem cell23_1210014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1210014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210014 prefixEnd_1210014 := by exact prefixLift 1210014
  have htrace : WordTrace (prefixWord ++ tailWord_1210014) baseStart_1210014 baseEnd_1210014 := by
    simpa [prefixWord, tailWord_1210014, baseEnd_1210014] using wordTrace_append hprefix tailTrace_1210014
  have hstable : (prefixWord ++ tailWord_1210014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210014).length < 2 ^ (prefixWord ++ tailWord_1210014).sum := by decide
  have hdescent : baseEnd_1210014 < baseStart_1210014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210074 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2]
def baseStart_1210074 : Nat := 118140960795 + 1210074 * 2 ^ 59
def prefixEnd_1210074 : Nat := 4983230072969 + 3 ^ 40 * 1210074 * 2
def baseEnd_1210074 : Nat := 621349589508803813609977

theorem tailTrace_1210074 : CollatzResearch.WordTrace tailWord_1210074 prefixEnd_1210074 621349589508803813609977 := by
  unfold tailWord_1210074
  simp only [CollatzResearch.WordTrace]
  refine ⟨11033756154529009257733319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29423349745410691353955517 11033756154529009257733319)
  ·
    refine ⟨16550634231793513886599979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11033756154529009257733319 16550634231793513886599979)
    ·
      refine ⟨24825951347690270829899969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16550634231793513886599979 24825951347690270829899969)
      ·
        refine ⟨18619463510767703122424977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24825951347690270829899969 18619463510767703122424977)
        ·
          refine ⟨13964597633075777341818733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18619463510767703122424977 13964597633075777341818733)
          ·
            refine ⟨5236724112403416503182025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13964597633075777341818733 5236724112403416503182025)
            ·
              refine ⟨3927543084302562377386519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5236724112403416503182025 3927543084302562377386519)
              ·
                refine ⟨5891314626453843566079779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3927543084302562377386519 5891314626453843566079779)
                ·
                  refine ⟨8836971939680765349119669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5891314626453843566079779 8836971939680765349119669)
                  ·
                    refine ⟨828466119345071751479969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8836971939680765349119669 828466119345071751479969)
                    ·
                      refine ⟨621349589508803813609977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 828466119345071751479969 621349589508803813609977)
                      ·
                        rfl

theorem cell23_1210074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_1210074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210074 prefixEnd_1210074 := by exact prefixLift 1210074
  have htrace : WordTrace (prefixWord ++ tailWord_1210074) baseStart_1210074 baseEnd_1210074 := by
    simpa [prefixWord, tailWord_1210074, baseEnd_1210074] using wordTrace_append hprefix tailTrace_1210074
  have hstable : (prefixWord ++ tailWord_1210074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210074).length < 2 ^ (prefixWord ++ tailWord_1210074).sum := by decide
  have hdescent : baseEnd_1210074 < baseStart_1210074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210114 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1210114 : Nat := 118140960795 + 1210114 * 2 ^ 59
def prefixEnd_1210114 : Nat := 4983230072969 + 3 ^ 40 * 1210114 * 2
def baseEnd_1210114 : Nat := 207123376244994552369931

theorem tailTrace_1210114 : CollatzResearch.WordTrace tailWord_1210114 prefixEnd_1210114 207123376244994552369931 := by
  unfold tailWord_1210114
  simp only [CollatzResearch.WordTrace]
  refine ⟨11034120884492780965597349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29424322358647415908259597 11034120884492780965597349)
  ·
    refine ⟨2068897665842396431049503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11034120884492780965597349 2068897665842396431049503)
    ·
      refine ⟨3103346498763594646574255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2068897665842396431049503 3103346498763594646574255)
      ·
        refine ⟨4655019748145391969861383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3103346498763594646574255 4655019748145391969861383)
        ·
          refine ⟨6982529622218087954792075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4655019748145391969861383 6982529622218087954792075)
          ·
            refine ⟨10473794433327131932188113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6982529622218087954792075 10473794433327131932188113)
            ·
              refine ⟨7855345824995348949141085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10473794433327131932188113 7855345824995348949141085)
              ·
                refine ⟨2945754684373255855927907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7855345824995348949141085 2945754684373255855927907)
                ·
                  refine ⟨4418632026559883783891861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2945754684373255855927907 4418632026559883783891861)
                  ·
                    refine ⟨207123376244994552369931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4418632026559883783891861 207123376244994552369931)
                    ·
                      rfl

theorem cell23_1210114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1210114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210114 prefixEnd_1210114 := by exact prefixLift 1210114
  have htrace : WordTrace (prefixWord ++ tailWord_1210114) baseStart_1210114 baseEnd_1210114 := by
    simpa [prefixWord, tailWord_1210114, baseEnd_1210114] using wordTrace_append hprefix tailTrace_1210114
  have hstable : (prefixWord ++ tailWord_1210114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210114).length < 2 ^ (prefixWord ++ tailWord_1210114).sum := by decide
  have hdescent : baseEnd_1210114 < baseStart_1210114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210181 : List Nat := [1, 3, 1, 1, 1, 2, 4, 4, 1, 3, 2]
def baseStart_1210181 : Nat := 118140960795 + 1210181 * 2 ^ 59
def prefixEnd_1210181 : Nat := 4983230072969 + 3 ^ 40 * 1210181 * 2
def baseEnd_1210181 : Nat := 621404531938834894971985

theorem tailTrace_1210181 : CollatzResearch.WordTrace tailWord_1210181 prefixEnd_1210181 621404531938834894971985 := by
  unfold tailWord_1210181
  simp only [CollatzResearch.WordTrace]
  refine ⟨44138927228728394305078397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29425951485818929536718931 44138927228728394305078397)
  ·
    refine ⟨16552097710773147864404399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44138927228728394305078397 16552097710773147864404399)
    ·
      refine ⟨24828146566159721796606599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16552097710773147864404399 24828146566159721796606599)
      ·
        refine ⟨37242219849239582694909899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24828146566159721796606599 37242219849239582694909899)
        ·
          refine ⟨55863329773859374042364849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37242219849239582694909899 55863329773859374042364849)
          ·
            refine ⟨41897497330394530531773637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55863329773859374042364849 41897497330394530531773637)
            ·
              refine ⟨7855780749448974474707557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41897497330394530531773637 7855780749448974474707557)
              ·
                refine ⟨1472958890521682714007667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7855780749448974474707557 1472958890521682714007667)
                ·
                  refine ⟨2209438335782524071011501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1472958890521682714007667 2209438335782524071011501)
                  ·
                    refine ⟨828539375918446526629313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2209438335782524071011501 828539375918446526629313)
                    ·
                      refine ⟨621404531938834894971985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 828539375918446526629313 621404531938834894971985)
                      ·
                        rfl

theorem cell23_1210181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 3, 2].length) (baseStart_1210181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210181 prefixEnd_1210181 := by exact prefixLift 1210181
  have htrace : WordTrace (prefixWord ++ tailWord_1210181) baseStart_1210181 baseEnd_1210181 := by
    simpa [prefixWord, tailWord_1210181, baseEnd_1210181] using wordTrace_append hprefix tailTrace_1210181
  have hstable : (prefixWord ++ tailWord_1210181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210181).length < 2 ^ (prefixWord ++ tailWord_1210181).sum := by decide
  have hdescent : baseEnd_1210181 < baseStart_1210181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210244 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_1210244 : Nat := 118140960795 + 1210244 * 2 ^ 59
def prefixEnd_1210244 : Nat := 4983230072969 + 3 ^ 40 * 1210244 * 2
def baseEnd_1210244 : Nat := 621436881220068148484195

theorem tailTrace_1210244 : CollatzResearch.WordTrace tailWord_1210244 prefixEnd_1210244 621436881220068148484195 := by
  unfold tailWord_1210244
  simp only [CollatzResearch.WordTrace]
  refine ⟨22070612513750078032310893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29427483351666770709747857 22070612513750078032310893)
  ·
    refine ⟨8276479692656279262116585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22070612513750078032310893 8276479692656279262116585)
    ·
      refine ⟨6207359769492209446587439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8276479692656279262116585 6207359769492209446587439)
      ·
        refine ⟨9311039654238314169881159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6207359769492209446587439 9311039654238314169881159)
        ·
          refine ⟨13966559481357471254821739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9311039654238314169881159 13966559481357471254821739)
          ·
            refine ⟨20949839222036206882232609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13966559481357471254821739 20949839222036206882232609)
            ·
              refine ⟨15712379416527155161674457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20949839222036206882232609 15712379416527155161674457)
              ·
                refine ⟨11784284562395366371255843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15712379416527155161674457 11784284562395366371255843)
                ·
                  refine ⟨17676426843593049556883765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11784284562395366371255843 17676426843593049556883765)
                  ·
                    refine ⟨1657165016586848395957853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17676426843593049556883765 1657165016586848395957853)
                    ·
                      refine ⟨621436881220068148484195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1657165016586848395957853 621436881220068148484195)
                      ·
                        rfl

theorem cell23_1210244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_1210244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210244 prefixEnd_1210244 := by exact prefixLift 1210244
  have htrace : WordTrace (prefixWord ++ tailWord_1210244) baseStart_1210244 baseEnd_1210244 := by
    simpa [prefixWord, tailWord_1210244, baseEnd_1210244] using wordTrace_append hprefix tailTrace_1210244
  have hstable : (prefixWord ++ tailWord_1210244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210244).length < 2 ^ (prefixWord ++ tailWord_1210244).sum := by decide
  have hdescent : baseEnd_1210244 < baseStart_1210244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210301 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_1210301 : Nat := 118140960795 + 1210301 * 2 ^ 59
def prefixEnd_1210301 : Nat := 4983230072969 + 3 ^ 40 * 1210301 * 2
def baseEnd_1210301 : Nat := 621466149617374425471433

theorem tailTrace_1210301 : CollatzResearch.WordTrace tailWord_1210301 prefixEnd_1210301 621466149617374425471433 := by
  unfold tailWord_1210301
  simp only [CollatzResearch.WordTrace]
  refine ⟨44143303988293654799446757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29428869325529103199631171 44143303988293654799446757)
  ·
    refine ⟨8276869497805060274896267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44143303988293654799446757 8276869497805060274896267)
    ·
      refine ⟨12415304246707590412344401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8276869497805060274896267 12415304246707590412344401)
      ·
        refine ⟨9311478185030692809258301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12415304246707590412344401 9311478185030692809258301)
        ·
          refine ⟨3491804319386509803471863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9311478185030692809258301 3491804319386509803471863)
          ·
            refine ⟨5237706479079764705207795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3491804319386509803471863 5237706479079764705207795)
            ·
              refine ⟨7856559718619647057811693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5237706479079764705207795 7856559718619647057811693)
              ·
                refine ⟨2946209894482367646679385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7856559718619647057811693 2946209894482367646679385)
                ·
                  refine ⟨2209657420861775735009539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2946209894482367646679385 2209657420861775735009539)
                  ·
                    refine ⟨3314486131292663602514309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2209657420861775735009539 3314486131292663602514309)
                    ·
                      refine ⟨621466149617374425471433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3314486131292663602514309 621466149617374425471433)
                      ·
                        rfl

theorem cell23_1210301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_1210301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210301 prefixEnd_1210301 := by exact prefixLift 1210301
  have htrace : WordTrace (prefixWord ++ tailWord_1210301) baseStart_1210301 baseEnd_1210301 := by
    simpa [prefixWord, tailWord_1210301, baseEnd_1210301] using wordTrace_append hprefix tailTrace_1210301
  have hstable : (prefixWord ++ tailWord_1210301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210301).length < 2 ^ (prefixWord ++ tailWord_1210301).sum := by decide
  have hdescent : baseEnd_1210301 < baseStart_1210301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210328 : List Nat := [2, 1, 2, 2, 2, 2, 3, 4, 1, 4]
def baseStart_1210328 : Nat := 118140960795 + 1210328 * 2 ^ 59
def prefixEnd_1210328 : Nat := 4983230072969 + 3 ^ 40 * 1210328 * 2
def baseEnd_1210328 : Nat := 207160004531681939944603

theorem tailTrace_1210328 : CollatzResearch.WordTrace tailWord_1210328 prefixEnd_1210328 207160004531681939944603 := by
  unfold tailWord_1210328
  simp only [CollatzResearch.WordTrace]
  refine ⟨22072144379597919205339819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29429525839463892273786425 22072144379597919205339819)
  ·
    refine ⟨33108216569396878808009729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22072144379597919205339819 33108216569396878808009729)
    ·
      refine ⟨24831162427047659106007297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33108216569396878808009729 24831162427047659106007297)
      ·
        refine ⟨18623371820285744329505473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24831162427047659106007297 18623371820285744329505473)
        ·
          refine ⟨13967528865214308247129105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18623371820285744329505473 13967528865214308247129105)
          ·
            refine ⟨10475646648910731185346829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13967528865214308247129105 10475646648910731185346829)
            ·
              refine ⟨3928367493341524194505061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10475646648910731185346829 3928367493341524194505061)
              ·
                refine ⟨736568905001535786469699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3928367493341524194505061 736568905001535786469699)
                ·
                  refine ⟨1104853357502303679704549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736568905001535786469699 1104853357502303679704549)
                  ·
                    refine ⟨207160004531681939944603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1104853357502303679704549 207160004531681939944603)
                    ·
                      rfl

theorem cell23_1210328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_1210328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210328 prefixEnd_1210328 := by exact prefixLift 1210328
  have htrace : WordTrace (prefixWord ++ tailWord_1210328) baseStart_1210328 baseEnd_1210328 := by
    simpa [prefixWord, tailWord_1210328, baseEnd_1210328] using wordTrace_append hprefix tailTrace_1210328
  have hstable : (prefixWord ++ tailWord_1210328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210328).length < 2 ^ (prefixWord ++ tailWord_1210328).sum := by decide
  have hdescent : baseEnd_1210328 < baseStart_1210328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210421 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_1210421 : Nat := 118140960795 + 1210421 * 2 ^ 59
def prefixEnd_1210421 : Nat := 4983230072969 + 3 ^ 40 * 1210421 * 2
def baseEnd_1210421 : Nat := 621527767295913955970881

theorem tailTrace_1210421 : CollatzResearch.WordTrace tailWord_1210421 prefixEnd_1210421 621527767295913955970881 := by
  unfold tailWord_1210421
  simp only [CollatzResearch.WordTrace]
  refine ⟨44147680747858915293815117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29431787165239276862543411 44147680747858915293815117)
  ·
    refine ⟨16555380280447093235180669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44147680747858915293815117 16555380280447093235180669)
    ·
      refine ⟨6208267605167659963192751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16555380280447093235180669 6208267605167659963192751)
      ·
        refine ⟨9312401407751489944789127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6208267605167659963192751 9312401407751489944789127)
        ·
          refine ⟨13968602111627234917183691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9312401407751489944789127 13968602111627234917183691)
          ·
            refine ⟨20952903167440852375775537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13968602111627234917183691 20952903167440852375775537)
            ·
              refine ⟨15714677375580639281831653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20952903167440852375775537 15714677375580639281831653)
              ·
                refine ⟨2946502007921369865343435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15714677375580639281831653 2946502007921369865343435)
                ·
                  refine ⟨4419753011882054798015153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2946502007921369865343435 4419753011882054798015153)
                  ·
                    refine ⟨3314814758911541098511365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4419753011882054798015153 3314814758911541098511365)
                    ·
                      refine ⟨621527767295913955970881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3314814758911541098511365 621527767295913955970881)
                      ·
                        rfl

theorem cell23_1210421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_1210421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210421 prefixEnd_1210421 := by exact prefixLift 1210421
  have htrace : WordTrace (prefixWord ++ tailWord_1210421) baseStart_1210421 baseEnd_1210421 := by
    simpa [prefixWord, tailWord_1210421, baseEnd_1210421] using wordTrace_append hprefix tailTrace_1210421
  have hstable : (prefixWord ++ tailWord_1210421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210421).length < 2 ^ (prefixWord ++ tailWord_1210421).sum := by decide
  have hdescent : baseEnd_1210421 < baseStart_1210421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210428 : List Nat := [2, 2, 2, 2, 2, 1, 1, 5, 1, 2, 3]
def baseStart_1210428 : Nat := 118140960795 + 1210428 * 2 ^ 59
def prefixEnd_1210428 : Nat := 4983230072969 + 3 ^ 40 * 1210428 * 2
def baseEnd_1210428 : Nat := 621531361660495428583349

theorem tailTrace_1210428 : CollatzResearch.WordTrace tailWord_1210428 prefixEnd_1210428 621531361660495428583349 := by
  unfold tailWord_1210428
  simp only [CollatzResearch.WordTrace]
  refine ⟨22073968029416777744659969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29431957372555703659546625 22073968029416777744659969)
  ·
    refine ⟨16555476022062583308494977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22073968029416777744659969 16555476022062583308494977)
    ·
      refine ⟨12416607016546937481371233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16555476022062583308494977 12416607016546937481371233)
      ·
        refine ⟨9312455262410203111028425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12416607016546937481371233 9312455262410203111028425)
        ·
          refine ⟨6984341446807652333271319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9312455262410203111028425 6984341446807652333271319)
          ·
            refine ⟨10476512170211478499906979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6984341446807652333271319 10476512170211478499906979)
            ·
              refine ⟨15714768255317217749860469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10476512170211478499906979 15714768255317217749860469)
              ·
                refine ⟨1473259523935989164049419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15714768255317217749860469 1473259523935989164049419)
                ·
                  refine ⟨2209889285903983746074129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473259523935989164049419 2209889285903983746074129)
                  ·
                    refine ⟨1657416964427987809555597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2209889285903983746074129 1657416964427987809555597)
                    ·
                      refine ⟨621531361660495428583349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1657416964427987809555597 621531361660495428583349)
                      ·
                        rfl

theorem cell23_1210428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_1210428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210428 prefixEnd_1210428 := by exact prefixLift 1210428
  have htrace : WordTrace (prefixWord ++ tailWord_1210428) baseStart_1210428 baseEnd_1210428 := by
    simpa [prefixWord, tailWord_1210428, baseEnd_1210428] using wordTrace_append hprefix tailTrace_1210428
  have hstable : (prefixWord ++ tailWord_1210428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210428).length < 2 ^ (prefixWord ++ tailWord_1210428).sum := by decide
  have hdescent : baseEnd_1210428 < baseStart_1210428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210438 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1210438 : Nat := 118140960795 + 1210438 * 2 ^ 59
def prefixEnd_1210438 : Nat := 4983230072969 + 3 ^ 40 * 1210438 * 2
def baseEnd_1210438 : Nat := 621536496467040389458303

theorem tailTrace_1210438 : CollatzResearch.WordTrace tailWord_1210438 prefixEnd_1210438 621536496467040389458303 := by
  unfold tailWord_1210438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1379634399649916474911999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29432200525864884798122645 1379634399649916474911999)
  ·
    refine ⟨2069451599474874712367999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1379634399649916474911999 2069451599474874712367999)
    ·
      refine ⟨3104177399212312068551999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2069451599474874712367999 3104177399212312068551999)
      ·
        refine ⟨4656266098818468102827999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3104177399212312068551999 4656266098818468102827999)
        ·
          refine ⟨6984399148227702154241999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4656266098818468102827999 6984399148227702154241999)
          ·
            refine ⟨10476598722341553231362999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6984399148227702154241999 10476598722341553231362999)
            ·
              refine ⟨15714898083512329847044499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10476598722341553231362999 15714898083512329847044499)
              ·
                refine ⟨23572347125268494770566749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15714898083512329847044499 23572347125268494770566749)
                ·
                  refine ⟨8839630171975685538962531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23572347125268494770566749 8839630171975685538962531)
                  ·
                    refine ⟨13259445257963528308443797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8839630171975685538962531 13259445257963528308443797)
                    ·
                      refine ⟨621536496467040389458303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13259445257963528308443797 621536496467040389458303)
                      ·
                        rfl

theorem cell23_1210438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1210438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210438 prefixEnd_1210438 := by exact prefixLift 1210438
  have htrace : WordTrace (prefixWord ++ tailWord_1210438) baseStart_1210438 baseEnd_1210438 := by
    simpa [prefixWord, tailWord_1210438, baseEnd_1210438] using wordTrace_append hprefix tailTrace_1210438
  have hstable : (prefixWord ++ tailWord_1210438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210438).length < 2 ^ (prefixWord ++ tailWord_1210438).sum := by decide
  have hdescent : baseEnd_1210438 < baseStart_1210438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210549 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_1210549 : Nat := 118140960795 + 1210549 * 2 ^ 59
def prefixEnd_1210549 : Nat := 4983230072969 + 3 ^ 40 * 1210549 * 2
def baseEnd_1210549 : Nat := 621593492819689455170293

theorem tailTrace_1210549 : CollatzResearch.WordTrace tailWord_1210549 prefixEnd_1210549 621593492819689455170293 := by
  unfold tailWord_1210549
  simp only [CollatzResearch.WordTrace]
  refine ⟨44152349291395193154474701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29434899527596795436316467 44152349291395193154474701)
  ·
    refine ⟨16557130984273197432928013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44152349291395193154474701 16557130984273197432928013)
    ·
      refine ⟨6208924119102449037348005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16557130984273197432928013 6208924119102449037348005)
      ·
        refine ⟨1164173272331709194502751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6208924119102449037348005 1164173272331709194502751)
        ·
          refine ⟨1746259908497563791754127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164173272331709194502751 1746259908497563791754127)
          ·
            refine ⟨2619389862746345687631191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746259908497563791754127 2619389862746345687631191)
            ·
              refine ⟨3929084794119518531446787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2619389862746345687631191 3929084794119518531446787)
              ·
                refine ⟨5893627191179277797170181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3929084794119518531446787 5893627191179277797170181)
                ·
                  refine ⟨1105055098346114586969409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5893627191179277797170181 1105055098346114586969409)
                  ·
                    refine ⟨828791323759585940227057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1105055098346114586969409 828791323759585940227057)
                    ·
                      refine ⟨621593492819689455170293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 828791323759585940227057 621593492819689455170293)
                      ·
                        rfl

theorem cell23_1210549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_1210549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210549 prefixEnd_1210549 := by exact prefixLift 1210549
  have htrace : WordTrace (prefixWord ++ tailWord_1210549) baseStart_1210549 baseEnd_1210549 := by
    simpa [prefixWord, tailWord_1210549, baseEnd_1210549] using wordTrace_append hprefix tailTrace_1210549
  have hstable : (prefixWord ++ tailWord_1210549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210549).length < 2 ^ (prefixWord ++ tailWord_1210549).sum := by decide
  have hdescent : baseEnd_1210549 < baseStart_1210549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210562 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1210562 : Nat := 118140960795 + 1210562 * 2 ^ 59
def prefixEnd_1210562 : Nat := 4983230072969 + 3 ^ 40 * 1210562 * 2
def baseEnd_1210562 : Nat := 621600168068197904307733

theorem tailTrace_1210562 : CollatzResearch.WordTrace tailWord_1210562 prefixEnd_1210562 621600168068197904307733 := by
  unfold tailWord_1210562
  simp only [CollatzResearch.WordTrace]
  refine ⟨11038205860087024093674485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29435215626898730916465293 11038205860087024093674485)
  ·
    refine ⟨1034831799383158508781983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11038205860087024093674485 1034831799383158508781983)
    ·
      refine ⟨1552247699074737763172975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1034831799383158508781983 1552247699074737763172975)
      ·
        refine ⟨2328371548612106644759463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1552247699074737763172975 2328371548612106644759463)
        ·
          refine ⟨3492557322918159967139195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2328371548612106644759463 3492557322918159967139195)
          ·
            refine ⟨5238835984377239950708793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3492557322918159967139195 5238835984377239950708793)
            ·
              refine ⟨3929126988282929963031595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5238835984377239950708793 3929126988282929963031595)
              ·
                refine ⟨5893690482424394944547393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3929126988282929963031595 5893690482424394944547393)
                ·
                  refine ⟨4420267861818296208410545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5893690482424394944547393 4420267861818296208410545)
                  ·
                    refine ⟨3315200896363722156307909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4420267861818296208410545 3315200896363722156307909)
                    ·
                      refine ⟨621600168068197904307733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3315200896363722156307909 621600168068197904307733)
                      ·
                        rfl

theorem cell23_1210562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1210562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210562 prefixEnd_1210562 := by exact prefixLift 1210562
  have htrace : WordTrace (prefixWord ++ tailWord_1210562) baseStart_1210562 baseEnd_1210562 := by
    simpa [prefixWord, tailWord_1210562, baseEnd_1210562] using wordTrace_append hprefix tailTrace_1210562
  have hstable : (prefixWord ++ tailWord_1210562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210562).length < 2 ^ (prefixWord ++ tailWord_1210562).sum := by decide
  have hdescent : baseEnd_1210562 < baseStart_1210562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210571 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 4]
def baseStart_1210571 : Nat := 118140960795 + 1210571 * 2 ^ 59
def prefixEnd_1210571 : Nat := 4983230072969 + 3 ^ 40 * 1210571 * 2
def baseEnd_1210571 : Nat := 621604789394088369095191

theorem tailTrace_1210571 : CollatzResearch.WordTrace tailWord_1210571 prefixEnd_1210571 621604789394088369095191 := by
  unfold tailWord_1210571
  simp only [CollatzResearch.WordTrace]
  refine ⟨44153151697315490911775567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29435434464876993941183711 44153151697315490911775567)
  ·
    refine ⟨66229727545973236367663351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44153151697315490911775567 66229727545973236367663351)
    ·
      refine ⟨99344591318959854551495027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66229727545973236367663351 99344591318959854551495027)
      ·
        refine ⟨149016886978439781827242541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99344591318959854551495027 149016886978439781827242541)
        ·
          refine ⟨55881332616914918185215953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149016886978439781827242541 55881332616914918185215953)
          ·
            refine ⟨41910999462686188638911965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55881332616914918185215953 41910999462686188638911965)
            ·
              refine ⟨15716624798507320739591987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41910999462686188638911965 15716624798507320739591987)
              ·
                refine ⟨23574937197760981109387981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15716624798507320739591987 23574937197760981109387981)
                ·
                  refine ⟨8840601449160367916020493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23574937197760981109387981 8840601449160367916020493)
                  ·
                    refine ⟨3315225543435137968507685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8840601449160367916020493 3315225543435137968507685)
                    ·
                      refine ⟨621604789394088369095191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3315225543435137968507685 621604789394088369095191)
                      ·
                        rfl

theorem cell23_1210571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 4].length) (baseStart_1210571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210571 prefixEnd_1210571 := by exact prefixLift 1210571
  have htrace : WordTrace (prefixWord ++ tailWord_1210571) baseStart_1210571 baseEnd_1210571 := by
    simpa [prefixWord, tailWord_1210571, baseEnd_1210571] using wordTrace_append hprefix tailTrace_1210571
  have hstable : (prefixWord ++ tailWord_1210571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210571).length < 2 ^ (prefixWord ++ tailWord_1210571).sum := by decide
  have hdescent : baseEnd_1210571 < baseStart_1210571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210591 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 5]
def baseStart_1210591 : Nat := 118140960795 + 1210591 * 2 ^ 59
def prefixEnd_1210591 : Nat := 4983230072969 + 3 ^ 40 * 1210591 * 2
def baseEnd_1210591 : Nat := 621615059007178290845099

theorem tailTrace_1210591 : CollatzResearch.WordTrace tailWord_1210591 prefixEnd_1210591 621615059007178290845099 := by
  unfold tailWord_1210591
  simp only [CollatzResearch.WordTrace]
  refine ⟨44153881157243034327503627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29435920771495356218335751 44153881157243034327503627)
  ·
    refine ⟨66230821735864551491255441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44153881157243034327503627 66230821735864551491255441)
    ·
      refine ⟨49673116301898413618441581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66230821735864551491255441 49673116301898413618441581)
      ·
        refine ⟨18627418613211905106915593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49673116301898413618441581 18627418613211905106915593)
        ·
          refine ⟨13970563959908928830186695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18627418613211905106915593 13970563959908928830186695)
          ·
            refine ⟨20955845939863393245280043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13970563959908928830186695 20955845939863393245280043)
            ·
              refine ⟨31433768909795089867920065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20955845939863393245280043 31433768909795089867920065)
              ·
                refine ⟨23575326682346317400940049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31433768909795089867920065 23575326682346317400940049)
                ·
                  refine ⟨17681495011759738050705037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23575326682346317400940049 17681495011759738050705037)
                  ·
                    refine ⟨6630560629409901769014389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17681495011759738050705037 6630560629409901769014389)
                    ·
                      refine ⟨621615059007178290845099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6630560629409901769014389 621615059007178290845099)
                      ·
                        rfl

theorem cell23_1210591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_1210591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210591 prefixEnd_1210591 := by exact prefixLift 1210591
  have htrace : WordTrace (prefixWord ++ tailWord_1210591) baseStart_1210591 baseEnd_1210591 := by
    simpa [prefixWord, tailWord_1210591, baseEnd_1210591] using wordTrace_append hprefix tailTrace_1210591
  have hstable : (prefixWord ++ tailWord_1210591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210591).length < 2 ^ (prefixWord ++ tailWord_1210591).sum := by decide
  have hdescent : baseEnd_1210591 < baseStart_1210591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210601 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 1, 6, 4]
def baseStart_1210601 : Nat := 118140960795 + 1210601 * 2 ^ 59
def prefixEnd_1210601 : Nat := 4983230072969 + 3 ^ 40 * 1210601 * 2
def baseEnd_1210601 : Nat := 621620193813723251720053

theorem tailTrace_1210601 : CollatzResearch.WordTrace tailWord_1210601 prefixEnd_1210601 621620193813723251720053 := by
  unfold tailWord_1210601
  simp only [CollatzResearch.WordTrace]
  refine ⟨44154245887206806035367657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29436163924804537356911771 44154245887206806035367657)
  ·
    refine ⟨33115684415405104526525743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44154245887206806035367657 33115684415405104526525743)
    ·
      refine ⟨49673526623107656789788615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33115684415405104526525743 49673526623107656789788615)
      ·
        refine ⟨74510289934661485184682923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49673526623107656789788615 74510289934661485184682923)
        ·
          refine ⟨111765434901992227777024385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74510289934661485184682923 111765434901992227777024385)
          ·
            refine ⟨83824076176494170832768289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111765434901992227777024385 83824076176494170832768289)
            ·
              refine ⟨62868057132370628124576217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83824076176494170832768289 62868057132370628124576217)
              ·
                refine ⟨47151042849277971093432163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62868057132370628124576217 47151042849277971093432163)
                ·
                  refine ⟨70726564273916956640148245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47151042849277971093432163 70726564273916956640148245)
                  ·
                    refine ⟨3315307700339857342506949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70726564273916956640148245 3315307700339857342506949)
                    ·
                      refine ⟨621620193813723251720053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3315307700339857342506949 621620193813723251720053)
                      ·
                        rfl

theorem cell23_1210601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_1210601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210601 prefixEnd_1210601 := by exact prefixLift 1210601
  have htrace : WordTrace (prefixWord ++ tailWord_1210601) baseStart_1210601 baseEnd_1210601 := by
    simpa [prefixWord, tailWord_1210601, baseEnd_1210601] using wordTrace_append hprefix tailTrace_1210601
  have hstable : (prefixWord ++ tailWord_1210601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210601).length < 2 ^ (prefixWord ++ tailWord_1210601).sum := by decide
  have hdescent : baseEnd_1210601 < baseStart_1210601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210611 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 8]
def baseStart_1210611 : Nat := 118140960795 + 1210611 * 2 ^ 59
def prefixEnd_1210611 : Nat := 4983230072969 + 3 ^ 40 * 1210611 * 2
def baseEnd_1210611 : Nat := 69069480957807579177223

theorem tailTrace_1210611 : CollatzResearch.WordTrace tailWord_1210611 prefixEnd_1210611 69069480957807579177223 := by
  unfold tailWord_1210611
  simp only [CollatzResearch.WordTrace]
  refine ⟨44154610617170577743231687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29436407078113718495487791 44154610617170577743231687)
  ·
    refine ⟨66231915925755866614847531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44154610617170577743231687 66231915925755866614847531)
    ·
      refine ⟨99347873888633799922271297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66231915925755866614847531 99347873888633799922271297)
      ·
        refine ⟨74510905416475349941703473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99347873888633799922271297 74510905416475349941703473)
        ·
          refine ⟨55883179062356512456277605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74510905416475349941703473 55883179062356512456277605)
          ·
            refine ⟨10478096074191846085552051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55883179062356512456277605 10478096074191846085552051)
            ·
              refine ⟨15717144111287769128328077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10478096074191846085552051 15717144111287769128328077)
              ·
                refine ⟨5893929041732913423123029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15717144111287769128328077 5893929041732913423123029)
                ·
                  refine ⟨69069480957807579177223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5893929041732913423123029 69069480957807579177223)
                  ·
                    rfl

theorem cell23_1210611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 8].length) (baseStart_1210611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210611 prefixEnd_1210611 := by exact prefixLift 1210611
  have htrace : WordTrace (prefixWord ++ tailWord_1210611) baseStart_1210611 baseEnd_1210611 := by
    simpa [prefixWord, tailWord_1210611, baseEnd_1210611] using wordTrace_append hprefix tailTrace_1210611
  have hstable : (prefixWord ++ tailWord_1210611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210611).length < 2 ^ (prefixWord ++ tailWord_1210611).sum := by decide
  have hdescent : baseEnd_1210611 < baseStart_1210611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210689 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1210689 : Nat := 118140960795 + 1210689 * 2 ^ 59
def prefixEnd_1210689 : Nat := 4983230072969 + 3 ^ 40 * 1210689 * 2
def baseEnd_1210689 : Nat := 621665380111318907419649

theorem tailTrace_1210689 : CollatzResearch.WordTrace tailWord_1210689 prefixEnd_1210689 621665380111318907419649 := by
  unfold tailWord_1210689
  simp only [CollatzResearch.WordTrace]
  refine ⟨44157455510887997064571121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29438303673925331376380747 44157455510887997064571121)
  ·
    refine ⟨33118091633165997798428341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44157455510887997064571121 33118091633165997798428341)
    ·
      refine ⟨3104821090609312293602657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33118091633165997798428341 3104821090609312293602657)
      ·
        refine ⟨2328615817956984220201993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3104821090609312293602657 2328615817956984220201993)
        ·
          refine ⟨1746461863467738165151495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2328615817956984220201993 1746461863467738165151495)
          ·
            refine ⟨2619692795201607247727243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746461863467738165151495 2619692795201607247727243)
            ·
              refine ⟨3929539192802410871590865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2619692795201607247727243 3929539192802410871590865)
              ·
                refine ⟨2947154394601808153693149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3929539192802410871590865 2947154394601808153693149)
                ·
                  refine ⟨1105182897975678057634931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2947154394601808153693149 1105182897975678057634931)
                  ·
                    refine ⟨1657774346963517086452397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1105182897975678057634931 1657774346963517086452397)
                    ·
                      refine ⟨621665380111318907419649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1657774346963517086452397 621665380111318907419649)
                      ·
                        rfl

theorem cell23_1210689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1210689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210689 prefixEnd_1210689 := by exact prefixLift 1210689
  have htrace : WordTrace (prefixWord ++ tailWord_1210689) baseStart_1210689 baseEnd_1210689 := by
    simpa [prefixWord, tailWord_1210689, baseEnd_1210689] using wordTrace_append hprefix tailTrace_1210689
  have hstable : (prefixWord ++ tailWord_1210689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210689).length < 2 ^ (prefixWord ++ tailWord_1210689).sum := by decide
  have hdescent : baseEnd_1210689 < baseStart_1210689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210695 : List Nat := [1, 1, 4, 1, 2, 2, 2, 4, 1, 1, 4]
def baseStart_1210695 : Nat := 118140960795 + 1210695 * 2 ^ 59
def prefixEnd_1210695 : Nat := 4983230072969 + 3 ^ 40 * 1210695 * 2
def baseEnd_1210695 : Nat := 621668460995245883944621

theorem tailTrace_1210695 : CollatzResearch.WordTrace tailWord_1210695 prefixEnd_1210695 621668460995245883944621 := by
  unfold tailWord_1210695
  simp only [CollatzResearch.WordTrace]
  refine ⟨44157674348866260089289539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29438449565910840059526359 44157674348866260089289539)
  ·
    refine ⟨66236511523299390133934309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44157674348866260089289539 66236511523299390133934309)
    ·
      refine ⟨12419345910618635650112683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66236511523299390133934309 12419345910618635650112683)
      ·
        refine ⟨18629018865927953475169025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12419345910618635650112683 18629018865927953475169025)
        ·
          refine ⟨13971764149445965106376769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18629018865927953475169025 13971764149445965106376769)
          ·
            refine ⟨10478823112084473829782577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13971764149445965106376769 10478823112084473829782577)
            ·
              refine ⟨7859117334063355372336933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10478823112084473829782577 7859117334063355372336933)
              ·
                refine ⟨1473584500136879132313175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7859117334063355372336933 1473584500136879132313175)
                ·
                  refine ⟨2210376750205318698469763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473584500136879132313175 2210376750205318698469763)
                  ·
                    refine ⟨3315565125307978047704645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2210376750205318698469763 3315565125307978047704645)
                    ·
                      refine ⟨621668460995245883944621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3315565125307978047704645 621668460995245883944621)
                      ·
                        rfl

theorem cell23_1210695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_1210695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210695 prefixEnd_1210695 := by exact prefixLift 1210695
  have htrace : WordTrace (prefixWord ++ tailWord_1210695) baseStart_1210695 baseEnd_1210695 := by
    simpa [prefixWord, tailWord_1210695, baseEnd_1210695] using wordTrace_append hprefix tailTrace_1210695
  have hstable : (prefixWord ++ tailWord_1210695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210695).length < 2 ^ (prefixWord ++ tailWord_1210695).sum := by decide
  have hdescent : baseEnd_1210695 < baseStart_1210695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210709 : List Nat := [1, 3, 2, 2, 4, 2, 2, 1, 1, 5]
def baseStart_1210709 : Nat := 118140960795 + 1210709 * 2 ^ 59
def prefixEnd_1210709 : Nat := 4983230072969 + 3 ^ 40 * 1210709 * 2
def baseEnd_1210709 : Nat := 207225216574802943056519

theorem tailTrace_1210709 : CollatzResearch.WordTrace tailWord_1210709 prefixEnd_1210709 207225216574802943056519 := by
  unfold tailWord_1210709
  simp only [CollatzResearch.WordTrace]
  refine ⟨44158184970815540480299181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29438789980543693653532787 44158184970815540480299181)
  ·
    refine ⟨16559319364055827680112193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44158184970815540480299181 16559319364055827680112193)
    ·
      refine ⟨12419489523041870760084145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16559319364055827680112193 12419489523041870760084145)
      ·
        refine ⟨9314617142281403070063109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12419489523041870760084145 9314617142281403070063109)
        ·
          refine ⟨1746490714177763075636833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9314617142281403070063109 1746490714177763075636833)
          ·
            refine ⟨1309868035633322306727625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1746490714177763075636833 1309868035633322306727625)
            ·
              refine ⟨982401026724991730045719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1309868035633322306727625 982401026724991730045719)
              ·
                refine ⟨1473601540087487595068579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982401026724991730045719 1473601540087487595068579)
                ·
                  refine ⟨2210402310131231392602869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473601540087487595068579 2210402310131231392602869)
                  ·
                    refine ⟨207225216574802943056519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2210402310131231392602869 207225216574802943056519)
                    ·
                      rfl

theorem cell23_1210709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_1210709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210709 prefixEnd_1210709 := by exact prefixLift 1210709
  have htrace : WordTrace (prefixWord ++ tailWord_1210709) baseStart_1210709 baseEnd_1210709 := by
    simpa [prefixWord, tailWord_1210709, baseEnd_1210709] using wordTrace_append hprefix tailTrace_1210709
  have hstable : (prefixWord ++ tailWord_1210709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210709).length < 2 ^ (prefixWord ++ tailWord_1210709).sum := by decide
  have hdescent : baseEnd_1210709 < baseStart_1210709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210722 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1210722 : Nat := 118140960795 + 1210722 * 2 ^ 59
def prefixEnd_1210722 : Nat := 4983230072969 + 3 ^ 40 * 1210722 * 2
def baseEnd_1210722 : Nat := 207227441657639092768999

theorem tailTrace_1210722 : CollatzResearch.WordTrace tailWord_1210722 prefixEnd_1210722 207227441657639092768999 := by
  unfold tailWord_1210722
  simp only [CollatzResearch.WordTrace]
  refine ⟨11039664779942110925130605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29439106079845629133681613 11039664779942110925130605)
  ·
    refine ⟨4139874292478291596923977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11039664779942110925130605 4139874292478291596923977)
    ·
      refine ⟨3104905719358718697692983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4139874292478291596923977 3104905719358718697692983)
      ·
        refine ⟨4657358579038078046539475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3104905719358718697692983 4657358579038078046539475)
        ·
          refine ⟨6986037868557117069809213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4657358579038078046539475 6986037868557117069809213)
          ·
            refine ⟨2619764200708918901178455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6986037868557117069809213 2619764200708918901178455)
            ·
              refine ⟨3929646301063378351767683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2619764200708918901178455 3929646301063378351767683)
              ·
                refine ⟨5894469451595067527651525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3929646301063378351767683 5894469451595067527651525)
                ·
                  refine ⟨1105213022174075161434661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5894469451595067527651525 1105213022174075161434661)
                  ·
                    refine ⟨207227441657639092768999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1105213022174075161434661 207227441657639092768999)
                    ·
                      rfl

theorem cell23_1210722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1210722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210722 prefixEnd_1210722 := by exact prefixLift 1210722
  have htrace : WordTrace (prefixWord ++ tailWord_1210722) baseStart_1210722 baseEnd_1210722 := by
    simpa [prefixWord, tailWord_1210722, baseEnd_1210722] using wordTrace_append hprefix tailTrace_1210722
  have hstable : (prefixWord ++ tailWord_1210722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210722).length < 2 ^ (prefixWord ++ tailWord_1210722).sum := by decide
  have hdescent : baseEnd_1210722 < baseStart_1210722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210729 : List Nat := [1, 2, 1, 1, 1, 3, 3, 6, 1, 2, 2]
def baseStart_1210729 : Nat := 118140960795 + 1210729 * 2 ^ 59
def prefixEnd_1210729 : Nat := 4983230072969 + 3 ^ 40 * 1210729 * 2
def baseEnd_1210729 : Nat := 621685919337498750919465

theorem tailTrace_1210729 : CollatzResearch.WordTrace tailWord_1210729 prefixEnd_1210729 621685919337498750919465 := by
  unfold tailWord_1210729
  simp only [CollatzResearch.WordTrace]
  refine ⟨44158914430743083896027241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29439276287162055930684827 44158914430743083896027241)
  ·
    refine ⟨33119185823057312922020431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44158914430743083896027241 33119185823057312922020431)
    ·
      refine ⟨49678778734585969383030647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33119185823057312922020431 49678778734585969383030647)
      ·
        refine ⟨74518168101878954074545971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49678778734585969383030647 74518168101878954074545971)
        ·
          refine ⟨111777252152818431111818957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74518168101878954074545971 111777252152818431111818957)
          ·
            refine ⟨41916469557306911666932109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111777252152818431111818957 41916469557306911666932109)
            ·
              refine ⟨15718676083990091875099541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41916469557306911666932109 15718676083990091875099541)
              ·
                refine ⟨736812941437035556645291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15718676083990091875099541 736812941437035556645291)
                ·
                  refine ⟨1105219412155553334967937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 736812941437035556645291 1105219412155553334967937)
                  ·
                    refine ⟨828914559116665001225953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1105219412155553334967937 828914559116665001225953)
                    ·
                      refine ⟨621685919337498750919465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 828914559116665001225953 621685919337498750919465)
                      ·
                        rfl

theorem cell23_1210729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 1, 2, 2].length) (baseStart_1210729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210729 prefixEnd_1210729 := by exact prefixLift 1210729
  have htrace : WordTrace (prefixWord ++ tailWord_1210729) baseStart_1210729 baseEnd_1210729 := by
    simpa [prefixWord, tailWord_1210729, baseEnd_1210729] using wordTrace_append hprefix tailTrace_1210729
  have hstable : (prefixWord ++ tailWord_1210729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210729).length < 2 ^ (prefixWord ++ tailWord_1210729).sum := by decide
  have hdescent : baseEnd_1210729 < baseStart_1210729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210768 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 4]
def baseStart_1210768 : Nat := 118140960795 + 1210768 * 2 ^ 59
def prefixEnd_1210768 : Nat := 4983230072969 + 3 ^ 40 * 1210768 * 2
def baseEnd_1210768 : Nat := 621705945083024098331785

theorem tailTrace_1210768 : CollatzResearch.WordTrace tailWord_1210768 prefixEnd_1210768 621705945083024098331785 := by
  unfold tailWord_1210768
  simp only [CollatzResearch.WordTrace]
  refine ⟨22080168438800896778348479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29440224585067862371131305 22080168438800896778348479)
  ·
    refine ⟨33120252658201345167522719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22080168438800896778348479 33120252658201345167522719)
    ·
      refine ⟨49680378987302017751284079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33120252658201345167522719 49680378987302017751284079)
      ·
        refine ⟨74520568480953026626926119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49680378987302017751284079 74520568480953026626926119)
        ·
          refine ⟨111780852721429539940389179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74520568480953026626926119 111780852721429539940389179)
          ·
            refine ⟨167671279082144309910583769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111780852721429539940389179 167671279082144309910583769)
            ·
              refine ⟨125753459311608232432937827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167671279082144309910583769 125753459311608232432937827)
              ·
                refine ⟨188630188967412348649406741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125753459311608232432937827 188630188967412348649406741)
                ·
                  refine ⟨8842040107847453842940941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 188630188967412348649406741 8842040107847453842940941)
                  ·
                    refine ⟨3315765040442795191102853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8842040107847453842940941 3315765040442795191102853)
                    ·
                      refine ⟨621705945083024098331785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3315765040442795191102853 621705945083024098331785)
                      ·
                        rfl

theorem cell23_1210768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_1210768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210768 prefixEnd_1210768 := by exact prefixLift 1210768
  have htrace : WordTrace (prefixWord ++ tailWord_1210768) baseStart_1210768 baseEnd_1210768 := by
    simpa [prefixWord, tailWord_1210768, baseEnd_1210768] using wordTrace_append hprefix tailTrace_1210768
  have hstable : (prefixWord ++ tailWord_1210768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210768).length < 2 ^ (prefixWord ++ tailWord_1210768).sum := by decide
  have hdescent : baseEnd_1210768 < baseStart_1210768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210802 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2]
def baseStart_1210802 : Nat := 118140960795 + 1210802 * 2 ^ 59
def prefixEnd_1210802 : Nat := 4983230072969 + 3 ^ 40 * 1210802 * 2
def baseEnd_1210802 : Nat := 621723403425276965306629

theorem tailTrace_1210802 : CollatzResearch.WordTrace tailWord_1210802 prefixEnd_1210802 621723403425276965306629 := by
  unfold tailWord_1210802
  simp only [CollatzResearch.WordTrace]
  refine ⟨11040394239869654340858665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29441051306319078242289773 11040394239869654340858665)
  ·
    refine ⟨8280295679902240755643999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11040394239869654340858665 8280295679902240755643999)
    ·
      refine ⟨12420443519853361133465999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8280295679902240755643999 12420443519853361133465999)
      ·
        refine ⟨18630665279780041700198999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12420443519853361133465999 18630665279780041700198999)
        ·
          refine ⟨27945997919670062550298499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18630665279780041700198999 27945997919670062550298499)
          ·
            refine ⟨41918996879505093825447749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27945997919670062550298499 41918996879505093825447749)
            ·
              refine ⟨7859811914907205092271453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41918996879505093825447749 7859811914907205092271453)
              ·
                refine ⟨2947429468090201909601795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7859811914907205092271453 2947429468090201909601795)
                ·
                  refine ⟨4421144202135302864402693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2947429468090201909601795 4421144202135302864402693)
                  ·
                    refine ⟨828964537900369287075505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4421144202135302864402693 828964537900369287075505)
                    ·
                      refine ⟨621723403425276965306629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 828964537900369287075505 621723403425276965306629)
                      ·
                        rfl

theorem cell23_1210802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_1210802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210802 prefixEnd_1210802 := by exact prefixLift 1210802
  have htrace : WordTrace (prefixWord ++ tailWord_1210802) baseStart_1210802 baseEnd_1210802 := by
    simpa [prefixWord, tailWord_1210802, baseEnd_1210802] using wordTrace_append hprefix tailTrace_1210802
  have hstable : (prefixWord ++ tailWord_1210802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210802).length < 2 ^ (prefixWord ++ tailWord_1210802).sum := by decide
  have hdescent : baseEnd_1210802 < baseStart_1210802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210808 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 9]
def baseStart_1210808 : Nat := 118140960795 + 1210808 * 2 ^ 59
def prefixEnd_1210808 : Nat := 4983230072969 + 3 ^ 40 * 1210808 * 2
def baseEnd_1210808 : Nat := 69080720478800437981289

theorem tailTrace_1210808 : CollatzResearch.WordTrace tailWord_1210808 prefixEnd_1210808 69080720478800437981289 := by
  unfold tailWord_1210808
  simp only [CollatzResearch.WordTrace]
  refine ⟨22080897898728440194076539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29441197198304586925435385 22080897898728440194076539)
  ·
    refine ⟨33121346848092660291114809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22080897898728440194076539 33121346848092660291114809)
    ·
      refine ⟨24841010136069495218336107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33121346848092660291114809 24841010136069495218336107)
      ·
        refine ⟨37261515204104242827504161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24841010136069495218336107 37261515204104242827504161)
        ·
          refine ⟨27946136403078182120628121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37261515204104242827504161 27946136403078182120628121)
          ·
            refine ⟨20959602302308636590471091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27946136403078182120628121 20959602302308636590471091)
            ·
              refine ⟨31439403453462954885706637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20959602302308636590471091 31439403453462954885706637)
              ·
                refine ⟨11789776295048608082139989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31439403453462954885706637 11789776295048608082139989)
                ·
                  refine ⟨69080720478800437981289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11789776295048608082139989 69080720478800437981289)
                  ·
                    rfl

theorem cell23_1210808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 9].length) (baseStart_1210808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210808 prefixEnd_1210808 := by exact prefixLift 1210808
  have htrace : WordTrace (prefixWord ++ tailWord_1210808) baseStart_1210808 baseEnd_1210808 := by
    simpa [prefixWord, tailWord_1210808, baseEnd_1210808] using wordTrace_append hprefix tailTrace_1210808
  have hstable : (prefixWord ++ tailWord_1210808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210808).length < 2 ^ (prefixWord ++ tailWord_1210808).sum := by decide
  have hdescent : baseEnd_1210808 < baseStart_1210808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210836 : List Nat := [2, 4, 1, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_1210836 : Nat := 118140960795 + 1210836 * 2 ^ 59
def prefixEnd_1210836 : Nat := 4983230072969 + 3 ^ 40 * 1210836 * 2
def baseEnd_1210836 : Nat := 621740861767529832281473

theorem tailTrace_1210836 : CollatzResearch.WordTrace tailWord_1210836 prefixEnd_1210836 621740861767529832281473 := by
  unfold tailWord_1210836
  simp only [CollatzResearch.WordTrace]
  refine ⟨22081408520677720585086181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29441878027570294113448241 22081408520677720585086181)
  ·
    refine ⟨4140264097627072609703659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22081408520677720585086181 4140264097627072609703659)
    ·
      refine ⟨6210396146440608914555489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4140264097627072609703659 6210396146440608914555489)
      ·
        refine ⟨4657797109830456685916617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6210396146440608914555489 4657797109830456685916617)
        ·
          refine ⟨3493347832372842514437463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4657797109830456685916617 3493347832372842514437463)
          ·
            refine ⟨5240021748559263771656195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3493347832372842514437463 5240021748559263771656195)
            ·
              refine ⟨7860032622838895657484293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5240021748559263771656195 7860032622838895657484293)
              ·
                refine ⟨1473756116782292935778305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7860032622838895657484293 1473756116782292935778305)
                ·
                  refine ⟨1105317087586719701833729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1473756116782292935778305 1105317087586719701833729)
                  ·
                    refine ⟨828987815690039776375297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1105317087586719701833729 828987815690039776375297)
                    ·
                      refine ⟨621740861767529832281473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 828987815690039776375297 621740861767529832281473)
                      ·
                        rfl

theorem cell23_1210836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_1210836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210836 prefixEnd_1210836 := by exact prefixLift 1210836
  have htrace : WordTrace (prefixWord ++ tailWord_1210836) baseStart_1210836 baseEnd_1210836 := by
    simpa [prefixWord, tailWord_1210836, baseEnd_1210836] using wordTrace_append hprefix tailTrace_1210836
  have hstable : (prefixWord ++ tailWord_1210836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210836).length < 2 ^ (prefixWord ++ tailWord_1210836).sum := by decide
  have hdescent : baseEnd_1210836 < baseStart_1210836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210842 : List Nat := [3, 1, 1, 2, 3, 1, 3, 4, 5]
def baseStart_1210842 : Nat := 118140960795 + 1210842 * 2 ^ 59
def prefixEnd_1210842 : Nat := 4983230072969 + 3 ^ 40 * 1210842 * 2
def baseEnd_1210842 : Nat := 69082660294606312089605

theorem tailTrace_1210842 : CollatzResearch.WordTrace tailWord_1210842 prefixEnd_1210842 69082660294606312089605 := by
  unfold tailWord_1210842
  simp only [CollatzResearch.WordTrace]
  refine ⟨11040758969833426048722695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29442023919555802796593853 11040758969833426048722695)
  ·
    refine ⟨16561138454750139073084043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11040758969833426048722695 16561138454750139073084043)
    ·
      refine ⟨24841707682125208609626065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16561138454750139073084043 24841707682125208609626065)
      ·
        refine ⟨18631280761593906457219549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24841707682125208609626065 18631280761593906457219549)
        ·
          refine ⟨6986730285597714921457331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18631280761593906457219549 6986730285597714921457331)
          ·
            refine ⟨10480095428396572382185997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6986730285597714921457331 10480095428396572382185997)
            ·
              refine ⟨3930035785648714643319749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10480095428396572382185997 3930035785648714643319749)
              ·
                refine ⟨736881709809133995622453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3930035785648714643319749 736881709809133995622453)
                ·
                  refine ⟨69082660294606312089605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 736881709809133995622453 69082660294606312089605)
                  ·
                    rfl

theorem cell23_1210842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 5].length) (baseStart_1210842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210842 prefixEnd_1210842 := by exact prefixLift 1210842
  have htrace : WordTrace (prefixWord ++ tailWord_1210842) baseStart_1210842 baseEnd_1210842 := by
    simpa [prefixWord, tailWord_1210842, baseEnd_1210842] using wordTrace_append hprefix tailTrace_1210842
  have hstable : (prefixWord ++ tailWord_1210842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210842).length < 2 ^ (prefixWord ++ tailWord_1210842).sum := by decide
  have hdescent : baseEnd_1210842 < baseStart_1210842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210855 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 1, 7]
def baseStart_1210855 : Nat := 118140960795 + 1210855 * 2 ^ 59
def prefixEnd_1210855 : Nat := 4983230072969 + 3 ^ 40 * 1210855 * 2
def baseEnd_1210855 : Nat := 207250205966655085981295

theorem tailTrace_1210855 : CollatzResearch.WordTrace tailWord_1210855 prefixEnd_1210855 207250205966655085981295 := by
  unfold tailWord_1210855
  simp only [CollatzResearch.WordTrace]
  refine ⟨44163510028286607415114019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29442340018857738276742679 44163510028286607415114019)
  ·
    refine ⟨66245265042429911122671029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44163510028286607415114019 66245265042429911122671029)
    ·
      refine ⟨6210493597727804167750409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66245265042429911122671029 6210493597727804167750409)
      ·
        refine ⟨4657870198295853125812807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6210493597727804167750409 4657870198295853125812807)
        ·
          refine ⟨6986805297443779688719211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4657870198295853125812807 6986805297443779688719211)
          ·
            refine ⟨10480207946165669533078817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6986805297443779688719211 10480207946165669533078817)
            ·
              refine ⟨7860155959624252149809113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10480207946165669533078817 7860155959624252149809113)
              ·
                refine ⟨5895116969718189112356835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7860155959624252149809113 5895116969718189112356835)
                ·
                  refine ⟨8842675454577283668535253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5895116969718189112356835 8842675454577283668535253)
                  ·
                    refine ⟨207250205966655085981295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8842675454577283668535253 207250205966655085981295)
                    ·
                      rfl

theorem cell23_1210855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_1210855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210855 prefixEnd_1210855 := by exact prefixLift 1210855
  have htrace : WordTrace (prefixWord ++ tailWord_1210855) baseStart_1210855 baseEnd_1210855 := by
    simpa [prefixWord, tailWord_1210855, baseEnd_1210855] using wordTrace_append hprefix tailTrace_1210855
  have hstable : (prefixWord ++ tailWord_1210855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210855).length < 2 ^ (prefixWord ++ tailWord_1210855).sum := by decide
  have hdescent : baseEnd_1210855 < baseStart_1210855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210895 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 3]
def baseStart_1210895 : Nat := 118140960795 + 1210895 * 2 ^ 59
def prefixEnd_1210895 : Nat := 4983230072969 + 3 ^ 40 * 1210895 * 2
def baseEnd_1210895 : Nat := 621771157126145101443701

theorem tailTrace_1210895 : CollatzResearch.WordTrace tailWord_1210895 prefixEnd_1210895 621771157126145101443701 := by
  unfold tailWord_1210895
  simp only [CollatzResearch.WordTrace]
  refine ⟨44164968948141694246570139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29443312632094462831046759 44164968948141694246570139)
  ·
    refine ⟨66247453422212541369855209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44164968948141694246570139 66247453422212541369855209)
    ·
      refine ⟨49685590066659406027391407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66247453422212541369855209 49685590066659406027391407)
      ·
        refine ⟨74528385099989109041087111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49685590066659406027391407 74528385099989109041087111)
        ·
          refine ⟨111792577649983663561630667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74528385099989109041087111 111792577649983663561630667)
          ·
            refine ⟨167688866474975495342446001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111792577649983663561630667 167688866474975495342446001)
            ·
              refine ⟨125766649856231621506834501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167688866474975495342446001 125766649856231621506834501)
              ·
                refine ⟨23581246848043429032531469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125766649856231621506834501 23581246848043429032531469)
                ·
                  refine ⟨8842967568016285887199301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23581246848043429032531469 8842967568016285887199301)
                  ·
                    refine ⟨1658056419003053603849869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8842967568016285887199301 1658056419003053603849869)
                    ·
                      refine ⟨621771157126145101443701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1658056419003053603849869 621771157126145101443701)
                      ·
                        rfl

theorem cell23_1210895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 3].length) (baseStart_1210895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210895 prefixEnd_1210895 := by exact prefixLift 1210895
  have htrace : WordTrace (prefixWord ++ tailWord_1210895) baseStart_1210895 baseEnd_1210895 := by
    simpa [prefixWord, tailWord_1210895, baseEnd_1210895] using wordTrace_append hprefix tailTrace_1210895
  have hstable : (prefixWord ++ tailWord_1210895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210895).length < 2 ^ (prefixWord ++ tailWord_1210895).sum := by decide
  have hdescent : baseEnd_1210895 < baseStart_1210895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210909 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_1210909 : Nat := 118140960795 + 1210909 * 2 ^ 59
def prefixEnd_1210909 : Nat := 4983230072969 + 3 ^ 40 * 1210909 * 2
def baseEnd_1210909 : Nat := 621778345855308046668637

theorem tailTrace_1210909 : CollatzResearch.WordTrace tailWord_1210909 prefixEnd_1210909 621778345855308046668637 := by
  unfold tailWord_1210909
  simp only [CollatzResearch.WordTrace]
  refine ⟨44165479570090974637579781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29443653046727316425053187 44165479570090974637579781)
  ·
    refine ⟨8281027419392057744546209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44165479570090974637579781 8281027419392057744546209)
    ·
      refine ⟨6210770564544043308409657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8281027419392057744546209 6210770564544043308409657)
      ·
        refine ⟨4658077923408032481307243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6210770564544043308409657 4658077923408032481307243)
        ·
          refine ⟨6987116885112048721960865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4658077923408032481307243 6987116885112048721960865)
          ·
            refine ⟨5240337663834036541470649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6987116885112048721960865 5240337663834036541470649)
            ·
              refine ⟨3930253247875527406102987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5240337663834036541470649 3930253247875527406102987)
              ·
                refine ⟨5895379871813291109154481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3930253247875527406102987 5895379871813291109154481)
                ·
                  refine ⟨4421534903859968331865861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5895379871813291109154481 4421534903859968331865861)
                  ·
                    refine ⟨829037794473744062224849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4421534903859968331865861 829037794473744062224849)
                    ·
                      refine ⟨621778345855308046668637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 829037794473744062224849 621778345855308046668637)
                      ·
                        rfl

theorem cell23_1210909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_1210909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210909 prefixEnd_1210909 := by exact prefixLift 1210909
  have htrace : WordTrace (prefixWord ++ tailWord_1210909) baseStart_1210909 baseEnd_1210909 := by
    simpa [prefixWord, tailWord_1210909, baseEnd_1210909] using wordTrace_append hprefix tailTrace_1210909
  have hstable : (prefixWord ++ tailWord_1210909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210909).length < 2 ^ (prefixWord ++ tailWord_1210909).sum := by decide
  have hdescent : baseEnd_1210909 < baseStart_1210909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210959 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 3, 1, 3]
def baseStart_1210959 : Nat := 118140960795 + 1210959 * 2 ^ 59
def prefixEnd_1210959 : Nat := 4983230072969 + 3 ^ 40 * 1210959 * 2
def baseEnd_1210959 : Nat := 621804019888032851043407

theorem tailTrace_1210959 : CollatzResearch.WordTrace tailWord_1210959 prefixEnd_1210959 621804019888032851043407 := by
  unfold tailWord_1210959
  simp only [CollatzResearch.WordTrace]
  refine ⟨44167303219909833176899931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29444868813273222117933287 44167303219909833176899931)
  ·
    refine ⟨66250954829864749765349897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44167303219909833176899931 66250954829864749765349897)
    ·
      refine ⟨49688216122398562324012423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66250954829864749765349897 49688216122398562324012423)
      ·
        refine ⟨74532324183597843486018635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49688216122398562324012423 74532324183597843486018635)
        ·
          refine ⟨111798486275396765229027953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74532324183597843486018635 111798486275396765229027953)
          ·
            refine ⟨83848864706547573921770965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111798486275396765229027953 83848864706547573921770965)
            ·
              refine ⟨1965207766559708763791507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 83848864706547573921770965 1965207766559708763791507)
              ·
                refine ⟨2947811649839563145687261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1965207766559708763791507 2947811649839563145687261)
                ·
                  refine ⟨1105429368689836179632723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2947811649839563145687261 1105429368689836179632723)
                  ·
                    refine ⟨1658144053034754269449085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1105429368689836179632723 1658144053034754269449085)
                    ·
                      refine ⟨621804019888032851043407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1658144053034754269449085 621804019888032851043407)
                      ·
                        rfl

theorem cell23_1210959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 3, 1, 3].length) (baseStart_1210959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210959 prefixEnd_1210959 := by exact prefixLift 1210959
  have htrace : WordTrace (prefixWord ++ tailWord_1210959) baseStart_1210959 baseEnd_1210959 := by
    simpa [prefixWord, tailWord_1210959, baseEnd_1210959] using wordTrace_append hprefix tailTrace_1210959
  have hstable : (prefixWord ++ tailWord_1210959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210959).length < 2 ^ (prefixWord ++ tailWord_1210959).sum := by decide
  have hdescent : baseEnd_1210959 < baseStart_1210959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210962 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_1210962 : Nat := 118140960795 + 1210962 * 2 ^ 59
def prefixEnd_1210962 : Nat := 4983230072969 + 3 ^ 40 * 1210962 * 2
def baseEnd_1210962 : Nat := 207268520109998779768631

theorem tailTrace_1210962 : CollatzResearch.WordTrace tailWord_1210962 prefixEnd_1210962 207268520109998779768631 := by
  unfold tailWord_1210962
  simp only [CollatzResearch.WordTrace]
  refine ⟨11041853159724741172314785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29444941759265976459506093 11041853159724741172314785)
  ·
    refine ⟨8281389869793555879236089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11041853159724741172314785 8281389869793555879236089)
    ·
      refine ⟨6211042402345166909427067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8281389869793555879236089 6211042402345166909427067)
      ·
        refine ⟨9316563603517750364140601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6211042402345166909427067 9316563603517750364140601)
        ·
          refine ⟨6987422702638312773105451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9316563603517750364140601 6987422702638312773105451)
          ·
            refine ⟨10481134053957469159658177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6987422702638312773105451 10481134053957469159658177)
            ·
              refine ⟨7860850540468101869743633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10481134053957469159658177 7860850540468101869743633)
              ·
                refine ⟨5895637905351076402307725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7860850540468101869743633 5895637905351076402307725)
                ·
                  refine ⟨2210864214506653650865397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5895637905351076402307725 2210864214506653650865397)
                  ·
                    refine ⟨207268520109998779768631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2210864214506653650865397 207268520109998779768631)
                    ·
                      rfl

theorem cell23_1210962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_1210962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210962 prefixEnd_1210962 := by exact prefixLift 1210962
  have htrace : WordTrace (prefixWord ++ tailWord_1210962) baseStart_1210962 baseEnd_1210962 := by
    simpa [prefixWord, tailWord_1210962, baseEnd_1210962] using wordTrace_append hprefix tailTrace_1210962
  have hstable : (prefixWord ++ tailWord_1210962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210962).length < 2 ^ (prefixWord ++ tailWord_1210962).sum := by decide
  have hdescent : baseEnd_1210962 < baseStart_1210962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210975 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 5, 6]
def baseStart_1210975 : Nat := 118140960795 + 1210975 * 2 ^ 59
def prefixEnd_1210975 : Nat := 4983230072969 + 3 ^ 40 * 1210975 * 2
def baseEnd_1210975 : Nat := 207270745192834929481111

theorem tailTrace_1210975 : CollatzResearch.WordTrace tailWord_1210975 prefixEnd_1210975 207270745192834929481111 := by
  unfold tailWord_1210975
  simp only [CollatzResearch.WordTrace]
  refine ⟨44167886787851867909482379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29445257858567911939654919 44167886787851867909482379)
  ·
    refine ⟨66251830181777801864223569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44167886787851867909482379 66251830181777801864223569)
    ·
      refine ⟨49688872636333351398167677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66251830181777801864223569 49688872636333351398167677)
      ·
        refine ⟨18633327238625006774312879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49688872636333351398167677 18633327238625006774312879)
        ·
          refine ⟨27949990857937510161469319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18633327238625006774312879 27949990857937510161469319)
          ·
            refine ⟨41924986286906265242203979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27949990857937510161469319 41924986286906265242203979)
            ·
              refine ⟨62887479430359397863305969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41924986286906265242203979 62887479430359397863305969)
              ·
                refine ⟨47165609572769548397479477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62887479430359397863305969 47165609572769548397479477)
                ·
                  refine ⟨4421775897447145162263701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47165609572769548397479477 4421775897447145162263701)
                  ·
                    refine ⟨207270745192834929481111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4421775897447145162263701 207270745192834929481111)
                    ·
                      rfl

theorem cell23_1210975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 6].length) (baseStart_1210975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210975 prefixEnd_1210975 := by exact prefixLift 1210975
  have htrace : WordTrace (prefixWord ++ tailWord_1210975) baseStart_1210975 baseEnd_1210975 := by
    simpa [prefixWord, tailWord_1210975, baseEnd_1210975] using wordTrace_append hprefix tailTrace_1210975
  have hstable : (prefixWord ++ tailWord_1210975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210975).length < 2 ^ (prefixWord ++ tailWord_1210975).sum := by decide
  have hdescent : baseEnd_1210975 < baseStart_1210975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210986 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_1210986 : Nat := 118140960795 + 1210986 * 2 ^ 59
def prefixEnd_1210986 : Nat := 4983230072969 + 3 ^ 40 * 1210986 * 2
def baseEnd_1210986 : Nat := 621817883865704245405783

theorem tailTrace_1210986 : CollatzResearch.WordTrace tailWord_1210986 prefixEnd_1210986 621817883865704245405783 := by
  unfold tailWord_1210986
  simp only [CollatzResearch.WordTrace]
  refine ⟨11042071997703004197033203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29445525327208011192088541 11042071997703004197033203)
  ·
    refine ⟨16563107996554506295549805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11042071997703004197033203 16563107996554506295549805)
    ·
      refine ⟨6211165498707939860831177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16563107996554506295549805 6211165498707939860831177)
      ·
        refine ⟨4658374124030954895623383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6211165498707939860831177 4658374124030954895623383)
        ·
          refine ⟨6987561186046432343435075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4658374124030954895623383 6987561186046432343435075)
          ·
            refine ⟨10481341779069648515152613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6987561186046432343435075 10481341779069648515152613)
            ·
              refine ⟨1965251583575559096591115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10481341779069648515152613 1965251583575559096591115)
              ·
                refine ⟨2947877375363338644886673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1965251583575559096591115 2947877375363338644886673)
                ·
                  refine ⟨2210908031522503983665005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2947877375363338644886673 2210908031522503983665005)
                  ·
                    refine ⟨829090511820938993874377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2210908031522503983665005 829090511820938993874377)
                    ·
                      refine ⟨621817883865704245405783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 829090511820938993874377 621817883865704245405783)
                      ·
                        rfl

theorem cell23_1210986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_1210986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210986 prefixEnd_1210986 := by exact prefixLift 1210986
  have htrace : WordTrace (prefixWord ++ tailWord_1210986) baseStart_1210986 baseEnd_1210986 := by
    simpa [prefixWord, tailWord_1210986, baseEnd_1210986] using wordTrace_append hprefix tailTrace_1210986
  have hstable : (prefixWord ++ tailWord_1210986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210986).length < 2 ^ (prefixWord ++ tailWord_1210986).sum := by decide
  have hdescent : baseEnd_1210986 < baseStart_1210986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210995 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 6]
def baseStart_1210995 : Nat := 118140960795 + 1210995 * 2 ^ 59
def prefixEnd_1210995 : Nat := 4983230072969 + 3 ^ 40 * 1210995 * 2
def baseEnd_1210995 : Nat := 621822505191594710193241

theorem tailTrace_1210995 : CollatzResearch.WordTrace tailWord_1210995 prefixEnd_1210995 621822505191594710193241 := by
  unfold tailWord_1210995
  simp only [CollatzResearch.WordTrace]
  refine ⟨44168616247779411325210439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29445744165186274216806959 44168616247779411325210439)
  ·
    refine ⟨66252924371669116987815659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44168616247779411325210439 66252924371669116987815659)
    ·
      refine ⟨99379386557503675481723489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66252924371669116987815659 99379386557503675481723489)
      ·
        refine ⟨74534539918127756611292617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99379386557503675481723489 74534539918127756611292617)
        ·
          refine ⟨55900904938595817458469463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74534539918127756611292617 55900904938595817458469463)
          ·
            refine ⟨83851357407893726187704195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55900904938595817458469463 83851357407893726187704195)
            ·
              refine ⟨125777036111840589281556293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83851357407893726187704195 125777036111840589281556293)
              ·
                refine ⟨23583194270970110490291805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125777036111840589281556293 23583194270970110490291805)
                ·
                  refine ⟨8843697851613791433859427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23583194270970110490291805 8843697851613791433859427)
                  ·
                    refine ⟨13265546777420687150789141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8843697851613791433859427 13265546777420687150789141)
                    ·
                      refine ⟨621822505191594710193241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13265546777420687150789141 621822505191594710193241)
                      ·
                        rfl

theorem cell23_1210995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_1210995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1210995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1210995 prefixEnd_1210995 := by exact prefixLift 1210995
  have htrace : WordTrace (prefixWord ++ tailWord_1210995) baseStart_1210995 baseEnd_1210995 := by
    simpa [prefixWord, tailWord_1210995, baseEnd_1210995] using wordTrace_append hprefix tailTrace_1210995
  have hstable : (prefixWord ++ tailWord_1210995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210995).length < 2 ^ (prefixWord ++ tailWord_1210995).sum := by decide
  have hdescent : baseEnd_1210995 < baseStart_1210995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211005 : List Nat := [1, 4, 1, 1, 16]
def baseStart_1211005 : Nat := 118140960795 + 1211005 * 2 ^ 59
def prefixEnd_1211005 : Nat := 4983230072969 + 3 ^ 40 * 1211005 * 2
def baseEnd_1211005 : Nat := 852987160491275268955

theorem tailTrace_1211005 : CollatzResearch.WordTrace tailWord_1211005 prefixEnd_1211005 852987160491275268955 := by
  unfold tailWord_1211005
  simp only [CollatzResearch.WordTrace]
  refine ⟨44168980977743183033074469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29445987318495455355382979 44168980977743183033074469)
  ·
    refine ⟨8281683933326846818701463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44168980977743183033074469 8281683933326846818701463)
    ·
      refine ⟨12422525899990270228052195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8281683933326846818701463 12422525899990270228052195)
      ·
        refine ⟨18633788849985405342078293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12422525899990270228052195 18633788849985405342078293)
        ·
          refine ⟨852987160491275268955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 18633788849985405342078293 852987160491275268955)
          ·
            rfl

theorem cell23_1211005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 16].length) (baseStart_1211005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211005 prefixEnd_1211005 := by exact prefixLift 1211005
  have htrace : WordTrace (prefixWord ++ tailWord_1211005) baseStart_1211005 baseEnd_1211005 := by
    simpa [prefixWord, tailWord_1211005, baseEnd_1211005] using wordTrace_append hprefix tailTrace_1211005
  have hstable : (prefixWord ++ tailWord_1211005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211005).length < 2 ^ (prefixWord ++ tailWord_1211005).sum := by decide
  have hdescent : baseEnd_1211005 < baseStart_1211005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211026 : List Nat := [3, 2, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_1211026 : Nat := 118140960795 + 1211026 * 2 ^ 59
def prefixEnd_1211026 : Nat := 4983230072969 + 3 ^ 40 * 1211026 * 2
def baseEnd_1211026 : Nat := 207279474363961362968533

theorem tailTrace_1211026 : CollatzResearch.WordTrace tailWord_1211026 prefixEnd_1211026 207279474363961362968533 := by
  unfold tailWord_1211026
  simp only [CollatzResearch.WordTrace]
  refine ⟨11042436727666775904897233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29446497940444735746392621 11042436727666775904897233)
  ·
    refine ⟨8281827545750081928672925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11042436727666775904897233 8281827545750081928672925)
    ·
      refine ⟨3105685329656280723252347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8281827545750081928672925 3105685329656280723252347)
      ·
        refine ⟨4658527994484421084878521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3105685329656280723252347 4658527994484421084878521)
        ·
          refine ⟨3493895995863315813658891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4658527994484421084878521 3493895995863315813658891)
          ·
            refine ⟨5240843993794973720488337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3493895995863315813658891 5240843993794973720488337)
            ·
              refine ⟨3930632995346230290366253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5240843993794973720488337 3930632995346230290366253)
              ·
                refine ⟨1473987373254836358887345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3930632995346230290366253 1473987373254836358887345)
                ·
                  refine ⟨1105490529941127269165509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1473987373254836358887345 1105490529941127269165509)
                  ·
                    refine ⟨207279474363961362968533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1105490529941127269165509 207279474363961362968533)
                    ·
                      rfl

theorem cell23_1211026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_1211026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211026 prefixEnd_1211026 := by exact prefixLift 1211026
  have htrace : WordTrace (prefixWord ++ tailWord_1211026) baseStart_1211026 baseEnd_1211026 := by
    simpa [prefixWord, tailWord_1211026, baseEnd_1211026] using wordTrace_append hprefix tailTrace_1211026
  have hstable : (prefixWord ++ tailWord_1211026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211026).length < 2 ^ (prefixWord ++ tailWord_1211026).sum := by decide
  have hdescent : baseEnd_1211026 < baseStart_1211026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211053 : List Nat := [1, 5, 2, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_1211053 : Nat := 118140960795 + 1211053 * 2 ^ 59
def prefixEnd_1211053 : Nat := 4983230072969 + 3 ^ 40 * 1211053 * 2
def baseEnd_1211053 : Nat := 621852287069555483267975

theorem tailTrace_1211053 : CollatzResearch.WordTrace tailWord_1211053 prefixEnd_1211053 621852287069555483267975 := by
  unfold tailWord_1211053
  simp only [CollatzResearch.WordTrace]
  refine ⟨44170731681569287230821813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29447154454379524820547875 44170731681569287230821813)
  ·
    refine ⟨4141006095147120677889545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44170731681569287230821813 4141006095147120677889545)
    ·
      refine ⟨3105754571360340508417159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4141006095147120677889545 3105754571360340508417159)
      ·
        refine ⟨4658631857040510762625739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3105754571360340508417159 4658631857040510762625739)
        ·
          refine ⟨6987947785560766143938609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4658631857040510762625739 6987947785560766143938609)
          ·
            refine ⟨5240960839170574607953957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6987947785560766143938609 5240960839170574607953957)
            ·
              refine ⟨982680157344482738991367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5240960839170574607953957 982680157344482738991367)
              ·
                refine ⟨1474020236016724108487051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982680157344482738991367 1474020236016724108487051)
                ·
                  refine ⟨2211030354025086162730577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474020236016724108487051 2211030354025086162730577)
                  ·
                    refine ⟨1658272765518814622047933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2211030354025086162730577 1658272765518814622047933)
                    ·
                      refine ⟨621852287069555483267975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1658272765518814622047933 621852287069555483267975)
                      ·
                        rfl

theorem cell23_1211053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_1211053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211053 prefixEnd_1211053 := by exact prefixLift 1211053
  have htrace : WordTrace (prefixWord ++ tailWord_1211053) baseStart_1211053 baseEnd_1211053 := by
    simpa [prefixWord, tailWord_1211053, baseEnd_1211053] using wordTrace_append hprefix tailTrace_1211053
  have hstable : (prefixWord ++ tailWord_1211053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211053).length < 2 ^ (prefixWord ++ tailWord_1211053).sum := by decide
  have hdescent : baseEnd_1211053 < baseStart_1211053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211109 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1211109 : Nat := 118140960795 + 1211109 * 2 ^ 59
def prefixEnd_1211109 : Nat := 4983230072969 + 3 ^ 40 * 1211109 * 2
def baseEnd_1211109 : Nat := 621881041986207264167717

theorem tailTrace_1211109 : CollatzResearch.WordTrace tailWord_1211109 prefixEnd_1211109 621881041986207264167717 := by
  unfold tailWord_1211109
  simp only [CollatzResearch.WordTrace]
  refine ⟨44172774169366408794860381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29448516112910939196573587 44172774169366408794860381)
  ·
    refine ⟨16564790313512403298072643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44172774169366408794860381 16564790313512403298072643)
    ·
      refine ⟨24847185470268604947108965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16564790313512403298072643 24847185470268604947108965)
      ·
        refine ⟨4658847275675363427582931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24847185470268604947108965 4658847275675363427582931)
        ·
          refine ⟨6988270913513045141374397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4658847275675363427582931 6988270913513045141374397)
          ·
            refine ⟨2620601592567391928015399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6988270913513045141374397 2620601592567391928015399)
            ·
              refine ⟨3930902388851087892023099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620601592567391928015399 3930902388851087892023099)
              ·
                refine ⟨5896353583276631838034649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3930902388851087892023099 5896353583276631838034649)
                ·
                  refine ⟨4422265187457473878525987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5896353583276631838034649 4422265187457473878525987)
                  ·
                    refine ⟨6633397781186210817788981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4422265187457473878525987 6633397781186210817788981)
                    ·
                      refine ⟨621881041986207264167717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6633397781186210817788981 621881041986207264167717)
                      ·
                        rfl

theorem cell23_1211109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1211109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211109 prefixEnd_1211109 := by exact prefixLift 1211109
  have htrace : WordTrace (prefixWord ++ tailWord_1211109) baseStart_1211109 baseEnd_1211109 := by
    simpa [prefixWord, tailWord_1211109, baseEnd_1211109] using wordTrace_append hprefix tailTrace_1211109
  have hstable : (prefixWord ++ tailWord_1211109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211109).length < 2 ^ (prefixWord ++ tailWord_1211109).sum := by decide
  have hdescent : baseEnd_1211109 < baseStart_1211109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211129 : List Nat := [1, 2, 1, 3, 1, 1, 1, 8, 5]
def baseStart_1211129 : Nat := 118140960795 + 1211129 * 2 ^ 59
def prefixEnd_1211129 : Nat := 4983230072969 + 3 ^ 40 * 1211129 * 2
def baseEnd_1211129 : Nat := 69099034622144131768625

theorem tailTrace_1211129 : CollatzResearch.WordTrace tailWord_1211129 prefixEnd_1211129 69099034622144131768625 := by
  unfold tailWord_1211129
  simp only [CollatzResearch.WordTrace]
  refine ⟨44173503629293952210588441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29449002419529301473725627 44173503629293952210588441)
  ·
    refine ⟨33130127721970464157941331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44173503629293952210588441 33130127721970464157941331)
    ·
      refine ⟨49695191582955696236911997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33130127721970464157941331 49695191582955696236911997)
      ·
        refine ⟨18635696843608386088841999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49695191582955696236911997 18635696843608386088841999)
        ·
          refine ⟨27953545265412579133262999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18635696843608386088841999 27953545265412579133262999)
          ·
            refine ⟨41930317898118868699894499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27953545265412579133262999 41930317898118868699894499)
            ·
              refine ⟨62895476847178303049841749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41930317898118868699894499 62895476847178303049841749)
              ·
                refine ⟨737056369302870738865333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 62895476847178303049841749 737056369302870738865333)
                ·
                  refine ⟨69099034622144131768625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 737056369302870738865333 69099034622144131768625)
                  ·
                    rfl

theorem cell23_1211129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 5].length) (baseStart_1211129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211129 prefixEnd_1211129 := by exact prefixLift 1211129
  have htrace : WordTrace (prefixWord ++ tailWord_1211129) baseStart_1211129 baseEnd_1211129 := by
    simpa [prefixWord, tailWord_1211129, baseEnd_1211129] using wordTrace_append hprefix tailTrace_1211129
  have hstable : (prefixWord ++ tailWord_1211129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211129).length < 2 ^ (prefixWord ++ tailWord_1211129).sum := by decide
  have hdescent : baseEnd_1211129 < baseStart_1211129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211213 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1211213 : Nat := 118140960795 + 1211213 * 2 ^ 59
def prefixEnd_1211213 : Nat := 4983230072969 + 3 ^ 40 * 1211213 * 2
def baseEnd_1211213 : Nat := 621934443974274857267239

theorem tailTrace_1211213 : CollatzResearch.WordTrace tailWord_1211213 prefixEnd_1211213 621934443974274857267239 := by
  unfold tailWord_1211213
  simp only [CollatzResearch.WordTrace]
  refine ⟨44176567360989634556646293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29451044907326423037764195 44176567360989634556646293)
  ·
    refine ⟨2070776595046389119842795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44176567360989634556646293 2070776595046389119842795)
    ·
      refine ⟨3106164892569583679764193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2070776595046389119842795 3106164892569583679764193)
      ·
        refine ⟨2329623669427187759823145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3106164892569583679764193 2329623669427187759823145)
        ·
          refine ⟨1747217752070390819867359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2329623669427187759823145 1747217752070390819867359)
          ·
            refine ⟨2620826628105586229801039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1747217752070390819867359 2620826628105586229801039)
            ·
              refine ⟨3931239942158379344701559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620826628105586229801039 3931239942158379344701559)
              ·
                refine ⟨5896859913237569017052339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3931239942158379344701559 5896859913237569017052339)
                ·
                  refine ⟨8845289869856353525578509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5896859913237569017052339 8845289869856353525578509)
                  ·
                    refine ⟨3316983701196132572091941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8845289869856353525578509 3316983701196132572091941)
                    ·
                      refine ⟨621934443974274857267239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3316983701196132572091941 621934443974274857267239)
                      ·
                        rfl

theorem cell23_1211213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1211213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211213 prefixEnd_1211213 := by exact prefixLift 1211213
  have htrace : WordTrace (prefixWord ++ tailWord_1211213) baseStart_1211213 baseEnd_1211213 := by
    simpa [prefixWord, tailWord_1211213, baseEnd_1211213] using wordTrace_append hprefix tailTrace_1211213
  have hstable : (prefixWord ++ tailWord_1211213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211213).length < 2 ^ (prefixWord ++ tailWord_1211213).sum := by decide
  have hdescent : baseEnd_1211213 < baseStart_1211213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211216 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 3]
def baseStart_1211216 : Nat := 118140960795 + 1211216 * 2 ^ 59
def prefixEnd_1211216 : Nat := 4983230072969 + 3 ^ 40 * 1211216 * 2
def baseEnd_1211216 : Nat := 621935984416238345529725

theorem tailTrace_1211216 : CollatzResearch.WordTrace tailWord_1211216 prefixEnd_1211216 621935984416238345529725 := by
  unfold tailWord_1211216
  simp only [CollatzResearch.WordTrace]
  refine ⟨22088338389989383034502751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29451117853319177379337001 22088338389989383034502751)
  ·
    refine ⟨33132507584984074551754127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22088338389989383034502751 33132507584984074551754127)
    ·
      refine ⟨49698761377476111827631191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33132507584984074551754127 49698761377476111827631191)
      ·
        refine ⟨74548142066214167741446787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49698761377476111827631191 74548142066214167741446787)
        ·
          refine ⟨111822213099321251612170181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74548142066214167741446787 111822213099321251612170181)
          ·
            refine ⟨20966664956122734677281909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111822213099321251612170181 20966664956122734677281909)
            ·
              refine ⟨1965624839636506375995179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20966664956122734677281909 1965624839636506375995179)
              ·
                refine ⟨2948437259454759563992769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1965624839636506375995179 2948437259454759563992769)
                ·
                  refine ⟨2211327944591069672994577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2948437259454759563992769 2211327944591069672994577)
                  ·
                    refine ⟨1658495958443302254745933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2211327944591069672994577 1658495958443302254745933)
                    ·
                      refine ⟨621935984416238345529725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1658495958443302254745933 621935984416238345529725)
                      ·
                        rfl

theorem cell23_1211216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 3].length) (baseStart_1211216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211216 prefixEnd_1211216 := by exact prefixLift 1211216
  have htrace : WordTrace (prefixWord ++ tailWord_1211216) baseStart_1211216 baseEnd_1211216 := by
    simpa [prefixWord, tailWord_1211216, baseEnd_1211216] using wordTrace_append hprefix tailTrace_1211216
  have hstable : (prefixWord ++ tailWord_1211216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211216).length < 2 ^ (prefixWord ++ tailWord_1211216).sum := by decide
  have hdescent : baseEnd_1211216 < baseStart_1211216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211223 : List Nat := [1, 1, 3, 2, 4, 1, 1, 5, 1, 4]
def baseStart_1211223 : Nat := 118140960795 + 1211223 * 2 ^ 59
def prefixEnd_1211223 : Nat := 4983230072969 + 3 ^ 40 * 1211223 * 2
def baseEnd_1211223 : Nat := 207313192926939939380731

theorem tailTrace_1211223 : CollatzResearch.WordTrace tailWord_1211223 prefixEnd_1211223 207313192926939939380731 := by
  unfold tailWord_1211223
  simp only [CollatzResearch.WordTrace]
  refine ⟨44176932090953406264510323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29451288060635604176340215 44176932090953406264510323)
  ·
    refine ⟨66265398136430109396765485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44176932090953406264510323 66265398136430109396765485)
    ·
      refine ⟨24849524301161291023787057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66265398136430109396765485 24849524301161291023787057)
      ·
        refine ⟨18637143225870968267840293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24849524301161291023787057 18637143225870968267840293)
        ·
          refine ⟨3494464354850806550220055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18637143225870968267840293 3494464354850806550220055)
          ·
            refine ⟨5241696532276209825330083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3494464354850806550220055 5241696532276209825330083)
            ·
              refine ⟨7862544798414314737995125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5241696532276209825330083 7862544798414314737995125)
              ·
                refine ⟨737113574851342006687043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7862544798414314737995125 737113574851342006687043)
                ·
                  refine ⟨1105670362277013010030565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737113574851342006687043 1105670362277013010030565)
                  ·
                    refine ⟨207313192926939939380731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1105670362277013010030565 207313192926939939380731)
                    ·
                      rfl

theorem cell23_1211223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_1211223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211223 prefixEnd_1211223 := by exact prefixLift 1211223
  have htrace : WordTrace (prefixWord ++ tailWord_1211223) baseStart_1211223 baseEnd_1211223 := by
    simpa [prefixWord, tailWord_1211223, baseEnd_1211223] using wordTrace_append hprefix tailTrace_1211223
  have hstable : (prefixWord ++ tailWord_1211223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211223).length < 2 ^ (prefixWord ++ tailWord_1211223).sum := by decide
  have hdescent : baseEnd_1211223 < baseStart_1211223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211236 : List Nat := [2, 3, 1, 1, 4, 1, 3, 2, 6]
def baseStart_1211236 : Nat := 118140960795 + 1211236 * 2 ^ 59
def prefixEnd_1211236 : Nat := 4983230072969 + 3 ^ 40 * 1211236 * 2
def baseEnd_1211236 : Nat := 69105139336592029697737

theorem tailTrace_1211236 : CollatzResearch.WordTrace tailWord_1211236 prefixEnd_1211236 69105139336592029697737 := by
  unfold tailWord_1211236
  simp only [CollatzResearch.WordTrace]
  refine ⟨22088703119953154742366781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29451604159937539656489041 22088703119953154742366781)
  ·
    refine ⟨8283263669982433028387543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22088703119953154742366781 8283263669982433028387543)
    ·
      refine ⟨12424895504973649542581315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8283263669982433028387543 12424895504973649542581315)
      ·
        refine ⟨18637343257460474313871973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12424895504973649542581315 18637343257460474313871973)
        ·
          refine ⟨3494501860773838933850995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18637343257460474313871973 3494501860773838933850995)
          ·
            refine ⟨5241752791160758400776493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3494501860773838933850995 5241752791160758400776493)
            ·
              refine ⟨1965657296685284400291185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5241752791160758400776493 1965657296685284400291185)
              ·
                refine ⟨1474242972513963300218389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1965657296685284400291185 1474242972513963300218389)
                ·
                  refine ⟨69105139336592029697737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1474242972513963300218389 69105139336592029697737)
                  ·
                    rfl

theorem cell23_1211236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_1211236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211236 prefixEnd_1211236 := by exact prefixLift 1211236
  have htrace : WordTrace (prefixWord ++ tailWord_1211236) baseStart_1211236 baseEnd_1211236 := by
    simpa [prefixWord, tailWord_1211236, baseEnd_1211236] using wordTrace_append hprefix tailTrace_1211236
  have hstable : (prefixWord ++ tailWord_1211236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211236).length < 2 ^ (prefixWord ++ tailWord_1211236).sum := by decide
  have hdescent : baseEnd_1211236 < baseStart_1211236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211239 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_1211239 : Nat := 118140960795 + 1211239 * 2 ^ 59
def prefixEnd_1211239 : Nat := 4983230072969 + 3 ^ 40 * 1211239 * 2
def baseEnd_1211239 : Nat := 621947794471291755542119

theorem tailTrace_1211239 : CollatzResearch.WordTrace tailWord_1211239 prefixEnd_1211239 621947794471291755542119 := by
  unfold tailWord_1211239
  simp only [CollatzResearch.WordTrace]
  refine ⟨44177515658895440997092771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29451677105930293998061847 44177515658895440997092771)
  ·
    refine ⟨66266273488343161495639157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44177515658895440997092771 66266273488343161495639157)
    ·
      refine ⟨6212463139532171390216171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66266273488343161495639157 6212463139532171390216171)
      ·
        refine ⟨9318694709298257085324257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6212463139532171390216171 9318694709298257085324257)
        ·
          refine ⟨6989021031973692813993193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9318694709298257085324257 6989021031973692813993193)
          ·
            refine ⟨5241765773980269610494895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6989021031973692813993193 5241765773980269610494895)
            ·
              refine ⟨7862648660970404415742343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5241765773980269610494895 7862648660970404415742343)
              ·
                refine ⟨11793972991455606623613515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7862648660970404415742343 11793972991455606623613515)
                ·
                  refine ⟨17690959487183409935420273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11793972991455606623613515 17690959487183409935420273)
                  ·
                    refine ⟨13268219615387557451565205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17690959487183409935420273 13268219615387557451565205)
                    ·
                      refine ⟨621947794471291755542119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13268219615387557451565205 621947794471291755542119)
                      ·
                        rfl

theorem cell23_1211239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_1211239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211239 prefixEnd_1211239 := by exact prefixLift 1211239
  have htrace : WordTrace (prefixWord ++ tailWord_1211239) baseStart_1211239 baseEnd_1211239 := by
    simpa [prefixWord, tailWord_1211239, baseEnd_1211239] using wordTrace_append hprefix tailTrace_1211239
  have hstable : (prefixWord ++ tailWord_1211239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211239).length < 2 ^ (prefixWord ++ tailWord_1211239).sum := by decide
  have hdescent : baseEnd_1211239 < baseStart_1211239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211253 : List Nat := [1, 3, 4, 1, 1, 3, 3, 1, 6]
def baseStart_1211253 : Nat := 118140960795 + 1211253 * 2 ^ 59
def prefixEnd_1211253 : Nat := 4983230072969 + 3 ^ 40 * 1211253 * 2
def baseEnd_1211253 : Nat := 69106109244494966751895

theorem tailTrace_1211253 : CollatzResearch.WordTrace tailWord_1211253 prefixEnd_1211253 69106109244494966751895 := by
  unfold tailWord_1211253
  simp only [CollatzResearch.WordTrace]
  refine ⟨44178026280844721388102413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29452017520563147592068275 44178026280844721388102413)
  ·
    refine ⟨16566759855316770520538405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44178026280844721388102413 16566759855316770520538405)
    ·
      refine ⟨3106267472871894472600951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16566759855316770520538405 3106267472871894472600951)
      ·
        refine ⟨4659401209307841708901427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3106267472871894472600951 4659401209307841708901427)
        ·
          refine ⟨6989101813961762563352141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4659401209307841708901427 6989101813961762563352141)
          ·
            refine ⟨2620913180235660961257053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6989101813961762563352141 2620913180235660961257053)
            ·
              refine ⟨982842442588372860471395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2620913180235660961257053 982842442588372860471395)
              ·
                refine ⟨1474263663882559290707093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982842442588372860471395 1474263663882559290707093)
                ·
                  refine ⟨69106109244494966751895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1474263663882559290707093 69106109244494966751895)
                  ·
                    rfl

theorem cell23_1211253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 6].length) (baseStart_1211253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211253 prefixEnd_1211253 := by exact prefixLift 1211253
  have htrace : WordTrace (prefixWord ++ tailWord_1211253) baseStart_1211253 baseEnd_1211253 := by
    simpa [prefixWord, tailWord_1211253, baseEnd_1211253] using wordTrace_append hprefix tailTrace_1211253
  have hstable : (prefixWord ++ tailWord_1211253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211253).length < 2 ^ (prefixWord ++ tailWord_1211253).sum := by decide
  have hdescent : baseEnd_1211253 < baseStart_1211253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211256 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 6, 3, 2]
def baseStart_1211256 : Nat := 118140960795 + 1211256 * 2 ^ 59
def prefixEnd_1211256 : Nat := 4983230072969 + 3 ^ 40 * 1211256 * 2
def baseEnd_1211256 : Nat := 621956523642418189029541

theorem tailTrace_1211256 : CollatzResearch.WordTrace tailWord_1211256 prefixEnd_1211256 621956523642418189029541 := by
  unfold tailWord_1211256
  simp only [CollatzResearch.WordTrace]
  refine ⟨22089067849916926450230811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29452090466555901933641081 22089067849916926450230811)
  ·
    refine ⟨33133601774875389675346217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22089067849916926450230811 33133601774875389675346217)
    ·
      refine ⟨24850201331156542256509663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33133601774875389675346217 24850201331156542256509663)
      ·
        refine ⟨37275301996734813384764495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24850201331156542256509663 37275301996734813384764495)
        ·
          refine ⟨55912952995102220077146743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37275301996734813384764495 55912952995102220077146743)
          ·
            refine ⟨83869429492653330115720115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55912952995102220077146743 83869429492653330115720115)
            ·
              refine ⟨125804144238979995173580173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83869429492653330115720115 125804144238979995173580173)
              ·
                refine ⟨47176554089617498190092565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125804144238979995173580173 47176554089617498190092565)
                ·
                  refine ⟨2211400972950820227660589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47176554089617498190092565 2211400972950820227660589)
                  ·
                    refine ⟨829275364856557585372721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2211400972950820227660589 829275364856557585372721)
                    ·
                      refine ⟨621956523642418189029541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 829275364856557585372721 621956523642418189029541)
                      ·
                        rfl

theorem cell23_1211256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 6, 3, 2].length) (baseStart_1211256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211256 prefixEnd_1211256 := by exact prefixLift 1211256
  have htrace : WordTrace (prefixWord ++ tailWord_1211256) baseStart_1211256 baseEnd_1211256 := by
    simpa [prefixWord, tailWord_1211256, baseEnd_1211256] using wordTrace_append hprefix tailTrace_1211256
  have hstable : (prefixWord ++ tailWord_1211256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211256).length < 2 ^ (prefixWord ++ tailWord_1211256).sum := by decide
  have hdescent : baseEnd_1211256 < baseStart_1211256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211290 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2]
def baseStart_1211290 : Nat := 118140960795 + 1211290 * 2 ^ 59
def prefixEnd_1211290 : Nat := 4983230072969 + 3 ^ 40 * 1211290 * 2
def baseEnd_1211290 : Nat := 621973981984671056004385

theorem tailTrace_1211290 : CollatzResearch.WordTrace tailWord_1211290 prefixEnd_1211290 621973981984671056004385 := by
  unfold tailWord_1211290
  simp only [CollatzResearch.WordTrace]
  refine ⟨11044843945427669176799831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29452917187807117804799549 11044843945427669176799831)
  ·
    refine ⟨16567265918141503765199747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11044843945427669176799831 16567265918141503765199747)
    ·
      refine ⟨24850898877212255647799621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16567265918141503765199747 24850898877212255647799621)
      ·
        refine ⟨4659543539477297933962429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24850898877212255647799621 4659543539477297933962429)
        ·
          refine ⟨1747328827303986725235911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4659543539477297933962429 1747328827303986725235911)
          ·
            refine ⟨2620993240955980087853867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1747328827303986725235911 2620993240955980087853867)
            ·
              refine ⟨3931489861433970131780801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620993240955980087853867 3931489861433970131780801)
              ·
                refine ⟨2948617396075477598835601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3931489861433970131780801 2948617396075477598835601)
                ·
                  refine ⟨2211463047056608199126701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2948617396075477598835601 2211463047056608199126701)
                  ·
                    refine ⟨829298642646228074672513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2211463047056608199126701 829298642646228074672513)
                    ·
                      refine ⟨621973981984671056004385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 829298642646228074672513 621973981984671056004385)
                      ·
                        rfl

theorem cell23_1211290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_1211290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211290 prefixEnd_1211290 := by exact prefixLift 1211290
  have htrace : WordTrace (prefixWord ++ tailWord_1211290) baseStart_1211290 baseEnd_1211290 := by
    simpa [prefixWord, tailWord_1211290, baseEnd_1211290] using wordTrace_append hprefix tailTrace_1211290
  have hstable : (prefixWord ++ tailWord_1211290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211290).length < 2 ^ (prefixWord ++ tailWord_1211290).sum := by decide
  have hdescent : baseEnd_1211290 < baseStart_1211290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211296 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 4, 4]
def baseStart_1211296 : Nat := 118140960795 + 1211296 * 2 ^ 59
def prefixEnd_1211296 : Nat := 4983230072969 + 3 ^ 40 * 1211296 * 2
def baseEnd_1211296 : Nat := 207325687622866010843119

theorem tailTrace_1211296 : CollatzResearch.WordTrace tailWord_1211296 prefixEnd_1211296 207325687622866010843119 := by
  unfold tailWord_1211296
  simp only [CollatzResearch.WordTrace]
  refine ⟨22089797309844469865958871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29453063079792626487945161 22089797309844469865958871)
  ·
    refine ⟨33134695964766704798938307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22089797309844469865958871 33134695964766704798938307)
    ·
      refine ⟨49702043947150057198407461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33134695964766704798938307 49702043947150057198407461)
      ·
        refine ⟨9319133240090635724701399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49702043947150057198407461 9319133240090635724701399)
        ·
          refine ⟨13978699860135953587052099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9319133240090635724701399 13978699860135953587052099)
          ·
            refine ⟨20968049790203930380578149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13978699860135953587052099 20968049790203930380578149)
            ·
              refine ⟨3931509335663236946358403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20968049790203930380578149 3931509335663236946358403)
              ·
                refine ⟨5897264003494855419537605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3931509335663236946358403 5897264003494855419537605)
                ·
                  refine ⟨1105737000655285391163301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5897264003494855419537605 1105737000655285391163301)
                  ·
                    refine ⟨207325687622866010843119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1105737000655285391163301 207325687622866010843119)
                    ·
                      rfl

theorem cell23_1211296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 4, 4].length) (baseStart_1211296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211296 prefixEnd_1211296 := by exact prefixLift 1211296
  have htrace : WordTrace (prefixWord ++ tailWord_1211296) baseStart_1211296 baseEnd_1211296 := by
    simpa [prefixWord, tailWord_1211296, baseEnd_1211296] using wordTrace_append hprefix tailTrace_1211296
  have hstable : (prefixWord ++ tailWord_1211296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211296).length < 2 ^ (prefixWord ++ tailWord_1211296).sum := by decide
  have hdescent : baseEnd_1211296 < baseStart_1211296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211299 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 6]
def baseStart_1211299 : Nat := 118140960795 + 1211299 * 2 ^ 59
def prefixEnd_1211299 : Nat := 4983230072969 + 3 ^ 40 * 1211299 * 2
def baseEnd_1211299 : Nat := 621978603310561520791843

theorem tailTrace_1211299 : CollatzResearch.WordTrace tailWord_1211299 prefixEnd_1211299 621978603310561520791843 := by
  unfold tailWord_1211299
  simp only [CollatzResearch.WordTrace]
  refine ⟨44179704038678071244276951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29453136025785380829517967 44179704038678071244276951)
  ·
    refine ⟨66269556058017106866415427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44179704038678071244276951 66269556058017106866415427)
    ·
      refine ⟨99404334087025660299623141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66269556058017106866415427 99404334087025660299623141)
      ·
        refine ⟨18638312641317311306179339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99404334087025660299623141 18638312641317311306179339)
        ·
          refine ⟨27957468961975966959269009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18638312641317311306179339 27957468961975966959269009)
          ·
            refine ⟨20968101721481975219451757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27957468961975966959269009 20968101721481975219451757)
            ·
              refine ⟨7863038145555740707294409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20968101721481975219451757 7863038145555740707294409)
              ·
                refine ⟨5897278609166805530470807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7863038145555740707294409 5897278609166805530470807)
                ·
                  refine ⟨8845917913750208295706211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5897278609166805530470807 8845917913750208295706211)
                  ·
                    refine ⟨13268876870625312443559317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8845917913750208295706211 13268876870625312443559317)
                    ·
                      refine ⟨621978603310561520791843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13268876870625312443559317 621978603310561520791843)
                      ·
                        rfl

theorem cell23_1211299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_1211299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211299 prefixEnd_1211299 := by exact prefixLift 1211299
  have htrace : WordTrace (prefixWord ++ tailWord_1211299) baseStart_1211299 baseEnd_1211299 := by
    simpa [prefixWord, tailWord_1211299, baseEnd_1211299] using wordTrace_append hprefix tailTrace_1211299
  have hstable : (prefixWord ++ tailWord_1211299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211299).length < 2 ^ (prefixWord ++ tailWord_1211299).sum := by decide
  have hdescent : baseEnd_1211299 < baseStart_1211299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211340 : List Nat := [2, 2, 1, 4, 1, 1, 5, 1, 1, 2, 3]
def baseStart_1211340 : Nat := 118140960795 + 1211340 * 2 ^ 59
def prefixEnd_1211340 : Nat := 4983230072969 + 3 ^ 40 * 1211340 * 2
def baseEnd_1211340 : Nat := 621999656017395860379155

theorem tailTrace_1211340 : CollatzResearch.WordTrace tailWord_1211340 prefixEnd_1211340 621999656017395860379155 := by
  unfold tailWord_1211340
  simp only [CollatzResearch.WordTrace]
  refine ⟨22090599715764767623259737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29454132954353023497679649 22090599715764767623259737)
  ·
    refine ⟨16567949786823575717444803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22090599715764767623259737 16567949786823575717444803)
    ·
      refine ⟨24851924680235363576167205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16567949786823575717444803 24851924680235363576167205)
      ·
        refine ⟨4659735877544130670531351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24851924680235363576167205 4659735877544130670531351)
        ·
          refine ⟨6989603816316196005797027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4659735877544130670531351 6989603816316196005797027)
          ·
            refine ⟨10484405724474294008695541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6989603816316196005797027 10484405724474294008695541)
            ·
              refine ⟨982913036669465063315207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10484405724474294008695541 982913036669465063315207)
              ·
                refine ⟨1474369555004197594972811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982913036669465063315207 1474369555004197594972811)
                ·
                  refine ⟨2211554332506296392459217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474369555004197594972811 2211554332506296392459217)
                  ·
                    refine ⟨1658665749379722294344413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2211554332506296392459217 1658665749379722294344413)
                    ·
                      refine ⟨621999656017395860379155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1658665749379722294344413 621999656017395860379155)
                      ·
                        rfl

theorem cell23_1211340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_1211340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211340 prefixEnd_1211340 := by exact prefixLift 1211340
  have htrace : WordTrace (prefixWord ++ tailWord_1211340) baseStart_1211340 baseEnd_1211340 := by
    simpa [prefixWord, tailWord_1211340, baseEnd_1211340] using wordTrace_append hprefix tailTrace_1211340
  have hstable : (prefixWord ++ tailWord_1211340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211340).length < 2 ^ (prefixWord ++ tailWord_1211340).sum := by decide
  have hdescent : baseEnd_1211340 < baseStart_1211340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211354 : List Nat := [3, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2]
def baseStart_1211354 : Nat := 118140960795 + 1211354 * 2 ^ 59
def prefixEnd_1211354 : Nat := 4983230072969 + 3 ^ 40 * 1211354 * 2
def baseEnd_1211354 : Nat := 622006844746558805604091

theorem tailTrace_1211354 : CollatzResearch.WordTrace tailWord_1211354 prefixEnd_1211354 622006844746558805604091 := by
  unfold tailWord_1211354
  simp only [CollatzResearch.WordTrace]
  refine ⟨11045427513369703909382279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29454473368985877091686077 11045427513369703909382279)
  ·
    refine ⟨16568141270054555864073419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11045427513369703909382279 16568141270054555864073419)
    ·
      refine ⟨24852211905081833796110129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16568141270054555864073419 24852211905081833796110129)
      ·
        refine ⟨18639158928811375347082597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24852211905081833796110129 18639158928811375347082597)
        ·
          refine ⟨3494842299152132877577987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18639158928811375347082597 3494842299152132877577987)
          ·
            refine ⟨5242263448728199316366981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3494842299152132877577987 5242263448728199316366981)
            ·
              refine ⟨982924396636537371818809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5242263448728199316366981 982924396636537371818809)
              ·
                refine ⟨737193297477403028864107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982924396636537371818809 737193297477403028864107)
                ·
                  refine ⟨1105789946216104543296161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737193297477403028864107 1105789946216104543296161)
                  ·
                    refine ⟨829342459662078407472121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1105789946216104543296161 829342459662078407472121)
                    ·
                      refine ⟨622006844746558805604091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 829342459662078407472121 622006844746558805604091)
                      ·
                        rfl

theorem cell23_1211354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_1211354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211354 prefixEnd_1211354 := by exact prefixLift 1211354
  have htrace : WordTrace (prefixWord ++ tailWord_1211354) baseStart_1211354 baseEnd_1211354 := by
    simpa [prefixWord, tailWord_1211354, baseEnd_1211354] using wordTrace_append hprefix tailTrace_1211354
  have hstable : (prefixWord ++ tailWord_1211354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211354).length < 2 ^ (prefixWord ++ tailWord_1211354).sum := by decide
  have hdescent : baseEnd_1211354 < baseStart_1211354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211363 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 5, 3, 2]
def baseStart_1211363 : Nat := 118140960795 + 1211363 * 2 ^ 59
def prefixEnd_1211363 : Nat := 4983230072969 + 3 ^ 40 * 1211363 * 2
def baseEnd_1211363 : Nat := 622011466072449270391549

theorem tailTrace_1211363 : CollatzResearch.WordTrace tailWord_1211363 prefixEnd_1211363 622011466072449270391549 := by
  unfold tailWord_1211363
  simp only [CollatzResearch.WordTrace]
  refine ⟨44182038310446210174606743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29454692206964140116404495 44182038310446210174606743)
  ·
    refine ⟨66273057465669315261910115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44182038310446210174606743 66273057465669315261910115)
    ·
      refine ⟨99409586198503972892865173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66273057465669315261910115 99409586198503972892865173)
      ·
        refine ⟨4659824353054873729353055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99409586198503972892865173 4659824353054873729353055)
        ·
          refine ⟨6989736529582310594029583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4659824353054873729353055 6989736529582310594029583)
          ·
            refine ⟨10484604794373465891044375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6989736529582310594029583 10484604794373465891044375)
            ·
              refine ⟨15726907191560198836566563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10484604794373465891044375 15726907191560198836566563)
              ·
                refine ⟨23590360787340298254849845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15726907191560198836566563 23590360787340298254849845)
                ·
                  refine ⟨2211596323813152961392173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23590360787340298254849845 2211596323813152961392173)
                  ·
                    refine ⟨829348621429932360522065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2211596323813152961392173 829348621429932360522065)
                    ·
                      refine ⟨622011466072449270391549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 829348621429932360522065 622011466072449270391549)
                      ·
                        rfl

theorem cell23_1211363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_1211363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211363 prefixEnd_1211363 := by exact prefixLift 1211363
  have htrace : WordTrace (prefixWord ++ tailWord_1211363) baseStart_1211363 baseEnd_1211363 := by
    simpa [prefixWord, tailWord_1211363, baseEnd_1211363] using wordTrace_append hprefix tailTrace_1211363
  have hstable : (prefixWord ++ tailWord_1211363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211363).length < 2 ^ (prefixWord ++ tailWord_1211363).sum := by decide
  have hdescent : baseEnd_1211363 < baseStart_1211363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211370 : List Nat := [3, 1, 3, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_1211370 : Nat := 118140960795 + 1211370 * 2 ^ 59
def prefixEnd_1211370 : Nat := 4983230072969 + 3 ^ 40 * 1211370 * 2
def baseEnd_1211370 : Nat := 622015060437030743004017

theorem tailTrace_1211370 : CollatzResearch.WordTrace tailWord_1211370 prefixEnd_1211370 622015060437030743004017 := by
  unfold tailWord_1211370
  simp only [CollatzResearch.WordTrace]
  refine ⟨11045573405355212592527891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29454862414280566913407709 11045573405355212592527891)
  ·
    refine ⟨16568360108032818888791837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11045573405355212592527891 16568360108032818888791837)
    ·
      refine ⟨6213135040512307083296939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16568360108032818888791837 6213135040512307083296939)
      ·
        refine ⟨9319702560768460624945409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6213135040512307083296939 9319702560768460624945409)
        ·
          refine ⟨6989776920576345468709057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9319702560768460624945409 6989776920576345468709057)
          ·
            refine ⟨5242332690432259101531793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6989776920576345468709057 5242332690432259101531793)
            ·
              refine ⟨3931749517824194326148845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5242332690432259101531793 3931749517824194326148845)
              ·
                refine ⟨1474406069184072872305817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3931749517824194326148845 1474406069184072872305817)
                ·
                  refine ⟨1105804551888054654229363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1474406069184072872305817 1105804551888054654229363)
                  ·
                    refine ⟨1658706827832081981344045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1105804551888054654229363 1658706827832081981344045)
                    ·
                      refine ⟨622015060437030743004017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1658706827832081981344045 622015060437030743004017)
                      ·
                        rfl

theorem cell23_1211370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_1211370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211370 prefixEnd_1211370 := by exact prefixLift 1211370
  have htrace : WordTrace (prefixWord ++ tailWord_1211370) baseStart_1211370 baseEnd_1211370 := by
    simpa [prefixWord, tailWord_1211370, baseEnd_1211370] using wordTrace_append hprefix tailTrace_1211370
  have hstable : (prefixWord ++ tailWord_1211370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211370).length < 2 ^ (prefixWord ++ tailWord_1211370).sum := by decide
  have hdescent : baseEnd_1211370 < baseStart_1211370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211416 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 7]
def baseStart_1211416 : Nat := 118140960795 + 1211416 * 2 ^ 59
def prefixEnd_1211416 : Nat := 4983230072969 + 3 ^ 40 * 1211416 * 2
def baseEnd_1211416 : Nat := 69115408949681951447645

theorem tailTrace_1211416 : CollatzResearch.WordTrace tailWord_1211416 prefixEnd_1211416 69115408949681951447645 := by
  unfold tailWord_1211416
  simp only [CollatzResearch.WordTrace]
  refine ⟨22091985689627100113143051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29455980919502800150857401 22091985689627100113143051)
  ·
    refine ⟨33137978534440650169714577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22091985689627100113143051 33137978534440650169714577)
    ·
      refine ⟨24853483900830487627285933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33137978534440650169714577 24853483900830487627285933)
      ·
        refine ⟨9320056462811432860232225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24853483900830487627285933 9320056462811432860232225)
        ·
          refine ⟨6990042347108574645174169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9320056462811432860232225 6990042347108574645174169)
          ·
            refine ⟨5242531760331430983880627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6990042347108574645174169 5242531760331430983880627)
            ·
              refine ⟨7863797640497146475820941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5242531760331430983880627 7863797640497146475820941)
              ·
                refine ⟨2948924115186429928432853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7863797640497146475820941 2948924115186429928432853)
                ·
                  refine ⟨69115408949681951447645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2948924115186429928432853 69115408949681951447645)
                  ·
                    rfl

theorem cell23_1211416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 7].length) (baseStart_1211416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211416 prefixEnd_1211416 := by exact prefixLift 1211416
  have htrace : WordTrace (prefixWord ++ tailWord_1211416) baseStart_1211416 baseEnd_1211416 := by
    simpa [prefixWord, tailWord_1211416, baseEnd_1211416] using wordTrace_append hprefix tailTrace_1211416
  have hstable : (prefixWord ++ tailWord_1211416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211416).length < 2 ^ (prefixWord ++ tailWord_1211416).sum := by decide
  have hdescent : baseEnd_1211416 < baseStart_1211416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211456 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 5]
def baseStart_1211456 : Nat := 118140960795 + 1211456 * 2 ^ 59
def prefixEnd_1211456 : Nat := 4983230072969 + 3 ^ 40 * 1211456 * 2
def baseEnd_1211456 : Nat := 622059219773317406528621

theorem tailTrace_1211456 : CollatzResearch.WordTrace tailWord_1211456 prefixEnd_1211456 622059219773317406528621 := by
  unfold tailWord_1211456
  simp only [CollatzResearch.WordTrace]
  refine ⟨22092715149554643528871111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29456953532739524705161481 22092715149554643528871111)
  ·
    refine ⟨33139072724331965293306667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22092715149554643528871111 33139072724331965293306667)
    ·
      refine ⟨49708609086497947939960001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33139072724331965293306667 49708609086497947939960001)
      ·
        refine ⟨37281456814873460954970001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49708609086497947939960001 37281456814873460954970001)
        ·
          refine ⟨27961092611155095716227501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37281456814873460954970001 27961092611155095716227501)
          ·
            refine ⟨10485409729183160893585313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27961092611155095716227501 10485409729183160893585313)
            ·
              refine ⟨7864057296887370670188985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10485409729183160893585313 7864057296887370670188985)
              ·
                refine ⟨5898042972665528002641739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7864057296887370670188985 5898042972665528002641739)
                ·
                  refine ⟨8847064458998292003962609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5898042972665528002641739 8847064458998292003962609)
                  ·
                    refine ⟨6635298344248719002971957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8847064458998292003962609 6635298344248719002971957)
                    ·
                      refine ⟨622059219773317406528621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6635298344248719002971957 622059219773317406528621)
                      ·
                        rfl

theorem cell23_1211456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_1211456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211456 prefixEnd_1211456 := by exact prefixLift 1211456
  have htrace : WordTrace (prefixWord ++ tailWord_1211456) baseStart_1211456 baseEnd_1211456 := by
    simpa [prefixWord, tailWord_1211456, baseEnd_1211456] using wordTrace_append hprefix tailTrace_1211456
  have hstable : (prefixWord ++ tailWord_1211456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211456).length < 2 ^ (prefixWord ++ tailWord_1211456).sum := by decide
  have hdescent : baseEnd_1211456 < baseStart_1211456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211463 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 2, 5]
def baseStart_1211463 : Nat := 118140960795 + 1211463 * 2 ^ 59
def prefixEnd_1211463 : Nat := 4983230072969 + 3 ^ 40 * 1211463 * 2
def baseEnd_1211463 : Nat := 207354271379299626380363

theorem tailTrace_1211463 : CollatzResearch.WordTrace tailWord_1211463 prefixEnd_1211463 207354271379299626380363 := by
  unfold tailWord_1211463
  simp only [CollatzResearch.WordTrace]
  refine ⟨44185685610083927253247043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29457123740055951502164695 44185685610083927253247043)
  ·
    refine ⟨66278528415125890879870565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44185685610083927253247043 66278528415125890879870565)
    ·
      refine ⟨12427224077836104539975731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66278528415125890879870565 12427224077836104539975731)
      ·
        refine ⟨18640836116754156809963597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12427224077836104539975731 18640836116754156809963597)
        ·
          refine ⟨6990313543782808803736349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18640836116754156809963597 6990313543782808803736349)
          ·
            refine ⟨2621367578918553301401131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6990313543782808803736349 2621367578918553301401131)
            ·
              refine ⟨3932051368377829952101697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2621367578918553301401131 3932051368377829952101697)
              ·
                refine ⟨2949038526283372464076273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3932051368377829952101697 2949038526283372464076273)
                ·
                  refine ⟨2211778894712529348057205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2949038526283372464076273 2211778894712529348057205)
                  ·
                    refine ⟨207354271379299626380363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2211778894712529348057205 207354271379299626380363)
                    ·
                      rfl

theorem cell23_1211463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_1211463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211463 prefixEnd_1211463 := by exact prefixLift 1211463
  have htrace : WordTrace (prefixWord ++ tailWord_1211463) baseStart_1211463 baseEnd_1211463 := by
    simpa [prefixWord, tailWord_1211463, baseEnd_1211463] using wordTrace_append hprefix tailTrace_1211463
  have hstable : (prefixWord ++ tailWord_1211463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211463).length < 2 ^ (prefixWord ++ tailWord_1211463).sum := by decide
  have hdescent : baseEnd_1211463 < baseStart_1211463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211493 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 5, 4]
def baseStart_1211493 : Nat := 118140960795 + 1211493 * 2 ^ 59
def prefixEnd_1211493 : Nat := 4983230072969 + 3 ^ 40 * 1211493 * 2
def baseEnd_1211493 : Nat := 207359406185844587255317

theorem tailTrace_1211493 : CollatzResearch.WordTrace tailWord_1211493 prefixEnd_1211493 207359406185844587255317 := by
  unfold tailWord_1211493
  simp only [CollatzResearch.WordTrace]
  refine ⟨44186779799975242376839133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29457853199983494917892755 44186779799975242376839133)
  ·
    refine ⟨16570042424990715891314675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44186779799975242376839133 16570042424990715891314675)
    ·
      refine ⟨24855063637486073836972013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16570042424990715891314675 24855063637486073836972013)
      ·
        refine ⟨9320648864057277688864505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24855063637486073836972013 9320648864057277688864505)
        ·
          refine ⟨6990486648042958266648379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9320648864057277688864505 6990486648042958266648379)
          ·
            refine ⟨10485729972064437399972569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6990486648042958266648379 10485729972064437399972569)
            ·
              refine ⟨7864297479048328049979427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10485729972064437399972569 7864297479048328049979427)
              ·
                refine ⟨11796446218572492074969141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7864297479048328049979427 11796446218572492074969141)
                ·
                  refine ⟨1105916832991171132028357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11796446218572492074969141 1105916832991171132028357)
                  ·
                    refine ⟨207359406185844587255317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1105916832991171132028357 207359406185844587255317)
                    ·
                      rfl

theorem cell23_1211493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_1211493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211493 prefixEnd_1211493 := by exact prefixLift 1211493
  have htrace : WordTrace (prefixWord ++ tailWord_1211493) baseStart_1211493 baseEnd_1211493 := by
    simpa [prefixWord, tailWord_1211493, baseEnd_1211493] using wordTrace_append hprefix tailTrace_1211493
  have hstable : (prefixWord ++ tailWord_1211493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211493).length < 2 ^ (prefixWord ++ tailWord_1211493).sum := by decide
  have hdescent : baseEnd_1211493 < baseStart_1211493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211518 : List Nat := [4, 2, 4, 1, 1, 2, 2, 2, 5]
def baseStart_1211518 : Nat := 118140960795 + 1211518 * 2 ^ 59
def prefixEnd_1211518 : Nat := 4983230072969 + 3 ^ 40 * 1211518 * 2
def baseEnd_1211518 : Nat := 69121228397099573772593

theorem tailTrace_1211518 : CollatzResearch.WordTrace tailWord_1211518 prefixEnd_1211518 69121228397099573772593 := by
  unfold tailWord_1211518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5523461453110583955812401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29458461083256447764332805 5523461453110583955812401)
  ·
    refine ⟨4142596089832937966859301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5523461453110583955812401 4142596089832937966859301)
    ·
      refine ⟨776736766843675868786119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4142596089832937966859301 776736766843675868786119)
      ·
        refine ⟨1165105150265513803179179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776736766843675868786119 1165105150265513803179179)
        ·
          refine ⟨1747657725398270704768769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1165105150265513803179179 1747657725398270704768769)
          ·
            refine ⟨1310743294048703028576577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1747657725398270704768769 1310743294048703028576577)
            ·
              refine ⟨983057470536527271432433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1310743294048703028576577 983057470536527271432433)
              ·
                refine ⟨737293102902395453574325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983057470536527271432433 737293102902395453574325)
                ·
                  refine ⟨69121228397099573772593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 737293102902395453574325 69121228397099573772593)
                  ·
                    rfl

theorem cell23_1211518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_1211518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211518 prefixEnd_1211518 := by exact prefixLift 1211518
  have htrace : WordTrace (prefixWord ++ tailWord_1211518) baseStart_1211518 baseEnd_1211518 := by
    simpa [prefixWord, tailWord_1211518, baseEnd_1211518] using wordTrace_append hprefix tailTrace_1211518
  have hstable : (prefixWord ++ tailWord_1211518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211518).length < 2 ^ (prefixWord ++ tailWord_1211518).sum := by decide
  have hdescent : baseEnd_1211518 < baseStart_1211518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211523 : List Nat := [1, 1, 1, 3, 3, 2, 4, 2, 6]
def baseStart_1211523 : Nat := 118140960795 + 1211523 * 2 ^ 59
def prefixEnd_1211523 : Nat := 4983230072969 + 3 ^ 40 * 1211523 * 2
def baseEnd_1211523 : Nat := 69121513664129849376757

theorem tailTrace_1211523 : CollatzResearch.WordTrace tailWord_1211523 prefixEnd_1211523 69121513664129849376757 := by
  unfold tailWord_1211523
  simp only [CollatzResearch.WordTrace]
  refine ⟨44187873989866557500431223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29458582659911038333620815 44187873989866557500431223)
  ·
    refine ⟨66281810984799836250646835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44187873989866557500431223 66281810984799836250646835)
    ·
      refine ⟨99422716477199754375970253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66281810984799836250646835 99422716477199754375970253)
      ·
        refine ⟨37283518678949907890988845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99422716477199754375970253 37283518678949907890988845)
        ·
          refine ⟨13981319504606215459120817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37283518678949907890988845 13981319504606215459120817)
          ·
            refine ⟨10485989628454661594340613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13981319504606215459120817 10485989628454661594340613)
            ·
              refine ⟨1966123055335249048938865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10485989628454661594340613 1966123055335249048938865)
              ·
                refine ⟨1474592291501436786704149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1966123055335249048938865 1474592291501436786704149)
                ·
                  refine ⟨69121513664129849376757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1474592291501436786704149 69121513664129849376757)
                  ·
                    rfl

theorem cell23_1211523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 6].length) (baseStart_1211523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211523 prefixEnd_1211523 := by exact prefixLift 1211523
  have htrace : WordTrace (prefixWord ++ tailWord_1211523) baseStart_1211523 baseEnd_1211523 := by
    simpa [prefixWord, tailWord_1211523, baseEnd_1211523] using wordTrace_append hprefix tailTrace_1211523
  have hstable : (prefixWord ++ tailWord_1211523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211523).length < 2 ^ (prefixWord ++ tailWord_1211523).sum := by decide
  have hdescent : baseEnd_1211523 < baseStart_1211523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211553 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 3, 5]
def baseStart_1211553 : Nat := 118140960795 + 1211553 * 2 ^ 59
def prefixEnd_1211553 : Nat := 4983230072969 + 3 ^ 40 * 1211553 * 2
def baseEnd_1211553 : Nat := 207369675798934509005225

theorem tailTrace_1211553 : CollatzResearch.WordTrace tailWord_1211553 prefixEnd_1211553 207369675798934509005225 := by
  unfold tailWord_1211553
  simp only [CollatzResearch.WordTrace]
  refine ⟨44188968179757872624023313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29459312119838581749348875 44188968179757872624023313)
  ·
    refine ⟨33141726134818404468017485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44188968179757872624023313 33141726134818404468017485)
    ·
      refine ⟨12428147300556901675506557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33141726134818404468017485 12428147300556901675506557)
      ·
        refine ⟨4660555237708838128314959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12428147300556901675506557 4660555237708838128314959)
        ·
          refine ⟨6990832856563257192472439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4660555237708838128314959 6990832856563257192472439)
          ·
            refine ⟨10486249284844885788708659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6990832856563257192472439 10486249284844885788708659)
            ·
              refine ⟨15729373927267328683062989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10486249284844885788708659 15729373927267328683062989)
              ·
                refine ⟨5898515222725248256148621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15729373927267328683062989 5898515222725248256148621)
                ·
                  refine ⟨2211943208521968096055733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5898515222725248256148621 2211943208521968096055733)
                  ·
                    refine ⟨207369675798934509005225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2211943208521968096055733 207369675798934509005225)
                    ·
                      rfl

theorem cell23_1211553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_1211553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211553 prefixEnd_1211553 := by exact prefixLift 1211553
  have htrace : WordTrace (prefixWord ++ tailWord_1211553) baseStart_1211553 baseEnd_1211553 := by
    simpa [prefixWord, tailWord_1211553, baseEnd_1211553] using wordTrace_append hprefix tailTrace_1211553
  have hstable : (prefixWord ++ tailWord_1211553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211553).length < 2 ^ (prefixWord ++ tailWord_1211553).sum := by decide
  have hdescent : baseEnd_1211553 < baseStart_1211553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211554 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_1211554 : Nat := 118140960795 + 1211554 * 2 ^ 59
def prefixEnd_1211554 : Nat := 4983230072969 + 3 ^ 40 * 1211554 * 2
def baseEnd_1211554 : Nat := 622109540877458023103171

theorem tailTrace_1211554 : CollatzResearch.WordTrace tailWord_1211554 prefixEnd_1211554 622109540877458023103171 := by
  unfold tailWord_1211554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11047251163188562448702429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29459336435169499863206477 11047251163188562448702429)
  ·
    refine ⟨4142719186195710918263411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11047251163188562448702429 4142719186195710918263411)
    ·
      refine ⟨6214078779293566377395117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4142719186195710918263411 6214078779293566377395117)
      ·
        refine ⟨2330279542235087391523169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6214078779293566377395117 2330279542235087391523169)
        ·
          refine ⟨1747709656676315543642377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2330279542235087391523169 1747709656676315543642377)
          ·
            refine ⟨1310782242507236657731783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1747709656676315543642377 1310782242507236657731783)
            ·
              refine ⟨1966173363760854986597675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310782242507236657731783 1966173363760854986597675)
              ·
                refine ⟨2949260045641282479896513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1966173363760854986597675 2949260045641282479896513)
                ·
                  refine ⟨2211945034230961859922385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2949260045641282479896513 2211945034230961859922385)
                  ·
                    refine ⟨1658958775673221394941789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2211945034230961859922385 1658958775673221394941789)
                    ·
                      refine ⟨622109540877458023103171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1658958775673221394941789 622109540877458023103171)
                      ·
                        rfl

theorem cell23_1211554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_1211554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211554 prefixEnd_1211554 := by exact prefixLift 1211554
  have htrace : WordTrace (prefixWord ++ tailWord_1211554) baseStart_1211554 baseEnd_1211554 := by
    simpa [prefixWord, tailWord_1211554, baseEnd_1211554] using wordTrace_append hprefix tailTrace_1211554
  have hstable : (prefixWord ++ tailWord_1211554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211554).length < 2 ^ (prefixWord ++ tailWord_1211554).sum := by decide
  have hdescent : baseEnd_1211554 < baseStart_1211554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211567 : List Nat := [1, 1, 2, 1, 2, 3, 3, 5, 1, 1, 3]
def baseStart_1211567 : Nat := 118140960795 + 1211567 * 2 ^ 59
def prefixEnd_1211567 : Nat := 4983230072969 + 3 ^ 40 * 1211567 * 2
def baseEnd_1211567 : Nat := 622116216125966472240611

theorem tailTrace_1211567 : CollatzResearch.WordTrace tailWord_1211567 prefixEnd_1211567 622116216125966472240611 := by
  unfold tailWord_1211567
  simp only [CollatzResearch.WordTrace]
  refine ⟨44189478801707153015032955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29459652534471435343355303 44189478801707153015032955)
  ·
    refine ⟨66284218202560729522549433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44189478801707153015032955 66284218202560729522549433)
    ·
      refine ⟨49713163651920547141912075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66284218202560729522549433 49713163651920547141912075)
      ·
        refine ⟨74569745477880820712868113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49713163651920547141912075 74569745477880820712868113)
        ·
          refine ⟨55927309108410615534651085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74569745477880820712868113 55927309108410615534651085)
          ·
            refine ⟨20972740915653980825494157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55927309108410615534651085 20972740915653980825494157)
            ·
              refine ⟨7864777843370242809560309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20972740915653980825494157 7864777843370242809560309)
              ·
                refine ⟨737322922815960263396279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7864777843370242809560309 737322922815960263396279)
                ·
                  refine ⟨1105984384223940395094419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737322922815960263396279 1105984384223940395094419)
                  ·
                    refine ⟨1658976576335910592641629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1105984384223940395094419 1658976576335910592641629)
                    ·
                      refine ⟨622116216125966472240611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1658976576335910592641629 622116216125966472240611)
                      ·
                        rfl

theorem cell23_1211567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 1, 1, 3].length) (baseStart_1211567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211567 prefixEnd_1211567 := by exact prefixLift 1211567
  have htrace : WordTrace (prefixWord ++ tailWord_1211567) baseStart_1211567 baseEnd_1211567 := by
    simpa [prefixWord, tailWord_1211567, baseEnd_1211567] using wordTrace_append hprefix tailTrace_1211567
  have hstable : (prefixWord ++ tailWord_1211567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211567).length < 2 ^ (prefixWord ++ tailWord_1211567).sum := by decide
  have hdescent : baseEnd_1211567 < baseStart_1211567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211570 : List Nat := [3, 2, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_1211570 : Nat := 118140960795 + 1211570 * 2 ^ 59
def prefixEnd_1211570 : Nat := 4983230072969 + 3 ^ 40 * 1211570 * 2
def baseEnd_1211570 : Nat := 207372585522643320167699

theorem tailTrace_1211570 : CollatzResearch.WordTrace tailWord_1211570 prefixEnd_1211570 207372585522643320167699 := by
  unfold tailWord_1211570
  simp only [CollatzResearch.WordTrace]
  refine ⟨11047397055174071131848041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29459725480464189684928109 11047397055174071131848041)
  ·
    refine ⟨8285547791380553348886031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11047397055174071131848041 8285547791380553348886031)
    ·
      refine ⟨12428321687070830023329047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8285547791380553348886031 12428321687070830023329047)
      ·
        refine ⟨18642482530606245034993571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12428321687070830023329047 18642482530606245034993571)
        ·
          refine ⟨27963723795909367552490357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18642482530606245034993571 27963723795909367552490357)
          ·
            refine ⟨2621599105866503208045971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27963723795909367552490357 2621599105866503208045971)
            ·
              refine ⟨3932398658799754812068957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2621599105866503208045971 3932398658799754812068957)
              ·
                refine ⟨1474649497049908054525859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3932398658799754812068957 1474649497049908054525859)
                ·
                  refine ⟨2211974245574862081788789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474649497049908054525859 2211974245574862081788789)
                  ·
                    refine ⟨207372585522643320167699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2211974245574862081788789 207372585522643320167699)
                    ·
                      rfl

theorem cell23_1211570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_1211570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211570 prefixEnd_1211570 := by exact prefixLift 1211570
  have htrace : WordTrace (prefixWord ++ tailWord_1211570) baseStart_1211570 baseEnd_1211570 := by
    simpa [prefixWord, tailWord_1211570, baseEnd_1211570] using wordTrace_append hprefix tailTrace_1211570
  have hstable : (prefixWord ++ tailWord_1211570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211570).length < 2 ^ (prefixWord ++ tailWord_1211570).sum := by decide
  have hdescent : baseEnd_1211570 < baseStart_1211570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211604 : List Nat := [2, 4, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_1211604 : Nat := 118140960795 + 1211604 * 2 ^ 59
def prefixEnd_1211604 : Nat := 4983230072969 + 3 ^ 40 * 1211604 * 2
def baseEnd_1211604 : Nat := 207378404970060942492647

theorem tailTrace_1211604 : CollatzResearch.WordTrace tailWord_1211604 prefixEnd_1211604 207378404970060942492647 := by
  unfold tailWord_1211604
  simp only [CollatzResearch.WordTrace]
  refine ⟨22095414151286554167064933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29460552201715405556086577 22095414151286554167064933)
  ·
    refine ⟨4142890153366228906324675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22095414151286554167064933 4142890153366228906324675)
    ·
      refine ⟨6214335230049343359487013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4142890153366228906324675 6214335230049343359487013)
      ·
        refine ⟨1165187855634251879903815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6214335230049343359487013 1165187855634251879903815)
        ·
          refine ⟨1747781783451377819855723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1165187855634251879903815 1747781783451377819855723)
          ·
            refine ⟨2621672675177066729783585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1747781783451377819855723 2621672675177066729783585)
            ·
              refine ⟨1966254506382800047337689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2621672675177066729783585 1966254506382800047337689)
              ·
                refine ⟨1474690879787100035503267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1966254506382800047337689 1474690879787100035503267)
                ·
                  refine ⟨2212036319680650053254901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474690879787100035503267 2212036319680650053254901)
                  ·
                    refine ⟨207378404970060942492647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2212036319680650053254901 207378404970060942492647)
                    ·
                      rfl

theorem cell23_1211604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_1211604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211604 prefixEnd_1211604 := by exact prefixLift 1211604
  have htrace : WordTrace (prefixWord ++ tailWord_1211604) baseStart_1211604 baseEnd_1211604 := by
    simpa [prefixWord, tailWord_1211604, baseEnd_1211604] using wordTrace_append hprefix tailTrace_1211604
  have hstable : (prefixWord ++ tailWord_1211604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211604).length < 2 ^ (prefixWord ++ tailWord_1211604).sum := by decide
  have hdescent : baseEnd_1211604 < baseStart_1211604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211607 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 3, 2, 2]
def baseStart_1211607 : Nat := 118140960795 + 1211607 * 2 ^ 59
def prefixEnd_1211607 : Nat := 4983230072969 + 3 ^ 40 * 1211607 * 2
def baseEnd_1211607 : Nat := 622136755352146315740427

theorem tailTrace_1211607 : CollatzResearch.WordTrace tailWord_1211607 prefixEnd_1211607 622136755352146315740427 := by
  unfold tailWord_1211607
  simp only [CollatzResearch.WordTrace]
  refine ⟨44190937721562239846489075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29460625147708159897659383 44190937721562239846489075)
  ·
    refine ⟨66286406582343359769733613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44190937721562239846489075 66286406582343359769733613)
    ·
      refine ⟨24857402468378759913650105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66286406582343359769733613 24857402468378759913650105)
      ·
        refine ⟨18643051851284069935237579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24857402468378759913650105 18643051851284069935237579)
        ·
          refine ⟨27964577776926104902856369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18643051851284069935237579 27964577776926104902856369)
          ·
            refine ⟨20973433332694578677142277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27964577776926104902856369 20973433332694578677142277)
            ·
              refine ⟨3932518749880233501964177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20973433332694578677142277 3932518749880233501964177)
              ·
                refine ⟨2949389062410175126473133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3932518749880233501964177 2949389062410175126473133)
                ·
                  refine ⟨1106020898403815672427425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2949389062410175126473133 1106020898403815672427425)
                  ·
                    refine ⟨829515673802861754320569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1106020898403815672427425 829515673802861754320569)
                    ·
                      refine ⟨622136755352146315740427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 829515673802861754320569 622136755352146315740427)
                      ·
                        rfl

theorem cell23_1211607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_1211607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211607 prefixEnd_1211607 := by exact prefixLift 1211607
  have htrace : WordTrace (prefixWord ++ tailWord_1211607) baseStart_1211607 baseEnd_1211607 := by
    simpa [prefixWord, tailWord_1211607, baseEnd_1211607] using wordTrace_append hprefix tailTrace_1211607
  have hstable : (prefixWord ++ tailWord_1211607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211607).length < 2 ^ (prefixWord ++ tailWord_1211607).sum := by decide
  have hdescent : baseEnd_1211607 < baseStart_1211607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211641 : List Nat := [1, 2, 1, 3, 1, 1, 7, 2, 1, 2, 2]
def baseStart_1211641 : Nat := 118140960795 + 1211641 * 2 ^ 59
def prefixEnd_1211641 : Nat := 4983230072969 + 3 ^ 40 * 1211641 * 2
def baseEnd_1211641 : Nat := 622154213694399182715271

theorem tailTrace_1211641 : CollatzResearch.WordTrace tailWord_1211641 prefixEnd_1211641 622154213694399182715271 := by
  unfold tailWord_1211641
  simp only [CollatzResearch.WordTrace]
  refine ⟨44192177803439063653226777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29461451868959375768817851 44192177803439063653226777)
  ·
    refine ⟨33144133352579297739920083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44192177803439063653226777 33144133352579297739920083)
    ·
      refine ⟨49716200028868946609880125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33144133352579297739920083 49716200028868946609880125)
      ·
        refine ⟨18643575010825854978705047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49716200028868946609880125 18643575010825854978705047)
        ·
          refine ⟨27965362516238782468057571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18643575010825854978705047 27965362516238782468057571)
          ·
            refine ⟨41948043774358173702086357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27965362516238782468057571 41948043774358173702086357)
            ·
              refine ⟨983157275961519696142649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 41948043774358173702086357 983157275961519696142649)
              ·
                refine ⟨737367956971139772106987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983157275961519696142649 737367956971139772106987)
                ·
                  refine ⟨1106051935456709658160481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737367956971139772106987 1106051935456709658160481)
                  ·
                    refine ⟨829538951592532243620361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1106051935456709658160481 829538951592532243620361)
                    ·
                      refine ⟨622154213694399182715271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 829538951592532243620361 622154213694399182715271)
                      ·
                        rfl

theorem cell23_1211641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_1211641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211641 prefixEnd_1211641 := by exact prefixLift 1211641
  have htrace : WordTrace (prefixWord ++ tailWord_1211641) baseStart_1211641 baseEnd_1211641 := by
    simpa [prefixWord, tailWord_1211641, baseEnd_1211641] using wordTrace_append hprefix tailTrace_1211641
  have hstable : (prefixWord ++ tailWord_1211641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211641).length < 2 ^ (prefixWord ++ tailWord_1211641).sum := by decide
  have hdescent : baseEnd_1211641 < baseStart_1211641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211657 : List Nat := [1, 2, 1, 1, 3, 3, 3, 3, 2, 1, 3]
def baseStart_1211657 : Nat := 118140960795 + 1211657 * 2 ^ 59
def prefixEnd_1211657 : Nat := 4983230072969 + 3 ^ 40 * 1211657 * 2
def baseEnd_1211657 : Nat := 622162429384871120115197

theorem tailTrace_1211657 : CollatzResearch.WordTrace tailWord_1211657 prefixEnd_1211657 622162429384871120115197 := by
  unfold tailWord_1211657
  simp only [CollatzResearch.WordTrace]
  refine ⟨44192761371381098385809225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29461840914254065590539483 44192761371381098385809225)
  ·
    refine ⟨33144571028535823789356919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44192761371381098385809225 33144571028535823789356919)
    ·
      refine ⟨49716856542803735684035379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33144571028535823789356919 49716856542803735684035379)
      ·
        refine ⟨74575284814205603526053069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49716856542803735684035379 74575284814205603526053069)
        ·
          refine ⟨27965731805327101322269901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74575284814205603526053069 27965731805327101322269901)
          ·
            refine ⟨10487149426997662995851213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27965731805327101322269901 10487149426997662995851213)
            ·
              refine ⟨3932681035124123623444205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10487149426997662995851213 3932681035124123623444205)
              ·
                refine ⟨1474755388171546358791577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3932681035124123623444205 1474755388171546358791577)
                ·
                  refine ⟨1106066541128659769093683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1474755388171546358791577 1106066541128659769093683)
                  ·
                    refine ⟨1659099811692989653640525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1106066541128659769093683 1659099811692989653640525)
                    ·
                      refine ⟨622162429384871120115197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1659099811692989653640525 622162429384871120115197)
                      ·
                        rfl

theorem cell23_1211657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 1, 3].length) (baseStart_1211657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211657 prefixEnd_1211657 := by exact prefixLift 1211657
  have htrace : WordTrace (prefixWord ++ tailWord_1211657) baseStart_1211657 baseEnd_1211657 := by
    simpa [prefixWord, tailWord_1211657, baseEnd_1211657] using wordTrace_append hprefix tailTrace_1211657
  have hstable : (prefixWord ++ tailWord_1211657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211657).length < 2 ^ (prefixWord ++ tailWord_1211657).sum := by decide
  have hdescent : baseEnd_1211657 < baseStart_1211657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211678 : List Nat := [4, 3, 2, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_1211678 : Nat := 118140960795 + 1211678 * 2 ^ 59
def prefixEnd_1211678 : Nat := 4983230072969 + 3 ^ 40 * 1211678 * 2
def baseEnd_1211678 : Nat := 622173212478615537952601

theorem tailTrace_1211678 : CollatzResearch.WordTrace tailWord_1211678 prefixEnd_1211678 622173212478615537952601 := by
  unfold tailWord_1211678
  simp only [CollatzResearch.WordTrace]
  refine ⟨5524190913038127371540461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29462351536203345981549125 5524190913038127371540461)
  ·
    refine ⟨2071571592389297764327673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5524190913038127371540461 2071571592389297764327673)
    ·
      refine ⟨1553678694291973323245755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2071571592389297764327673 1553678694291973323245755)
      ·
        refine ⟨2330518041437959984868633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1553678694291973323245755 2330518041437959984868633)
        ·
          refine ⟨1747888531078469988651475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2330518041437959984868633 1747888531078469988651475)
          ·
            refine ⟨2621832796617704982977213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1747888531078469988651475 2621832796617704982977213)
            ·
              refine ⟨983187298731639368616455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2621832796617704982977213 983187298731639368616455)
              ·
                refine ⟨1474780948097459052924683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983187298731639368616455 1474780948097459052924683)
                ·
                  refine ⟨2212171422146188579387025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474780948097459052924683 2212171422146188579387025)
                  ·
                    refine ⟨1659128566609641434540269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2212171422146188579387025 1659128566609641434540269)
                    ·
                      refine ⟨622173212478615537952601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1659128566609641434540269 622173212478615537952601)
                      ·
                        rfl

theorem cell23_1211678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_1211678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211678 prefixEnd_1211678 := by exact prefixLift 1211678
  have htrace : WordTrace (prefixWord ++ tailWord_1211678) baseStart_1211678 baseEnd_1211678 := by
    simpa [prefixWord, tailWord_1211678, baseEnd_1211678] using wordTrace_append hprefix tailTrace_1211678
  have hstable : (prefixWord ++ tailWord_1211678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211678).length < 2 ^ (prefixWord ++ tailWord_1211678).sum := by decide
  have hdescent : baseEnd_1211678 < baseStart_1211678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211730 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_1211730 : Nat := 118140960795 + 1211730 * 2 ^ 59
def prefixEnd_1211730 : Nat := 4983230072969 + 3 ^ 40 * 1211730 * 2
def baseEnd_1211730 : Nat := 622199913472649334502361

theorem tailTrace_1211730 : CollatzResearch.WordTrace tailWord_1211730 prefixEnd_1211730 622199913472649334502361 := by
  unfold tailWord_1211730
  simp only [CollatzResearch.WordTrace]
  refine ⟨11048855975029157963304161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29463615933411087902144429 11048855975029157963304161)
  ·
    refine ⟨8286641981271868472478121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11048855975029157963304161 8286641981271868472478121)
    ·
      refine ⟨6214981485953901354358591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8286641981271868472478121 6214981485953901354358591)
      ·
        refine ⟨9322472228930852031537887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6214981485953901354358591 9322472228930852031537887)
        ·
          refine ⟨13983708343396278047306831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9322472228930852031537887 13983708343396278047306831)
          ·
            refine ⟨20975562515094417070960247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13983708343396278047306831 20975562515094417070960247)
            ·
              refine ⟨31463343772641625606440371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20975562515094417070960247 31463343772641625606440371)
              ·
                refine ⟨47195015658962438409660557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31463343772641625606440371 47195015658962438409660557)
                ·
                  refine ⟨17698130872110914403622709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47195015658962438409660557 17698130872110914403622709)
                  ·
                    refine ⟨1659199769260398225339629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17698130872110914403622709 1659199769260398225339629)
                    ·
                      refine ⟨622199913472649334502361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1659199769260398225339629 622199913472649334502361)
                      ·
                        rfl

theorem cell23_1211730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_1211730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211730 prefixEnd_1211730 := by exact prefixLift 1211730
  have htrace : WordTrace (prefixWord ++ tailWord_1211730) baseStart_1211730 baseEnd_1211730 := by
    simpa [prefixWord, tailWord_1211730, baseEnd_1211730] using wordTrace_append hprefix tailTrace_1211730
  have hstable : (prefixWord ++ tailWord_1211730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211730).length < 2 ^ (prefixWord ++ tailWord_1211730).sum := by decide
  have hdescent : baseEnd_1211730 < baseStart_1211730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211763 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 4, 8]
def baseStart_1211763 : Nat := 118140960795 + 1211763 * 2 ^ 59
def prefixEnd_1211763 : Nat := 4983230072969 + 3 ^ 40 * 1211763 * 2
def baseEnd_1211763 : Nat := 207405619444749235129903

theorem tailTrace_1211763 : CollatzResearch.WordTrace tailWord_1211763 prefixEnd_1211763 207405619444749235129903 := by
  unfold tailWord_1211763
  simp only [CollatzResearch.WordTrace]
  refine ⟨44196627508997078489167943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29464418339331385659445295 44196627508997078489167943)
  ·
    refine ⟨66294941263495617733751915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44196627508997078489167943 66294941263495617733751915)
    ·
      refine ⟨99442411895243426600627873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66294941263495617733751915 99442411895243426600627873)
      ·
        refine ⟨74581808921432569950470905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99442411895243426600627873 74581808921432569950470905)
        ·
          refine ⟨55936356691074427462853179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74581808921432569950470905 55936356691074427462853179)
          ·
            refine ⟨83904535036611641194279769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55936356691074427462853179 83904535036611641194279769)
            ·
              refine ⟨62928401277458730895709827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83904535036611641194279769 62928401277458730895709827)
              ·
                refine ⟨94392601916188096343564741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62928401277458730895709827 94392601916188096343564741)
                ·
                  refine ⟨17698612859285268064418389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94392601916188096343564741 17698612859285268064418389)
                  ·
                    refine ⟨207405619444749235129903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17698612859285268064418389 207405619444749235129903)
                    ·
                      rfl

theorem cell23_1211763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 8].length) (baseStart_1211763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211763 prefixEnd_1211763 := by exact prefixLift 1211763
  have htrace : WordTrace (prefixWord ++ tailWord_1211763) baseStart_1211763 baseEnd_1211763 := by
    simpa [prefixWord, tailWord_1211763, baseEnd_1211763] using wordTrace_append hprefix tailTrace_1211763
  have hstable : (prefixWord ++ tailWord_1211763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211763).length < 2 ^ (prefixWord ++ tailWord_1211763).sum := by decide
  have hdescent : baseEnd_1211763 < baseStart_1211763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211770 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4]
def baseStart_1211770 : Nat := 118140960795 + 1211770 * 2 ^ 59
def prefixEnd_1211770 : Nat := 4983230072969 + 3 ^ 40 * 1211770 * 2
def baseEnd_1211770 : Nat := 622220452698829178002177

theorem tailTrace_1211770 : CollatzResearch.WordTrace tailWord_1211770 prefixEnd_1211770 622220452698829178002177 := by
  unfold tailWord_1211770
  simp only [CollatzResearch.WordTrace]
  refine ⟨11049220704992929671168191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29464588546647812456448509 11049220704992929671168191)
  ·
    refine ⟨16573831057489394506752287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11049220704992929671168191 16573831057489394506752287)
    ·
      refine ⟨24860746586234091760128431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16573831057489394506752287 24860746586234091760128431)
      ·
        refine ⟨37291119879351137640192647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24860746586234091760128431 37291119879351137640192647)
        ·
          refine ⟨55936679819026706460288971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37291119879351137640192647 55936679819026706460288971)
          ·
            refine ⟨83905019728540059690433457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55936679819026706460288971 83905019728540059690433457)
            ·
              refine ⟨62928764796405044767825093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83905019728540059690433457 62928764796405044767825093)
              ·
                refine ⟨11799143399325945893967205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62928764796405044767825093 11799143399325945893967205)
                ·
                  refine ⟨2212339387373614855118851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11799143399325945893967205 2212339387373614855118851)
                  ·
                    refine ⟨3318509081060422282678277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2212339387373614855118851 3318509081060422282678277)
                    ·
                      refine ⟨622220452698829178002177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3318509081060422282678277 622220452698829178002177)
                      ·
                        rfl

theorem cell23_1211770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_1211770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211770 prefixEnd_1211770 := by exact prefixLift 1211770
  have htrace : WordTrace (prefixWord ++ tailWord_1211770) baseStart_1211770 baseEnd_1211770 := by
    simpa [prefixWord, tailWord_1211770, baseEnd_1211770] using wordTrace_append hprefix tailTrace_1211770
  have hstable : (prefixWord ++ tailWord_1211770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211770).length < 2 ^ (prefixWord ++ tailWord_1211770).sum := by decide
  have hdescent : baseEnd_1211770 < baseStart_1211770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211807 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 3]
def baseStart_1211807 : Nat := 118140960795 + 1211807 * 2 ^ 59
def prefixEnd_1211807 : Nat := 4983230072969 + 3 ^ 40 * 1211807 * 2
def baseEnd_1211807 : Nat := 622239451483045533239507

theorem tailTrace_1211807 : CollatzResearch.WordTrace tailWord_1211807 prefixEnd_1211807 622239451483045533239507 := by
  unfold tailWord_1211807
  simp only [CollatzResearch.WordTrace]
  refine ⟨44198232320837674003769675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29465488213891782669179783 44198232320837674003769675)
  ·
    refine ⟨66297348481256511005654513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44198232320837674003769675 66297348481256511005654513)
    ·
      refine ⟨49723011360942383254240885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66297348481256511005654513 49723011360942383254240885)
      ·
        refine ⟨4661532315088348430085083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49723011360942383254240885 4661532315088348430085083)
        ·
          refine ⟨6992298472632522645127625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4661532315088348430085083 6992298472632522645127625)
          ·
            refine ⟨5244223854474391983845719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6992298472632522645127625 5244223854474391983845719)
            ·
              refine ⟨7866335781711587975768579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5244223854474391983845719 7866335781711587975768579)
              ·
                refine ⟨11799503672567381963652869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7866335781711587975768579 11799503672567381963652869)
                ·
                  refine ⟨2212406938606384118184913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11799503672567381963652869 2212406938606384118184913)
                  ·
                    refine ⟨1659305203954788088638685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2212406938606384118184913 1659305203954788088638685)
                    ·
                      refine ⟨622239451483045533239507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1659305203954788088638685 622239451483045533239507)
                      ·
                        rfl

theorem cell23_1211807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_1211807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211807 prefixEnd_1211807 := by exact prefixLift 1211807
  have htrace : WordTrace (prefixWord ++ tailWord_1211807) baseStart_1211807 baseEnd_1211807 := by
    simpa [prefixWord, tailWord_1211807, baseEnd_1211807] using wordTrace_append hprefix tailTrace_1211807
  have hstable : (prefixWord ++ tailWord_1211807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211807).length < 2 ^ (prefixWord ++ tailWord_1211807).sum := by decide
  have hdescent : baseEnd_1211807 < baseStart_1211807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211864 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 2, 3, 2]
def baseStart_1211864 : Nat := 118140960795 + 1211864 * 2 ^ 59
def prefixEnd_1211864 : Nat := 4983230072969 + 3 ^ 40 * 1211864 * 2
def baseEnd_1211864 : Nat := 622268719880351810226745

theorem tailTrace_1211864 : CollatzResearch.WordTrace tailWord_1211864 prefixEnd_1211864 622268719880351810226745 := by
  unfold tailWord_1211864
  simp only [CollatzResearch.WordTrace]
  refine ⟨22100155640815586369297323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29466874187754115159063097 22100155640815586369297323)
  ·
    refine ⟨33150233461223379553945985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22100155640815586369297323 33150233461223379553945985)
    ·
      refine ⟨24862675095917534665459489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33150233461223379553945985 24862675095917534665459489)
      ·
        refine ⟨18647006321938150999094617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24862675095917534665459489 18647006321938150999094617)
        ·
          refine ⟨13985254741453613249320963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18647006321938150999094617 13985254741453613249320963)
          ·
            refine ⟨20977882112180419873981445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13985254741453613249320963 20977882112180419873981445)
            ·
              refine ⟨3933352896033828726371521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20977882112180419873981445 3933352896033828726371521)
              ·
                refine ⟨2950014672025371544778641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3933352896033828726371521 2950014672025371544778641)
                ·
                  refine ⟨2212511004019028658583981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2950014672025371544778641 2212511004019028658583981)
                  ·
                    refine ⟨829691626507135746968993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2212511004019028658583981 829691626507135746968993)
                    ·
                      refine ⟨622268719880351810226745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 829691626507135746968993 622268719880351810226745)
                      ·
                        rfl

theorem cell23_1211864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_1211864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211864 prefixEnd_1211864 := by exact prefixLift 1211864
  have htrace : WordTrace (prefixWord ++ tailWord_1211864) baseStart_1211864 baseEnd_1211864 := by
    simpa [prefixWord, tailWord_1211864, baseEnd_1211864] using wordTrace_append hprefix tailTrace_1211864
  have hstable : (prefixWord ++ tailWord_1211864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211864).length < 2 ^ (prefixWord ++ tailWord_1211864).sum := by decide
  have hdescent : baseEnd_1211864 < baseStart_1211864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211871 : List Nat := [1, 1, 2, 3, 3, 1, 3, 4, 1, 1, 3]
def baseStart_1211871 : Nat := 118140960795 + 1211871 * 2 ^ 59
def prefixEnd_1211871 : Nat := 4983230072969 + 3 ^ 40 * 1211871 * 2
def baseEnd_1211871 : Nat := 622272314244933282839213

theorem tailTrace_1211871 : CollatzResearch.WordTrace tailWord_1211871 prefixEnd_1211871 622272314244933282839213 := by
  unfold tailWord_1211871
  simp only [CollatzResearch.WordTrace]
  refine ⟨44200566592605812934099467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29467044395070541956066311 44200566592605812934099467)
  ·
    refine ⟨66300849888908719401149201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44200566592605812934099467 66300849888908719401149201)
    ·
      refine ⟨49725637416681539550861901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66300849888908719401149201 49725637416681539550861901)
      ·
        refine ⟨18647114031255577331573213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49725637416681539550861901 18647114031255577331573213)
        ·
          refine ⟨6992667761720841499339955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18647114031255577331573213 6992667761720841499339955)
          ·
            refine ⟨10489001642581262249009933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6992667761720841499339955 10489001642581262249009933)
            ·
              refine ⟨3933375615967973343378725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10489001642581262249009933 3933375615967973343378725)
              ·
                refine ⟨737507927993995001883511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3933375615967973343378725 737507927993995001883511)
                ·
                  refine ⟨1106261891990992502825267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737507927993995001883511 1106261891990992502825267)
                  ·
                    refine ⟨1659392837986488754237901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1106261891990992502825267 1659392837986488754237901)
                    ·
                      refine ⟨622272314244933282839213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1659392837986488754237901 622272314244933282839213)
                      ·
                        rfl

theorem cell23_1211871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_1211871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211871 prefixEnd_1211871 := by exact prefixLift 1211871
  have htrace : WordTrace (prefixWord ++ tailWord_1211871) baseStart_1211871 baseEnd_1211871 := by
    simpa [prefixWord, tailWord_1211871, baseEnd_1211871] using wordTrace_append hprefix tailTrace_1211871
  have hstable : (prefixWord ++ tailWord_1211871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211871).length < 2 ^ (prefixWord ++ tailWord_1211871).sum := by decide
  have hdescent : baseEnd_1211871 < baseStart_1211871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211894 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_1211894 : Nat := 118140960795 + 1211894 * 2 ^ 59
def prefixEnd_1211894 : Nat := 4983230072969 + 3 ^ 40 * 1211894 * 2
def baseEnd_1211894 : Nat := 622284124299986692851607

theorem tailTrace_1211894 : CollatzResearch.WordTrace tailWord_1211894 prefixEnd_1211894 622284124299986692851607 := by
  unfold tailWord_1211894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2762587841970155491386671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29467603647681658574791157 2762587841970155491386671)
  ·
    refine ⟨4143881762955233237080007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2762587841970155491386671 4143881762955233237080007)
    ·
      refine ⟨6215822644432849855620011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4143881762955233237080007 6215822644432849855620011)
      ·
        refine ⟨9323733966649274783430017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6215822644432849855620011 9323733966649274783430017)
        ·
          refine ⟨6992800474986956087572513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9323733966649274783430017 6992800474986956087572513)
          ·
            refine ⟨5244600356240217065679385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6992800474986956087572513 5244600356240217065679385)
            ·
              refine ⟨3933450267180162799259539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5244600356240217065679385 3933450267180162799259539)
              ·
                refine ⟨5900175400770244198889309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3933450267180162799259539 5900175400770244198889309)
                ·
                  refine ⟨2212565775288841574583491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5900175400770244198889309 2212565775288841574583491)
                  ·
                    refine ⟨3318848662933262361875237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2212565775288841574583491 3318848662933262361875237)
                    ·
                      refine ⟨622284124299986692851607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3318848662933262361875237 622284124299986692851607)
                      ·
                        rfl

theorem cell23_1211894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_1211894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211894 prefixEnd_1211894 := by exact prefixLift 1211894
  have htrace : WordTrace (prefixWord ++ tailWord_1211894) baseStart_1211894 baseEnd_1211894 := by
    simpa [prefixWord, tailWord_1211894, baseEnd_1211894] using wordTrace_append hprefix tailTrace_1211894
  have hstable : (prefixWord ++ tailWord_1211894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211894).length < 2 ^ (prefixWord ++ tailWord_1211894).sum := by decide
  have hdescent : baseEnd_1211894 < baseStart_1211894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211900 : List Nat := [2, 2, 2, 1, 2, 1, 2, 11]
def baseStart_1211900 : Nat := 118140960795 + 1211900 * 2 ^ 59
def prefixEnd_1211900 : Nat := 4983230072969 + 3 ^ 40 * 1211900 * 2
def baseEnd_1211900 : Nat := 23047674266070876643577

theorem tailTrace_1211900 : CollatzResearch.WordTrace tailWord_1211900 prefixEnd_1211900 23047674266070876643577 := by
  unfold tailWord_1211900
  simp only [CollatzResearch.WordTrace]
  refine ⟨22100812154750375443452577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29467749539667167257936769 22100812154750375443452577)
  ·
    refine ⟨16575609116062781582589433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22100812154750375443452577 16575609116062781582589433)
    ·
      refine ⟨12431706837047086186942075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16575609116062781582589433 12431706837047086186942075)
      ·
        refine ⟨18647560255570629280413113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12431706837047086186942075 18647560255570629280413113)
        ·
          refine ⟨13985670191677971960309835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18647560255570629280413113 13985670191677971960309835)
          ·
            refine ⟨20978505287516957940464753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13985670191677971960309835 20978505287516957940464753)
            ·
              refine ⟨15733878965637718455348565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20978505287516957940464753 15733878965637718455348565)
              ·
                refine ⟨23047674266070876643577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 15733878965637718455348565 23047674266070876643577)
                ·
                  rfl

theorem cell23_1211900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 11].length) (baseStart_1211900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211900 prefixEnd_1211900 := by exact prefixLift 1211900
  have htrace : WordTrace (prefixWord ++ tailWord_1211900) baseStart_1211900 baseEnd_1211900 := by
    simpa [prefixWord, tailWord_1211900, baseEnd_1211900] using wordTrace_append hprefix tailTrace_1211900
  have hstable : (prefixWord ++ tailWord_1211900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211900).length < 2 ^ (prefixWord ++ tailWord_1211900).sum := by decide
  have hdescent : baseEnd_1211900 < baseStart_1211900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211908 : List Nat := [2, 3, 2, 3, 2, 2, 2, 1, 1, 5]
def baseStart_1211908 : Nat := 118140960795 + 1211908 * 2 ^ 59
def prefixEnd_1211908 : Nat := 4983230072969 + 3 ^ 40 * 1211908 * 2
def baseEnd_1211908 : Nat := 207430437676383212692181

theorem tailTrace_1211908 : CollatzResearch.WordTrace tailWord_1211908 prefixEnd_1211908 207430437676383212692181 := by
  unfold tailWord_1211908
  simp only [CollatzResearch.WordTrace]
  refine ⟨22100958046735884126598189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29467944062314512168797585 22100958046735884126598189)
  ·
    refine ⟨8287859267525956547474321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22100958046735884126598189 8287859267525956547474321)
    ·
      refine ⟨6215894450644467410605741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8287859267525956547474321 6215894450644467410605741)
      ·
        refine ⟨2330960418991675278977153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6215894450644467410605741 2330960418991675278977153)
        ·
          refine ⟨1748220314243756459232865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2330960418991675278977153 1748220314243756459232865)
          ·
            refine ⟨1311165235682817344424649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1748220314243756459232865 1311165235682817344424649)
            ·
              refine ⟨983373926762113008318487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1311165235682817344424649 983373926762113008318487)
              ·
                refine ⟨1475060890143169512477731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983373926762113008318487 1475060890143169512477731)
                ·
                  refine ⟨2212591335214754268716597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1475060890143169512477731 2212591335214754268716597)
                  ·
                    refine ⟨207430437676383212692181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2212591335214754268716597 207430437676383212692181)
                    ·
                      rfl

theorem cell23_1211908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_1211908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211908 prefixEnd_1211908 := by exact prefixLift 1211908
  have htrace : WordTrace (prefixWord ++ tailWord_1211908) baseStart_1211908 baseEnd_1211908 := by
    simpa [prefixWord, tailWord_1211908, baseEnd_1211908] using wordTrace_append hprefix tailTrace_1211908
  have hstable : (prefixWord ++ tailWord_1211908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211908).length < 2 ^ (prefixWord ++ tailWord_1211908).sum := by decide
  have hdescent : baseEnd_1211908 < baseStart_1211908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211911 : List Nat := [1, 1, 4, 3, 2, 1, 4, 1, 1, 1, 4]
def baseStart_1211911 : Nat := 118140960795 + 1211911 * 2 ^ 59
def prefixEnd_1211911 : Nat := 4983230072969 + 3 ^ 40 * 1211911 * 2
def baseEnd_1211911 : Nat := 622292853471113126339029

theorem tailTrace_1211911 : CollatzResearch.WordTrace tailWord_1211911 prefixEnd_1211911 622292853471113126339029 := by
  unfold tailWord_1211911
  simp only [CollatzResearch.WordTrace]
  refine ⟨44202025512460899765555587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29468017008307266510370391 44202025512460899765555587)
  ·
    refine ⟨66303038268691349648333381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44202025512460899765555587 66303038268691349648333381)
    ·
      refine ⟨12431819675379628059062509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66303038268691349648333381 12431819675379628059062509)
      ·
        refine ⟨4661932378267360522148441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12431819675379628059062509 4661932378267360522148441)
        ·
          refine ⟨3496449283700520391611331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4661932378267360522148441 3496449283700520391611331)
          ·
            refine ⟨5244673925550780587416997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3496449283700520391611331 5244673925550780587416997)
            ·
              refine ⟨983376361040771360140687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5244673925550780587416997 983376361040771360140687)
              ·
                refine ⟨1475064541561157040211031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983376361040771360140687 1475064541561157040211031)
                ·
                  refine ⟨2212596812341735560316547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1475064541561157040211031 2212596812341735560316547)
                  ·
                    refine ⟨3318895218512603340474821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2212596812341735560316547 3318895218512603340474821)
                    ·
                      refine ⟨622292853471113126339029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3318895218512603340474821 622292853471113126339029)
                      ·
                        rfl

theorem cell23_1211911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_1211911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211911 prefixEnd_1211911 := by exact prefixLift 1211911
  have htrace : WordTrace (prefixWord ++ tailWord_1211911) baseStart_1211911 baseEnd_1211911 := by
    simpa [prefixWord, tailWord_1211911, baseEnd_1211911] using wordTrace_append hprefix tailTrace_1211911
  have hstable : (prefixWord ++ tailWord_1211911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211911).length < 2 ^ (prefixWord ++ tailWord_1211911).sum := by decide
  have hdescent : baseEnd_1211911 < baseStart_1211911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211928 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 3, 2, 2]
def baseStart_1211928 : Nat := 118140960795 + 1211928 * 2 ^ 59
def prefixEnd_1211928 : Nat := 4983230072969 + 3 ^ 40 * 1211928 * 2
def baseEnd_1211928 : Nat := 622301582642239559826451

theorem tailTrace_1211928 : CollatzResearch.WordTrace tailWord_1211928 prefixEnd_1211928 622301582642239559826451 := by
  unfold tailWord_1211928
  simp only [CollatzResearch.WordTrace]
  refine ⟨22101322776699655834462219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29468430368932874445949625 22101322776699655834462219)
  ·
    refine ⟨33151984165049483751693329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22101322776699655834462219 33151984165049483751693329)
    ·
      refine ⟨24863988123787112813769997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33151984165049483751693329 24863988123787112813769997)
      ·
        refine ⟨9323995546420167305163749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24863988123787112813769997 9323995546420167305163749)
        ·
          refine ⟨1748249164953781369718203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9323995546420167305163749 1748249164953781369718203)
          ·
            refine ⟨2622373747430672054577305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1748249164953781369718203 2622373747430672054577305)
            ·
              refine ⟨1966780310573004040932979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2622373747430672054577305 1966780310573004040932979)
              ·
                refine ⟨2950170465859506061399469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1966780310573004040932979 2950170465859506061399469)
                ·
                  refine ⟨1106313924697314773024801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2950170465859506061399469 1106313924697314773024801)
                  ·
                    refine ⟨829735443522986079768601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1106313924697314773024801 829735443522986079768601)
                    ·
                      refine ⟨622301582642239559826451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 829735443522986079768601 622301582642239559826451)
                      ·
                        rfl

theorem cell23_1211928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_1211928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211928 prefixEnd_1211928 := by exact prefixLift 1211928
  have htrace : WordTrace (prefixWord ++ tailWord_1211928) baseStart_1211928 baseEnd_1211928 := by
    simpa [prefixWord, tailWord_1211928, baseEnd_1211928] using wordTrace_append hprefix tailTrace_1211928
  have hstable : (prefixWord ++ tailWord_1211928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211928).length < 2 ^ (prefixWord ++ tailWord_1211928).sum := by decide
  have hdescent : baseEnd_1211928 < baseStart_1211928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211957 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_1211957 : Nat := 118140960795 + 1211957 * 2 ^ 59
def prefixEnd_1211957 : Nat := 4983230072969 + 3 ^ 40 * 1211957 * 2
def baseEnd_1211957 : Nat := 622316473581219946363817

theorem tailTrace_1211957 : CollatzResearch.WordTrace tailWord_1211957 prefixEnd_1211957 622316473581219946363817 := by
  unfold tailWord_1211957
  simp only [CollatzResearch.WordTrace]
  refine ⟨44203703270294249621730125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29469135513529499747820083 44203703270294249621730125)
  ·
    refine ⟨16576388726360343608148797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44203703270294249621730125 16576388726360343608148797)
    ·
      refine ⟨6216145772385128853055799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16576388726360343608148797 6216145772385128853055799)
      ·
        refine ⟨9324218658577693279583699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6216145772385128853055799 9324218658577693279583699)
        ·
          refine ⟨13986327987866539919375549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9324218658577693279583699 13986327987866539919375549)
          ·
            refine ⟨5244872995449952469765831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13986327987866539919375549 5244872995449952469765831)
            ·
              refine ⟨7867309493174928704648747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5244872995449952469765831 7867309493174928704648747)
              ·
                refine ⟨11800964239762393056973121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7867309493174928704648747 11800964239762393056973121)
                ·
                  refine ⟨8850723179821794792729841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11800964239762393056973121 8850723179821794792729841)
                  ·
                    refine ⟨6638042384866346094547381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8850723179821794792729841 6638042384866346094547381)
                    ·
                      refine ⟨622316473581219946363817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6638042384866346094547381 622316473581219946363817)
                      ·
                        rfl

theorem cell23_1211957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_1211957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1211957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1211957 prefixEnd_1211957 := by exact prefixLift 1211957
  have htrace : WordTrace (prefixWord ++ tailWord_1211957) baseStart_1211957 baseEnd_1211957 := by
    simpa [prefixWord, tailWord_1211957, baseEnd_1211957] using wordTrace_append hprefix tailTrace_1211957
  have hstable : (prefixWord ++ tailWord_1211957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211957).length < 2 ^ (prefixWord ++ tailWord_1211957).sum := by decide
  have hdescent : baseEnd_1211957 < baseStart_1211957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212007 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 7]
def baseStart_1212007 : Nat := 118140960795 + 1212007 * 2 ^ 59
def prefixEnd_1212007 : Nat := 4983230072969 + 3 ^ 40 * 1212007 * 2
def baseEnd_1212007 : Nat := 69149127512660527859843

theorem tailTrace_1212007 : CollatzResearch.WordTrace tailWord_1212007 prefixEnd_1212007 69149127512660527859843 := by
  unfold tailWord_1212007
  simp only [CollatzResearch.WordTrace]
  refine ⟨44205526920113108161050275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29470351280075405440700183 44205526920113108161050275)
  ·
    refine ⟨66308290380169662241575413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44205526920113108161050275 66308290380169662241575413)
    ·
      refine ⟨6216402223140905835147695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66308290380169662241575413 6216402223140905835147695)
      ·
        refine ⟨9324603334711358752721543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6216402223140905835147695 9324603334711358752721543)
        ·
          refine ⟨13986905002067038129082315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9324603334711358752721543 13986905002067038129082315)
          ·
            refine ⟨20980357503100557193623473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13986905002067038129082315 20980357503100557193623473)
            ·
              refine ⟨15735268127325417895217605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20980357503100557193623473 15735268127325417895217605)
              ·
                refine ⟨2950362773873515855353301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15735268127325417895217605 2950362773873515855353301)
                ·
                  refine ⟨69149127512660527859843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2950362773873515855353301 69149127512660527859843)
                  ·
                    rfl

theorem cell23_1212007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 7].length) (baseStart_1212007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212007 prefixEnd_1212007 := by exact prefixLift 1212007
  have htrace : WordTrace (prefixWord ++ tailWord_1212007) baseStart_1212007 baseEnd_1212007 := by
    simpa [prefixWord, tailWord_1212007, baseEnd_1212007] using wordTrace_append hprefix tailTrace_1212007
  have hstable : (prefixWord ++ tailWord_1212007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212007).length < 2 ^ (prefixWord ++ tailWord_1212007).sum := by decide
  have hdescent : baseEnd_1212007 < baseStart_1212007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212041 : List Nat := [1, 2, 1, 1, 4, 1, 6, 2, 5]
def baseStart_1212041 : Nat := 118140960795 + 1212041 * 2 ^ 59
def prefixEnd_1212041 : Nat := 4983230072969 + 3 ^ 40 * 1212041 * 2
def baseEnd_1212041 : Nat := 69151067328466401968159

theorem tailTrace_1212041 : CollatzResearch.WordTrace tailWord_1212041 prefixEnd_1212041 69151067328466401968159 := by
  unfold tailWord_1212041
  simp only [CollatzResearch.WordTrace]
  refine ⟨44206767001989931967787977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29471178001326621311858651 44206767001989931967787977)
  ·
    refine ⟨33155075251492448975840983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44206767001989931967787977 33155075251492448975840983)
    ·
      refine ⟨49732612877238673463761475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33155075251492448975840983 49732612877238673463761475)
      ·
        refine ⟨74598919315858010195642213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49732612877238673463761475 74598919315858010195642213)
        ·
          refine ⟨13987297371723376911682915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74598919315858010195642213 13987297371723376911682915)
          ·
            refine ⟨20980946057585065367524373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13987297371723376911682915 20980946057585065367524373)
            ·
              refine ⟨983481846449299939102705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20980946057585065367524373 983481846449299939102705)
              ·
                refine ⟨737611384836974954327029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983481846449299939102705 737611384836974954327029)
                ·
                  refine ⟨69151067328466401968159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 737611384836974954327029 69151067328466401968159)
                  ·
                    rfl

theorem cell23_1212041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 5].length) (baseStart_1212041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212041 prefixEnd_1212041 := by exact prefixLift 1212041
  have htrace : WordTrace (prefixWord ++ tailWord_1212041) baseStart_1212041 baseEnd_1212041 := by
    simpa [prefixWord, tailWord_1212041, baseEnd_1212041] using wordTrace_append hprefix tailTrace_1212041
  have hstable : (prefixWord ++ tailWord_1212041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212041).length < 2 ^ (prefixWord ++ tailWord_1212041).sum := by decide
  have hdescent : baseEnd_1212041 < baseStart_1212041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212044 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 1, 7, 2]
def baseStart_1212044 : Nat := 118140960795 + 1212044 * 2 ^ 59
def prefixEnd_1212044 : Nat := 4983230072969 + 3 ^ 40 * 1212044 * 2
def baseEnd_1212044 : Nat := 622361146398161105975917

theorem tailTrace_1212044 : CollatzResearch.WordTrace tailWord_1212044 prefixEnd_1212044 622361146398161105975917 := by
  unfold tailWord_1212044
  simp only [CollatzResearch.WordTrace]
  refine ⟨22103438210489531740073593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29471250947319375653431457 22103438210489531740073593)
  ·
    refine ⟨16577578657867148805055195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22103438210489531740073593 16577578657867148805055195)
    ·
      refine ⟨24866367986800723207582793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16577578657867148805055195 24866367986800723207582793)
      ·
        refine ⟨18649775990100542405687095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24866367986800723207582793 18649775990100542405687095)
        ·
          refine ⟨27974663985150813608530643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18649775990100542405687095 27974663985150813608530643)
          ·
            refine ⟨41961995977726220412795965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27974663985150813608530643 41961995977726220412795965)
            ·
              refine ⟨15735748491647332654798487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41961995977726220412795965 15735748491647332654798487)
              ·
                refine ⟨23603622737470998982197731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15735748491647332654798487 23603622737470998982197731)
                ·
                  refine ⟨35405434106206498473296597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23603622737470998982197731 35405434106206498473296597)
                  ·
                    refine ⟨829814861864214807967889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35405434106206498473296597 829814861864214807967889)
                    ·
                      refine ⟨622361146398161105975917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 829814861864214807967889 622361146398161105975917)
                      ·
                        rfl

theorem cell23_1212044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_1212044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212044 prefixEnd_1212044 := by exact prefixLift 1212044
  have htrace : WordTrace (prefixWord ++ tailWord_1212044) baseStart_1212044 baseEnd_1212044 := by
    simpa [prefixWord, tailWord_1212044, baseEnd_1212044] using wordTrace_append hprefix tailTrace_1212044
  have hstable : (prefixWord ++ tailWord_1212044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212044).length < 2 ^ (prefixWord ++ tailWord_1212044).sum := by decide
  have hdescent : baseEnd_1212044 < baseStart_1212044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212148 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 8]
def baseStart_1212148 : Nat := 118140960795 + 1212148 * 2 ^ 59
def prefixEnd_1212148 : Nat := 4983230072969 + 3 ^ 40 * 1212148 * 2
def baseEnd_1212148 : Nat := 69157172042914299897271

theorem tailTrace_1212148 : CollatzResearch.WordTrace tailWord_1212148 prefixEnd_1212148 69157172042914299897271 := by
  unfold tailWord_1212148
  simp only [CollatzResearch.WordTrace]
  refine ⟨22105334806301144620966549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29473779741734859494622065 22105334806301144620966549)
  ·
    refine ⟨1036187569045366154107807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22105334806301144620966549 1036187569045366154107807)
    ·
      refine ⟨1554281353568049231161711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1036187569045366154107807 1554281353568049231161711)
      ·
        refine ⟨2331422030352073846742567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1554281353568049231161711 2331422030352073846742567)
        ·
          refine ⟨3497133045528110770113851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2331422030352073846742567 3497133045528110770113851)
          ·
            refine ⟨5245699568292166155170777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3497133045528110770113851 5245699568292166155170777)
            ·
              refine ⟨3934274676219124616378083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5245699568292166155170777 3934274676219124616378083)
              ·
                refine ⟨5901412014328686924567125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3934274676219124616378083 5901412014328686924567125)
                ·
                  refine ⟨69157172042914299897271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5901412014328686924567125 69157172042914299897271)
                  ·
                    rfl

theorem cell23_1212148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_1212148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212148 prefixEnd_1212148 := by exact prefixLift 1212148
  have htrace : WordTrace (prefixWord ++ tailWord_1212148) baseStart_1212148 baseEnd_1212148 := by
    simpa [prefixWord, tailWord_1212148, baseEnd_1212148] using wordTrace_append hprefix tailTrace_1212148
  have hstable : (prefixWord ++ tailWord_1212148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212148).length < 2 ^ (prefixWord ++ tailWord_1212148).sum := by decide
  have hdescent : baseEnd_1212148 < baseStart_1212148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212151 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 4, 3, 2]
def baseStart_1212151 : Nat := 118140960795 + 1212151 * 2 ^ 59
def prefixEnd_1212151 : Nat := 4983230072969 + 3 ^ 40 * 1212151 * 2
def baseEnd_1212151 : Nat := 622416088828192187337925

theorem tailTrace_1212151 : CollatzResearch.WordTrace tailWord_1212151 prefixEnd_1212151 622416088828192187337925 := by
  unfold tailWord_1212151
  simp only [CollatzResearch.WordTrace]
  refine ⟨44210779031591420754292307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29473852687727613836194871 44210779031591420754292307)
  ·
    refine ⟨66316168547387131131438461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44210779031591420754292307 66316168547387131131438461)
    ·
      refine ⟨24868563205270174174289423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66316168547387131131438461 24868563205270174174289423)
      ·
        refine ⟨37302844807905261261434135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24868563205270174174289423 37302844807905261261434135)
        ·
          refine ⟨55954267211857891892151203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37302844807905261261434135 55954267211857891892151203)
          ·
            refine ⟨83931400817786837838226805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55954267211857891892151203 83931400817786837838226805)
            ·
              refine ⟨7868568826667516047333763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83931400817786837838226805 7868568826667516047333763)
              ·
                refine ⟨11802853240001274071000645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7868568826667516047333763 11802853240001274071000645)
                ·
                  refine ⟨2213034982500238888312621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11802853240001274071000645 2213034982500238888312621)
                  ·
                    refine ⟨829888118437589583117233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2213034982500238888312621 829888118437589583117233)
                    ·
                      refine ⟨622416088828192187337925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 829888118437589583117233 622416088828192187337925)
                      ·
                        rfl

theorem cell23_1212151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 3, 2].length) (baseStart_1212151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212151 prefixEnd_1212151 := by exact prefixLift 1212151
  have htrace : WordTrace (prefixWord ++ tailWord_1212151) baseStart_1212151 baseEnd_1212151 := by
    simpa [prefixWord, tailWord_1212151, baseEnd_1212151] using wordTrace_append hprefix tailTrace_1212151
  have hstable : (prefixWord ++ tailWord_1212151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212151).length < 2 ^ (prefixWord ++ tailWord_1212151).sum := by decide
  have hdescent : baseEnd_1212151 < baseStart_1212151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212178 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1212178 : Nat := 118140960795 + 1212178 * 2 ^ 59
def prefixEnd_1212178 : Nat := 4983230072969 + 3 ^ 40 * 1212178 * 2
def baseEnd_1212178 : Nat := 207476650935287860566767

theorem tailTrace_1212178 : CollatzResearch.WordTrace tailWord_1212178 prefixEnd_1212178 207476650935287860566767 := by
  unfold tailWord_1212178
  simp only [CollatzResearch.WordTrace]
  refine ⟨11052940950623401091381297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29474509201662402910350125 11052940950623401091381297)
  ·
    refine ⟨8289705712967550818535973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11052940950623401091381297 8289705712967550818535973)
    ·
      refine ⟨1554319821181415778475495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8289705712967550818535973 1554319821181415778475495)
      ·
        refine ⟨2331479731772123667713243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1554319821181415778475495 2331479731772123667713243)
        ·
          refine ⟨3497219597658185501569865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2331479731772123667713243 3497219597658185501569865)
          ·
            refine ⟨2622914698243639126177399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3497219597658185501569865 2622914698243639126177399)
            ·
              refine ⟨3934372047365458689266099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2622914698243639126177399 3934372047365458689266099)
              ·
                refine ⟨5901558071048188033899149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3934372047365458689266099 5901558071048188033899149)
                ·
                  refine ⟨2213084276643070512712181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5901558071048188033899149 2213084276643070512712181)
                  ·
                    refine ⟨207476650935287860566767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2213084276643070512712181 207476650935287860566767)
                    ·
                      rfl

theorem cell23_1212178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1212178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212178 prefixEnd_1212178 := by exact prefixLift 1212178
  have htrace : WordTrace (prefixWord ++ tailWord_1212178) baseStart_1212178 baseEnd_1212178 := by
    simpa [prefixWord, tailWord_1212178, baseEnd_1212178] using wordTrace_append hprefix tailTrace_1212178
  have hstable : (prefixWord ++ tailWord_1212178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212178).length < 2 ^ (prefixWord ++ tailWord_1212178).sum := by decide
  have hdescent : baseEnd_1212178 < baseStart_1212178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212181 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_1212181 : Nat := 118140960795 + 1212181 * 2 ^ 59
def prefixEnd_1212181 : Nat := 4983230072969 + 3 ^ 40 * 1212181 * 2
def baseEnd_1212181 : Nat := 622431493247827069962787

theorem tailTrace_1212181 : CollatzResearch.WordTrace tailWord_1212181 prefixEnd_1212181 622431493247827069962787 := by
  unfold tailWord_1212181
  simp only [CollatzResearch.WordTrace]
  refine ⟨44211873221482735877884397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29474582147655157251922931 44211873221482735877884397)
  ·
    refine ⟨16579452458056025954206649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44211873221482735877884397 16579452458056025954206649)
    ·
      refine ⟨12434589343542019465654987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16579452458056025954206649 12434589343542019465654987)
      ·
        refine ⟨18651884015313029198482481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12434589343542019465654987 18651884015313029198482481)
        ·
          refine ⟨13988913011484771898861861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18651884015313029198482481 13988913011484771898861861)
          ·
            refine ⟨2622921189653394731036599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13988913011484771898861861 2622921189653394731036599)
            ·
              refine ⟨3934381784480092096554899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2622921189653394731036599 3934381784480092096554899)
              ·
                refine ⟨5901572676720138144832349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3934381784480092096554899 5901572676720138144832349)
                ·
                  refine ⟨2213089753770051804312131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5901572676720138144832349 2213089753770051804312131)
                  ·
                    refine ⟨3319634630655077706468197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2213089753770051804312131 3319634630655077706468197)
                    ·
                      refine ⟨622431493247827069962787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3319634630655077706468197 622431493247827069962787)
                      ·
                        rfl

theorem cell23_1212181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_1212181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212181 prefixEnd_1212181 := by exact prefixLift 1212181
  have htrace : WordTrace (prefixWord ++ tailWord_1212181) baseStart_1212181 baseEnd_1212181 := by
    simpa [prefixWord, tailWord_1212181, baseEnd_1212181] using wordTrace_append hprefix tailTrace_1212181
  have hstable : (prefixWord ++ tailWord_1212181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212181).length < 2 ^ (prefixWord ++ tailWord_1212181).sum := by decide
  have hdescent : baseEnd_1212181 < baseStart_1212181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212184 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_1212184 : Nat := 118140960795 + 1212184 * 2 ^ 59
def prefixEnd_1212184 : Nat := 4983230072969 + 3 ^ 40 * 1212184 * 2
def baseEnd_1212184 : Nat := 622433033689790558225273

theorem tailTrace_1212184 : CollatzResearch.WordTrace tailWord_1212184 prefixEnd_1212184 622433033689790558225273 := by
  unfold tailWord_1212184
  simp only [CollatzResearch.WordTrace]
  refine ⟨22105991320235933695121803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29474655093647911593495737 22105991320235933695121803)
  ·
    refine ⟨33158986980353900542682705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22105991320235933695121803 33158986980353900542682705)
    ·
      refine ⟨24869240235265425407012029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33158986980353900542682705 24869240235265425407012029)
      ·
        refine ⟨9325965088224534527629511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24869240235265425407012029 9325965088224534527629511)
        ·
          refine ⟨13988947632336801791444267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9325965088224534527629511 13988947632336801791444267)
          ·
            refine ⟨20983421448505202687166401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13988947632336801791444267 20983421448505202687166401)
            ·
              refine ⟨15737566086378902015374801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20983421448505202687166401 15737566086378902015374801)
              ·
                refine ⟨11803174564784176511531101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15737566086378902015374801 11803174564784176511531101)
                ·
                  refine ⟨4426190461794066191824163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11803174564784176511531101 4426190461794066191824163)
                  ·
                    refine ⟨6639285692691099287736245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4426190461794066191824163 6639285692691099287736245)
                    ·
                      refine ⟨622433033689790558225273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6639285692691099287736245 622433033689790558225273)
                      ·
                        rfl

theorem cell23_1212184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_1212184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212184 prefixEnd_1212184 := by exact prefixLift 1212184
  have htrace : WordTrace (prefixWord ++ tailWord_1212184) baseStart_1212184 baseEnd_1212184 := by
    simpa [prefixWord, tailWord_1212184, baseEnd_1212184] using wordTrace_append hprefix tailTrace_1212184
  have hstable : (prefixWord ++ tailWord_1212184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212184).length < 2 ^ (prefixWord ++ tailWord_1212184).sum := by decide
  have hdescent : baseEnd_1212184 < baseStart_1212184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212221 : List Nat := [1, 4, 1, 4, 1, 1, 3, 8]
def baseStart_1212221 : Nat := 118140960795 + 1212221 * 2 ^ 59
def prefixEnd_1212221 : Nat := 4983230072969 + 3 ^ 40 * 1212221 * 2
def baseEnd_1212221 : Nat := 23053778980518774572689

theorem tailTrace_1212221 : CollatzResearch.WordTrace tailWord_1212221 prefixEnd_1212221 23053778980518774572689 := by
  unfold tailWord_1212221
  simp only [CollatzResearch.WordTrace]
  refine ⟨44213332141337822709340517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29475554760891881806227011 44213332141337822709340517)
  ·
    refine ⟨8289999776500841758001347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44213332141337822709340517 8289999776500841758001347)
    ·
      refine ⟨12434999664751262637002021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8289999776500841758001347 12434999664751262637002021)
      ·
        refine ⟨2331562437140861744437879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12434999664751262637002021 2331562437140861744437879)
        ·
          refine ⟨3497343655711292616656819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2331562437140861744437879 3497343655711292616656819)
          ·
            refine ⟨5246015483566938924985229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3497343655711292616656819 5246015483566938924985229)
            ·
              refine ⟨1967255806337602096869461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5246015483566938924985229 1967255806337602096869461)
              ·
                refine ⟨23053778980518774572689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1967255806337602096869461 23053778980518774572689)
                ·
                  rfl

theorem cell23_1212221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 8].length) (baseStart_1212221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212221 prefixEnd_1212221 := by exact prefixLift 1212221
  have htrace : WordTrace (prefixWord ++ tailWord_1212221) baseStart_1212221 baseEnd_1212221 := by
    simpa [prefixWord, tailWord_1212221, baseEnd_1212221] using wordTrace_append hprefix tailTrace_1212221
  have hstable : (prefixWord ++ tailWord_1212221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212221).length < 2 ^ (prefixWord ++ tailWord_1212221).sum := by decide
  have hdescent : baseEnd_1212221 < baseStart_1212221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212231 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_1212231 : Nat := 118140960795 + 1212231 * 2 ^ 59
def prefixEnd_1212231 : Nat := 4983230072969 + 3 ^ 40 * 1212231 * 2
def baseEnd_1212231 : Nat := 622457167280551874337557

theorem tailTrace_1212231 : CollatzResearch.WordTrace tailWord_1212231 prefixEnd_1212231 622457167280551874337557 := by
  unfold tailWord_1212231
  simp only [CollatzResearch.WordTrace]
  refine ⟨44213696871301594417204547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29475797914201062944803031 44213696871301594417204547)
  ·
    refine ⟨66320545306952391625806821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44213696871301594417204547 66320545306952391625806821)
    ·
      refine ⟨12435102245053573429838779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66320545306952391625806821 12435102245053573429838779)
      ·
        refine ⟨18652653367580360144758169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12435102245053573429838779 18652653367580360144758169)
        ·
          refine ⟨13989490025685270108568627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18652653367580360144758169 13989490025685270108568627)
          ·
            refine ⟨20984235038527905162852941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13989490025685270108568627 20984235038527905162852941)
            ·
              refine ⟨7869088139447964436069853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20984235038527905162852941 7869088139447964436069853)
              ·
                refine ⟨2950908052292986663526195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7869088139447964436069853 2950908052292986663526195)
                ·
                  refine ⟨4426362078439479995289293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2950908052292986663526195 4426362078439479995289293)
                  ·
                    refine ⟨1659885779414804998233485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4426362078439479995289293 1659885779414804998233485)
                    ·
                      refine ⟨622457167280551874337557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1659885779414804998233485 622457167280551874337557)
                      ·
                        rfl

theorem cell23_1212231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_1212231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212231 prefixEnd_1212231 := by exact prefixLift 1212231
  have htrace : WordTrace (prefixWord ++ tailWord_1212231) baseStart_1212231 baseEnd_1212231 := by
    simpa [prefixWord, tailWord_1212231, baseEnd_1212231] using wordTrace_append hprefix tailTrace_1212231
  have hstable : (prefixWord ++ tailWord_1212231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212231).length < 2 ^ (prefixWord ++ tailWord_1212231).sum := by decide
  have hdescent : baseEnd_1212231 < baseStart_1212231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212234 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 2, 7]
def baseStart_1212234 : Nat := 118140960795 + 1212234 * 2 ^ 59
def prefixEnd_1212234 : Nat := 4983230072969 + 3 ^ 40 * 1212234 * 2
def baseEnd_1212234 : Nat := 207486235907505120866681

theorem tailTrace_1212234 : CollatzResearch.WordTrace tailWord_1212234 prefixEnd_1212234 207486235907505120866681 := by
  unfold tailWord_1212234
  simp only [CollatzResearch.WordTrace]
  refine ⟨11053451572572681482390939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29475870860193817286375837 11053451572572681482390939)
  ·
    refine ⟨16580177358859022223586409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11053451572572681482390939 16580177358859022223586409)
    ·
      refine ⟨12435133019144266667689807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16580177358859022223586409 12435133019144266667689807)
      ·
        refine ⟨18652699528716400001534711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12435133019144266667689807 18652699528716400001534711)
        ·
          refine ⟨27979049293074600002302067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18652699528716400001534711 27979049293074600002302067)
          ·
            refine ⟨41968573939611900003453101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27979049293074600002302067 41968573939611900003453101)
            ·
              refine ⟨15738215227354462501294913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41968573939611900003453101 15738215227354462501294913)
              ·
                refine ⟨11803661420515846875971185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15738215227354462501294913 11803661420515846875971185)
                ·
                  refine ⟨8852746065386885156978389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11803661420515846875971185 8852746065386885156978389)
                  ·
                    refine ⟨207486235907505120866681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8852746065386885156978389 207486235907505120866681)
                    ·
                      rfl

theorem cell23_1212234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_1212234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212234 prefixEnd_1212234 := by exact prefixLift 1212234
  have htrace : WordTrace (prefixWord ++ tailWord_1212234) baseStart_1212234 baseEnd_1212234 := by
    simpa [prefixWord, tailWord_1212234, baseEnd_1212234] using wordTrace_append hprefix tailTrace_1212234
  have hstable : (prefixWord ++ tailWord_1212234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212234).length < 2 ^ (prefixWord ++ tailWord_1212234).sum := by decide
  have hdescent : baseEnd_1212234 < baseStart_1212234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212271 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 2, 8, 2]
def baseStart_1212271 : Nat := 118140960795 + 1212271 * 2 ^ 59
def prefixEnd_1212271 : Nat := 4983230072969 + 3 ^ 40 * 1212271 * 2
def baseEnd_1212271 : Nat := 622477706506731717837373

theorem tailTrace_1212271 : CollatzResearch.WordTrace tailWord_1212271 prefixEnd_1212271 622477706506731717837373 := by
  unfold tailWord_1212271
  simp only [CollatzResearch.WordTrace]
  refine ⟨44215155791156681248660667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29476770527437787499107111 44215155791156681248660667)
  ·
    refine ⟨66322733686735021872991001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44215155791156681248660667 66322733686735021872991001)
    ·
      refine ⟨49742050265051266404743251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66322733686735021872991001 49742050265051266404743251)
      ·
        refine ⟨74613075397576899607114877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49742050265051266404743251 74613075397576899607114877)
        ·
          refine ⟨27979903274091337352668079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74613075397576899607114877 27979903274091337352668079)
          ·
            refine ⟨41969854911137006029002119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27979903274091337352668079 41969854911137006029002119)
            ·
              refine ⟨62954782366705509043503179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41969854911137006029002119 62954782366705509043503179)
              ·
                refine ⟨94432173550058263565254769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62954782366705509043503179 94432173550058263565254769)
                ·
                  refine ⟨70824130162543697673941077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94432173550058263565254769 70824130162543697673941077)
                  ·
                    refine ⟨829970275342308957116497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70824130162543697673941077 829970275342308957116497)
                    ·
                      refine ⟨622477706506731717837373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 829970275342308957116497 622477706506731717837373)
                      ·
                        rfl

theorem cell23_1212271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 8, 2].length) (baseStart_1212271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212271 prefixEnd_1212271 := by exact prefixLift 1212271
  have htrace : WordTrace (prefixWord ++ tailWord_1212271) baseStart_1212271 baseEnd_1212271 := by
    simpa [prefixWord, tailWord_1212271, baseEnd_1212271] using wordTrace_append hprefix tailTrace_1212271
  have hstable : (prefixWord ++ tailWord_1212271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212271).length < 2 ^ (prefixWord ++ tailWord_1212271).sum := by decide
  have hdescent : baseEnd_1212271 < baseStart_1212271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212304 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 7]
def baseStart_1212304 : Nat := 118140960795 + 1212304 * 2 ^ 59
def prefixEnd_1212304 : Nat := 4983230072969 + 3 ^ 40 * 1212304 * 2
def baseEnd_1212304 : Nat := 622494651368330088724721

theorem tailTrace_1212304 : CollatzResearch.WordTrace tailWord_1212304 prefixEnd_1212304 622494651368330088724721 := by
  unfold tailWord_1212304
  simp only [CollatzResearch.WordTrace]
  refine ⟨22108179700018563942305983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29477572933358085256407977 22108179700018563942305983)
  ·
    refine ⟨33162269550027845913458975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22108179700018563942305983 33162269550027845913458975)
    ·
      refine ⟨49743404325041768870188463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33162269550027845913458975 49743404325041768870188463)
      ·
        refine ⟨74615106487562653305282695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49743404325041768870188463 74615106487562653305282695)
        ·
          refine ⟨111922659731343979957924043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74615106487562653305282695 111922659731343979957924043)
          ·
            refine ⟨167883989597015969936886065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111922659731343979957924043 167883989597015969936886065)
            ·
              refine ⟨125912992197761977452664549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167883989597015969936886065 125912992197761977452664549)
              ·
                refine ⟨23608686037080370772374603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125912992197761977452664549 23608686037080370772374603)
                ·
                  refine ⟨35413029055620556158561905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23608686037080370772374603 35413029055620556158561905)
                  ·
                    refine ⟨26559771791715417118921429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35413029055620556158561905 26559771791715417118921429)
                    ·
                      refine ⟨622494651368330088724721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26559771791715417118921429 622494651368330088724721)
                      ·
                        rfl

theorem cell23_1212304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_1212304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212304 prefixEnd_1212304 := by exact prefixLift 1212304
  have htrace : WordTrace (prefixWord ++ tailWord_1212304) baseStart_1212304 baseEnd_1212304 := by
    simpa [prefixWord, tailWord_1212304, baseEnd_1212304] using wordTrace_append hprefix tailTrace_1212304
  have hstable : (prefixWord ++ tailWord_1212304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212304).length < 2 ^ (prefixWord ++ tailWord_1212304).sum := by decide
  have hdescent : baseEnd_1212304 < baseStart_1212304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212308 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1212308 : Nat := 118140960795 + 1212308 * 2 ^ 59
def prefixEnd_1212308 : Nat := 4983230072969 + 3 ^ 40 * 1212308 * 2
def baseEnd_1212308 : Nat := 622496705290948073074703

theorem tailTrace_1212308 : CollatzResearch.WordTrace tailWord_1212308 prefixEnd_1212308 622496705290948073074703 := by
  unfold tailWord_1212308
  simp only [CollatzResearch.WordTrace]
  refine ⟨22108252646011318283878789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29477670194681757711838385 22108252646011318283878789)
  ·
    refine ⟨4145297371127122178227273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22108252646011318283878789 4145297371127122178227273)
    ·
      refine ⟨3108973028345341633670455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4145297371127122178227273 3108973028345341633670455)
      ·
        refine ⟨4663459542518012450505683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3108973028345341633670455 4663459542518012450505683)
        ·
          refine ⟨6995189313777018675758525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4663459542518012450505683 6995189313777018675758525)
          ·
            refine ⟨2623195992666382003409447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6995189313777018675758525 2623195992666382003409447)
            ·
              refine ⟨3934793988999573005114171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2623195992666382003409447 3934793988999573005114171)
              ·
                refine ⟨5902190983499359507671257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3934793988999573005114171 5902190983499359507671257)
                ·
                  refine ⟨4426643237624519630753443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5902190983499359507671257 4426643237624519630753443)
                  ·
                    refine ⟨6639964856436779446130165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4426643237624519630753443 6639964856436779446130165)
                    ·
                      refine ⟨622496705290948073074703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6639964856436779446130165 622496705290948073074703)
                      ·
                        rfl

theorem cell23_1212308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1212308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212308 prefixEnd_1212308 := by exact prefixLift 1212308
  have htrace : WordTrace (prefixWord ++ tailWord_1212308) baseStart_1212308 baseEnd_1212308 := by
    simpa [prefixWord, tailWord_1212308, baseEnd_1212308] using wordTrace_append hprefix tailTrace_1212308
  have hstable : (prefixWord ++ tailWord_1212308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212308).length < 2 ^ (prefixWord ++ tailWord_1212308).sum := by decide
  have hdescent : baseEnd_1212308 < baseStart_1212308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212361 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 6, 1, 4]
def baseStart_1212361 : Nat := 118140960795 + 1212361 * 2 ^ 59
def prefixEnd_1212361 : Nat := 4983230072969 + 3 ^ 40 * 1212361 * 2
def baseEnd_1212361 : Nat := 622523919765636365711959

theorem tailTrace_1212361 : CollatzResearch.WordTrace tailWord_1212361 prefixEnd_1212361 622523919765636365711959 := by
  unfold tailWord_1212361
  simp only [CollatzResearch.WordTrace]
  refine ⟨44218438360830626619436937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29478958907220417746291291 44218438360830626619436937)
  ·
    refine ⟨33163828770622969964577703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44218438360830626619436937 33163828770622969964577703)
    ·
      refine ⟨49745743155934454946866555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33163828770622969964577703 49745743155934454946866555)
      ·
        refine ⟨74618614733901682420299833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49745743155934454946866555 74618614733901682420299833)
        ·
          refine ⟨55963961050426261815224875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74618614733901682420299833 55963961050426261815224875)
          ·
            refine ⟨83945941575639392722837313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55963961050426261815224875 83945941575639392722837313)
            ·
              refine ⟨62959456181729544542127985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83945941575639392722837313 62959456181729544542127985)
              ·
                refine ⟨47219592136297158406595989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62959456181729544542127985 47219592136297158406595989)
                ·
                  refine ⟨2213418381388929300309187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47219592136297158406595989 2213418381388929300309187)
                  ·
                    refine ⟨3320127572083393950463781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2213418381388929300309187 3320127572083393950463781)
                    ·
                      refine ⟨622523919765636365711959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3320127572083393950463781 622523919765636365711959)
                      ·
                        rfl

theorem cell23_1212361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_1212361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212361 prefixEnd_1212361 := by exact prefixLift 1212361
  have htrace : WordTrace (prefixWord ++ tailWord_1212361) baseStart_1212361 baseEnd_1212361 := by
    simpa [prefixWord, tailWord_1212361, baseEnd_1212361] using wordTrace_append hprefix tailTrace_1212361
  have hstable : (prefixWord ++ tailWord_1212361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212361).length < 2 ^ (prefixWord ++ tailWord_1212361).sum := by decide
  have hdescent : baseEnd_1212361 < baseStart_1212361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212388 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_1212388 : Nat := 118140960795 + 1212388 * 2 ^ 59
def prefixEnd_1212388 : Nat := 4983230072969 + 3 ^ 40 * 1212388 * 2
def baseEnd_1212388 : Nat := 207512594581102586691445

theorem tailTrace_1212388 : CollatzResearch.WordTrace tailWord_1212388 prefixEnd_1212388 207512594581102586691445 := by
  unfold tailWord_1212388
  simp only [CollatzResearch.WordTrace]
  refine ⟨22109711565866405115334909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29479615421155206820446545 22109711565866405115334909)
  ·
    refine ⟨8291141837199901918250591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22109711565866405115334909 8291141837199901918250591)
    ·
      refine ⟨12436712755799852877375887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8291141837199901918250591 12436712755799852877375887)
      ·
        refine ⟨18655069133699779316063831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12436712755799852877375887 18655069133699779316063831)
        ·
          refine ⟨27982603700549668974095747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18655069133699779316063831 27982603700549668974095747)
          ·
            refine ⟨41973905550824503461143621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27982603700549668974095747 41973905550824503461143621)
            ·
              refine ⟨7870107290779594398964429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41973905550824503461143621 7870107290779594398964429)
              ·
                refine ⟨2951290234042347899611661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7870107290779594398964429 2951290234042347899611661)
                ·
                  refine ⟨1106733837765880462354373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2951290234042347899611661 1106733837765880462354373)
                  ·
                    refine ⟨207512594581102586691445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1106733837765880462354373 207512594581102586691445)
                    ·
                      rfl

theorem cell23_1212388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_1212388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212388 prefixEnd_1212388 := by exact prefixLift 1212388
  have htrace : WordTrace (prefixWord ++ tailWord_1212388) baseStart_1212388 baseEnd_1212388 := by
    simpa [prefixWord, tailWord_1212388, baseEnd_1212388] using wordTrace_append hprefix tailTrace_1212388
  have hstable : (prefixWord ++ tailWord_1212388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212388).length < 2 ^ (prefixWord ++ tailWord_1212388).sum := by decide
  have hdescent : baseEnd_1212388 < baseStart_1212388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212452 : List Nat := [2, 3, 1, 4, 2, 1, 3, 1, 6]
def baseStart_1212452 : Nat := 118140960795 + 1212452 * 2 ^ 59
def prefixEnd_1212452 : Nat := 4983230072969 + 3 ^ 40 * 1212452 * 2
def baseEnd_1212452 : Nat := 69174516278355056630449

theorem tailTrace_1212452 : CollatzResearch.WordTrace tailWord_1212452 prefixEnd_1212452 69174516278355056630449 := by
  unfold tailWord_1212452
  simp only [CollatzResearch.WordTrace]
  refine ⟨22110878701750474580499805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29481171602333966107333073 22110878701750474580499805)
  ·
    refine ⟨8291579513156427967687427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22110878701750474580499805 8291579513156427967687427)
    ·
      refine ⟨12437369269734641951531141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8291579513156427967687427 12437369269734641951531141)
      ·
        refine ⟨2332006738075245365912089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12437369269734641951531141 2332006738075245365912089)
        ·
          refine ⟨1749005053556434024434067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2332006738075245365912089 1749005053556434024434067)
          ·
            refine ⟨2623507580334651036651101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1749005053556434024434067 2623507580334651036651101)
            ·
              refine ⟨983815342625494138744163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2623507580334651036651101 983815342625494138744163)
              ·
                refine ⟨1475723013938241208116245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983815342625494138744163 1475723013938241208116245)
                ·
                  refine ⟨69174516278355056630449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1475723013938241208116245 69174516278355056630449)
                  ·
                    rfl

theorem cell23_1212452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_1212452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212452 prefixEnd_1212452 := by exact prefixLift 1212452
  have htrace : WordTrace (prefixWord ++ tailWord_1212452) baseStart_1212452 baseEnd_1212452 := by
    simpa [prefixWord, tailWord_1212452, baseEnd_1212452] using wordTrace_append hprefix tailTrace_1212452
  have hstable : (prefixWord ++ tailWord_1212452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212452).length < 2 ^ (prefixWord ++ tailWord_1212452).sum := by decide
  have hdescent : baseEnd_1212452 < baseStart_1212452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212462 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_1212462 : Nat := 118140960795 + 1212462 * 2 ^ 59
def prefixEnd_1212462 : Nat := 4983230072969 + 3 ^ 40 * 1212462 * 2
def baseEnd_1212462 : Nat := 622575781311740470548995

theorem tailTrace_1212462 : CollatzResearch.WordTrace tailWord_1212462 prefixEnd_1212462 622575781311740470548995 := by
  unfold tailWord_1212462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5527765266683090108607955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29481414755643147245909093 5527765266683090108607955)
  ·
    refine ⟨8291647900024635162911933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5527765266683090108607955 8291647900024635162911933)
    ·
      refine ⟨3109367962509238186091975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8291647900024635162911933 3109367962509238186091975)
      ·
        refine ⟨4664051943763857279137963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3109367962509238186091975 4664051943763857279137963)
        ·
          refine ⟨6996077915645785918706945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664051943763857279137963 6996077915645785918706945)
          ·
            refine ⟨5247058436734339439030209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6996077915645785918706945 5247058436734339439030209)
            ·
              refine ⟨3935293827550754579272657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5247058436734339439030209 3935293827550754579272657)
              ·
                refine ⟨2951470370663065934454493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3935293827550754579272657 2951470370663065934454493)
                ·
                  refine ⟨1106801388998649725420435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2951470370663065934454493 1106801388998649725420435)
                  ·
                    refine ⟨1660202083497974588130653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1106801388998649725420435 1660202083497974588130653)
                    ·
                      refine ⟨622575781311740470548995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1660202083497974588130653 622575781311740470548995)
                      ·
                        rfl

theorem cell23_1212462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_1212462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212462 prefixEnd_1212462 := by exact prefixLift 1212462
  have htrace : WordTrace (prefixWord ++ tailWord_1212462) baseStart_1212462 baseEnd_1212462 := by
    simpa [prefixWord, tailWord_1212462, baseEnd_1212462] using wordTrace_append hprefix tailTrace_1212462
  have hstable : (prefixWord ++ tailWord_1212462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212462).length < 2 ^ (prefixWord ++ tailWord_1212462).sum := by decide
  have hdescent : baseEnd_1212462 < baseStart_1212462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212465 : List Nat := [1, 2, 2, 3, 1, 4, 2, 2, 1, 5]
def baseStart_1212465 : Nat := 118140960795 + 1212465 * 2 ^ 59
def prefixEnd_1212465 : Nat := 4983230072969 + 3 ^ 40 * 1212465 * 2
def baseEnd_1212465 : Nat := 207525773917901319603827

theorem tailTrace_1212465 : CollatzResearch.WordTrace tailWord_1212465 prefixEnd_1212465 207525773917901319603827 := by
  unfold tailWord_1212465
  simp only [CollatzResearch.WordTrace]
  refine ⟨44222231552453852381222849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29481487701635901587481899 44222231552453852381222849)
  ·
    refine ⟨33166673664340389285917137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44222231552453852381222849 33166673664340389285917137)
    ·
      refine ⟨24875005248255291964437853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33166673664340389285917137 24875005248255291964437853)
      ·
        refine ⟨9328126968095734486664195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24875005248255291964437853 9328126968095734486664195)
        ·
          refine ⟨13992190452143601729996293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9328126968095734486664195 13992190452143601729996293)
          ·
            refine ⟨2623535709776925324374305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13992190452143601729996293 2623535709776925324374305)
            ·
              refine ⟨1967651782332693993280729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2623535709776925324374305 1967651782332693993280729)
              ·
                refine ⟨1475738836749520494960547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1967651782332693993280729 1475738836749520494960547)
                ·
                  refine ⟨2213608255124280742440821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1475738836749520494960547 2213608255124280742440821)
                  ·
                    refine ⟨207525773917901319603827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2213608255124280742440821 207525773917901319603827)
                    ·
                      rfl

theorem cell23_1212465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_1212465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212465 prefixEnd_1212465 := by exact prefixLift 1212465
  have htrace : WordTrace (prefixWord ++ tailWord_1212465) baseStart_1212465 baseEnd_1212465 := by
    simpa [prefixWord, tailWord_1212465, baseEnd_1212465] using wordTrace_append hprefix tailTrace_1212465
  have hstable : (prefixWord ++ tailWord_1212465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212465).length < 2 ^ (prefixWord ++ tailWord_1212465).sum := by decide
  have hdescent : baseEnd_1212465 < baseStart_1212465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212508 : List Nat := [2, 2, 4, 1, 1, 2, 1, 10]
def baseStart_1212508 : Nat := 118140960795 + 1212508 * 2 ^ 59
def prefixEnd_1212508 : Nat := 4983230072969 + 3 ^ 40 * 1212508 * 2
def baseEnd_1212508 : Nat := 23059237089698047799029

theorem tailTrace_1212508 : CollatzResearch.WordTrace tailWord_1212508 prefixEnd_1212508 23059237089698047799029 := by
  unfold tailWord_1212508
  simp only [CollatzResearch.WordTrace]
  refine ⟨22111899945649035362519089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29482533260865380483358785 22111899945649035362519089)
  ·
    refine ⟨16583924959236776521889317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22111899945649035362519089 16583924959236776521889317)
    ·
      refine ⟨3109485929856895597854247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16583924959236776521889317 3109485929856895597854247)
      ·
        refine ⟨4664228894785343396781371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3109485929856895597854247 4664228894785343396781371)
        ·
          refine ⟨6996343342178015095172057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664228894785343396781371 6996343342178015095172057)
          ·
            refine ⟨5247257506633511321379043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6996343342178015095172057 5247257506633511321379043)
            ·
              refine ⟨7870886259950266982068565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5247257506633511321379043 7870886259950266982068565)
              ·
                refine ⟨23059237089698047799029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7870886259950266982068565 23059237089698047799029)
                ·
                  rfl

theorem cell23_1212508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 10].length) (baseStart_1212508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212508 prefixEnd_1212508 := by exact prefixLift 1212508
  have htrace : WordTrace (prefixWord ++ tailWord_1212508) baseStart_1212508 baseEnd_1212508 := by
    simpa [prefixWord, tailWord_1212508, baseEnd_1212508] using wordTrace_append hprefix tailTrace_1212508
  have hstable : (prefixWord ++ tailWord_1212508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212508).length < 2 ^ (prefixWord ++ tailWord_1212508).sum := by decide
  have hdescent : baseEnd_1212508 < baseStart_1212508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212512 : List Nat := [2, 1, 1, 3, 2, 3, 4, 1, 2, 4]
def baseStart_1212512 : Nat := 118140960795 + 1212512 * 2 ^ 59
def prefixEnd_1212512 : Nat := 4983230072969 + 3 ^ 40 * 1212512 * 2
def baseEnd_1212512 : Nat := 207533818448155091641255

theorem tailTrace_1212512 : CollatzResearch.WordTrace tailWord_1212512 prefixEnd_1212512 207533818448155091641255 := by
  unfold tailWord_1212512
  simp only [CollatzResearch.WordTrace]
  refine ⟨22111972891641789704091895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29482630522189052938789193 22111972891641789704091895)
  ·
    refine ⟨33167959337462684556137843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22111972891641789704091895 33167959337462684556137843)
    ·
      refine ⟨49751939006194026834206765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33167959337462684556137843 49751939006194026834206765)
      ·
        refine ⟨18656977127322760062827537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49751939006194026834206765 18656977127322760062827537)
        ·
          refine ⟨13992732845492070047120653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18656977127322760062827537 13992732845492070047120653)
          ·
            refine ⟨5247274817059526267670245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13992732845492070047120653 5247274817059526267670245)
            ·
              refine ⟨983864028198661175188171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5247274817059526267670245 983864028198661175188171)
              ·
                refine ⟨1475796042297991762782257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983864028198661175188171 1475796042297991762782257)
                ·
                  refine ⟨1106847031723493822086693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1475796042297991762782257 1106847031723493822086693)
                  ·
                    refine ⟨207533818448155091641255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1106847031723493822086693 207533818448155091641255)
                    ·
                      rfl

theorem cell23_1212512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 2, 4].length) (baseStart_1212512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212512 prefixEnd_1212512 := by exact prefixLift 1212512
  have htrace : WordTrace (prefixWord ++ tailWord_1212512) baseStart_1212512 baseEnd_1212512 := by
    simpa [prefixWord, tailWord_1212512, baseEnd_1212512] using wordTrace_append hprefix tailTrace_1212512
  have hstable : (prefixWord ++ tailWord_1212512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212512).length < 2 ^ (prefixWord ++ tailWord_1212512).sum := by decide
  have hdescent : baseEnd_1212512 < baseStart_1212512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212522 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_1212522 : Nat := 118140960795 + 1212522 * 2 ^ 59
def prefixEnd_1212522 : Nat := 4983230072969 + 3 ^ 40 * 1212522 * 2
def baseEnd_1212522 : Nat := 622606590151010235798719

theorem tailTrace_1212522 : CollatzResearch.WordTrace tailWord_1212522 prefixEnd_1212522 622606590151010235798719 := by
  unfold tailWord_1212522
  simp only [CollatzResearch.WordTrace]
  refine ⟨11056077628311837779011955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29482873675498234077365213 11056077628311837779011955)
  ·
    refine ⟨16584116442467756668517933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11056077628311837779011955 16584116442467756668517933)
    ·
      refine ⟨6219043665925408750694225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16584116442467756668517933 6219043665925408750694225)
      ·
        refine ⟨4664282749444056563020669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6219043665925408750694225 4664282749444056563020669)
        ·
          refine ⟨1749106031041521211132751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4664282749444056563020669 1749106031041521211132751)
          ·
            refine ⟨2623659046562281816699127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1749106031041521211132751 2623659046562281816699127)
            ·
              refine ⟨3935488569843422725048691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2623659046562281816699127 3935488569843422725048691)
              ·
                refine ⟨5903232854765134087573037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3935488569843422725048691 5903232854765134087573037)
                ·
                  refine ⟨2213712320536925282839889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5903232854765134087573037 2213712320536925282839889)
                  ·
                    refine ⟨1660284240402693962129917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2213712320536925282839889 1660284240402693962129917)
                    ·
                      refine ⟨622606590151010235798719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1660284240402693962129917 622606590151010235798719)
                      ·
                        rfl

theorem cell23_1212522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_1212522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212522 prefixEnd_1212522 := by exact prefixLift 1212522
  have htrace : WordTrace (prefixWord ++ tailWord_1212522) baseStart_1212522 baseEnd_1212522 := by
    simpa [prefixWord, tailWord_1212522, baseEnd_1212522] using wordTrace_append hprefix tailTrace_1212522
  have hstable : (prefixWord ++ tailWord_1212522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212522).length < 2 ^ (prefixWord ++ tailWord_1212522).sum := by decide
  have hdescent : baseEnd_1212522 < baseStart_1212522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212535 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 3]
def baseStart_1212535 : Nat := 118140960795 + 1212535 * 2 ^ 59
def prefixEnd_1212535 : Nat := 4983230072969 + 3 ^ 40 * 1212535 * 2
def baseEnd_1212535 : Nat := 622613265399518684936159

theorem tailTrace_1212535 : CollatzResearch.WordTrace tailWord_1212535 prefixEnd_1212535 622613265399518684936159 := by
  unfold tailWord_1212535
  simp only [CollatzResearch.WordTrace]
  refine ⟨44224784662200254336271059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29483189774800169557514039 44224784662200254336271059)
  ·
    refine ⟨66337176993300381504406589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44224784662200254336271059 66337176993300381504406589)
    ·
      refine ⟨24876441372487643064152471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66337176993300381504406589 24876441372487643064152471)
      ·
        refine ⟨37314662058731464596228707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24876441372487643064152471 37314662058731464596228707)
        ·
          refine ⟨55971993088097196894343061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37314662058731464596228707 55971993088097196894343061)
          ·
            refine ⟨2623687176004556104422331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55971993088097196894343061 2623687176004556104422331)
            ·
              refine ⟨3935530764006834156633497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2623687176004556104422331 3935530764006834156633497)
              ·
                refine ⟨2951648073005125617475123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3935530764006834156633497 2951648073005125617475123)
                ·
                  refine ⟨4427472109507688426212685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2951648073005125617475123 4427472109507688426212685)
                  ·
                    refine ⟨1660302041065383159829757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4427472109507688426212685 1660302041065383159829757)
                    ·
                      refine ⟨622613265399518684936159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1660302041065383159829757 622613265399518684936159)
                      ·
                        rfl

theorem cell23_1212535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_1212535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212535 prefixEnd_1212535 := by exact prefixLift 1212535
  have htrace : WordTrace (prefixWord ++ tailWord_1212535) baseStart_1212535 baseEnd_1212535 := by
    simpa [prefixWord, tailWord_1212535, baseEnd_1212535] using wordTrace_append hprefix tailTrace_1212535
  have hstable : (prefixWord ++ tailWord_1212535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212535).length < 2 ^ (prefixWord ++ tailWord_1212535).sum := by decide
  have hdescent : baseEnd_1212535 < baseStart_1212535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212562 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_1212562 : Nat := 118140960795 + 1212562 * 2 ^ 59
def prefixEnd_1212562 : Nat := 4983230072969 + 3 ^ 40 * 1212562 * 2
def baseEnd_1212562 : Nat := 622627129377190079298535

theorem tailTrace_1212562 : CollatzResearch.WordTrace tailWord_1212562 prefixEnd_1212562 622627129377190079298535 := by
  unfold tailWord_1212562
  simp only [CollatzResearch.WordTrace]
  refine ⟨11056442358275609486875985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29483846288734958631669293 11056442358275609486875985)
  ·
    refine ⟨8292331768706707115156989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11056442358275609486875985 8292331768706707115156989)
    ·
      refine ⟨3109624413265015168183871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8292331768706707115156989 3109624413265015168183871)
      ·
        refine ⟨4664436619897522752275807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3109624413265015168183871 4664436619897522752275807)
        ·
          refine ⟨6996654929846284128413711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664436619897522752275807 6996654929846284128413711)
          ·
            refine ⟨10494982394769426192620567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6996654929846284128413711 10494982394769426192620567)
            ·
              refine ⟨15742473592154139288930851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10494982394769426192620567 15742473592154139288930851)
              ·
                refine ⟨23613710388231208933396277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15742473592154139288930851 23613710388231208933396277)
                ·
                  refine ⟨2213785348896675837505901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23613710388231208933396277 2213785348896675837505901)
                  ·
                    refine ⟨830169505836253439064713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2213785348896675837505901 830169505836253439064713)
                    ·
                      refine ⟨622627129377190079298535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 830169505836253439064713 622627129377190079298535)
                      ·
                        rfl

theorem cell23_1212562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_1212562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212562 prefixEnd_1212562 := by exact prefixLift 1212562
  have htrace : WordTrace (prefixWord ++ tailWord_1212562) baseStart_1212562 baseEnd_1212562 := by
    simpa [prefixWord, tailWord_1212562, baseEnd_1212562] using wordTrace_append hprefix tailTrace_1212562
  have hstable : (prefixWord ++ tailWord_1212562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212562).length < 2 ^ (prefixWord ++ tailWord_1212562).sum := by decide
  have hdescent : baseEnd_1212562 < baseStart_1212562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212590 : List Nat := [4, 1, 4, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_1212590 : Nat := 118140960795 + 1212590 * 2 ^ 59
def prefixEnd_1212590 : Nat := 4983230072969 + 3 ^ 40 * 1212590 * 2
def baseEnd_1212590 : Nat := 622641506835515969748407

theorem tailTrace_1212590 : CollatzResearch.WordTrace tailWord_1212590 prefixEnd_1212590 622641506835515969748407 := by
  unfold tailWord_1212590
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528348834625124841190403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29484527118000665819682149 5528348834625124841190403)
  ·
    refine ⟨8292523251937687261785605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5528348834625124841190403 8292523251937687261785605)
    ·
      refine ⟨1554848109738316361584801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8292523251937687261785605 1554848109738316361584801)
      ·
        refine ⟨1166136082303737271188601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1554848109738316361584801 1166136082303737271188601)
        ·
          refine ⟨874602061727802953391451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1166136082303737271188601 874602061727802953391451)
          ·
            refine ⟨1311903092591704430087177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874602061727802953391451 1311903092591704430087177)
            ·
              refine ⟨983927319443778322565383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1311903092591704430087177 983927319443778322565383)
              ·
                refine ⟨1475890979165667483848075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983927319443778322565383 1475890979165667483848075)
                ·
                  refine ⟨2213836468748501225772113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1475890979165667483848075 2213836468748501225772113)
                  ·
                    refine ⟨1660377351561375919329085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2213836468748501225772113 1660377351561375919329085)
                    ·
                      refine ⟨622641506835515969748407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1660377351561375919329085 622641506835515969748407)
                      ·
                        rfl

theorem cell23_1212590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_1212590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212590 prefixEnd_1212590 := by exact prefixLift 1212590
  have htrace : WordTrace (prefixWord ++ tailWord_1212590) baseStart_1212590 baseEnd_1212590 := by
    simpa [prefixWord, tailWord_1212590, baseEnd_1212590] using wordTrace_append hprefix tailTrace_1212590
  have hstable : (prefixWord ++ tailWord_1212590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212590).length < 2 ^ (prefixWord ++ tailWord_1212590).sum := by decide
  have hdescent : baseEnd_1212590 < baseStart_1212590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212625 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 2, 3, 3]
def baseStart_1212625 : Nat := 118140960795 + 1212625 * 2 ^ 59
def prefixEnd_1212625 : Nat := 4983230072969 + 3 ^ 40 * 1212625 * 2
def baseEnd_1212625 : Nat := 622659478658423332810745

theorem tailTrace_1212625 : CollatzResearch.WordTrace tailWord_1212625 prefixEnd_1212625 622659478658423332810745 := by
  unfold tailWord_1212625
  simp only [CollatzResearch.WordTrace]
  refine ⟨44228067231874199707047329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29485378154582799804698219 44228067231874199707047329)
  ·
    refine ⟨33171050423905649780285497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44228067231874199707047329 33171050423905649780285497)
    ·
      refine ⟨24878287817929237335214123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33171050423905649780285497 24878287817929237335214123)
      ·
        refine ⟨37317431726893856002821185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24878287817929237335214123 37317431726893856002821185)
        ·
          refine ⟨27988073795170392002115889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37317431726893856002821185 27988073795170392002115889)
          ·
            refine ⟨20991055346377794001586917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27988073795170392002115889 20991055346377794001586917)
            ·
              refine ⟨3935822877445836375297547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20991055346377794001586917 3935822877445836375297547)
              ·
                refine ⟨5903734316168754562946321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3935822877445836375297547 5903734316168754562946321)
                ·
                  refine ⟨4427800737126565922209741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5903734316168754562946321 4427800737126565922209741)
                  ·
                    refine ⟨1660425276422462220828653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4427800737126565922209741 1660425276422462220828653)
                    ·
                      refine ⟨622659478658423332810745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1660425276422462220828653 622659478658423332810745)
                      ·
                        rfl

theorem cell23_1212625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_1212625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212625 prefixEnd_1212625 := by exact prefixLift 1212625
  have htrace : WordTrace (prefixWord ++ tailWord_1212625) baseStart_1212625 baseEnd_1212625 := by
    simpa [prefixWord, tailWord_1212625, baseEnd_1212625] using wordTrace_append hprefix tailTrace_1212625
  have hstable : (prefixWord ++ tailWord_1212625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212625).length < 2 ^ (prefixWord ++ tailWord_1212625).sum := by decide
  have hdescent : baseEnd_1212625 < baseStart_1212625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212635 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 4, 5, 2]
def baseStart_1212635 : Nat := 118140960795 + 1212635 * 2 ^ 59
def prefixEnd_1212635 : Nat := 4983230072969 + 3 ^ 40 * 1212635 * 2
def baseEnd_1212635 : Nat := 622664613464968293685699

theorem tailTrace_1212635 : CollatzResearch.WordTrace tailWord_1212635 prefixEnd_1212635 622664613464968293685699 := by
  unfold tailWord_1212635
  simp only [CollatzResearch.WordTrace]
  refine ⟨44228431961837971414911359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29485621307891980943274239 44228431961837971414911359)
  ·
    refine ⟨66342647942756957122367039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44228431961837971414911359 66342647942756957122367039)
    ·
      refine ⟨99513971914135435683550559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66342647942756957122367039 99513971914135435683550559)
      ·
        refine ⟨149270957871203153525325839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99513971914135435683550559 149270957871203153525325839)
        ·
          refine ⟨223906436806804730287988759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149270957871203153525325839 223906436806804730287988759)
          ·
            refine ⟨335859655210207095431983139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223906436806804730287988759 335859655210207095431983139)
            ·
              refine ⟨503789482815310643147974709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335859655210207095431983139 503789482815310643147974709)
              ·
                refine ⟨47230264013935372795122629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 503789482815310643147974709 47230264013935372795122629)
                ·
                  refine ⟨8855674502612882399085493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47230264013935372795122629 8855674502612882399085493)
                  ·
                    refine ⟨830219484619957724914265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8855674502612882399085493 830219484619957724914265)
                    ·
                      refine ⟨622664613464968293685699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 830219484619957724914265 622664613464968293685699)
                      ·
                        rfl

theorem cell23_1212635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 5, 2].length) (baseStart_1212635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212635 prefixEnd_1212635 := by exact prefixLift 1212635
  have htrace : WordTrace (prefixWord ++ tailWord_1212635) baseStart_1212635 baseEnd_1212635 := by
    simpa [prefixWord, tailWord_1212635, baseEnd_1212635] using wordTrace_append hprefix tailTrace_1212635
  have hstable : (prefixWord ++ tailWord_1212635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212635).length < 2 ^ (prefixWord ++ tailWord_1212635).sum := by decide
  have hdescent : baseEnd_1212635 < baseStart_1212635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212645 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 1, 7]
def baseStart_1212645 : Nat := 118140960795 + 1212645 * 2 ^ 59
def prefixEnd_1212645 : Nat := 4983230072969 + 3 ^ 40 * 1212645 * 2
def baseEnd_1212645 : Nat := 207556582757171084853551

theorem tailTrace_1212645 : CollatzResearch.WordTrace tailWord_1212645 prefixEnd_1212645 207556582757171084853551 := by
  unfold tailWord_1212645
  simp only [CollatzResearch.WordTrace]
  refine ⟨44228796691801743122775389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29485864461201162081850259 44228796691801743122775389)
  ·
    refine ⟨16585798759425653671040771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44228796691801743122775389 16585798759425653671040771)
    ·
      refine ⟨24878698139138480506561157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16585798759425653671040771 24878698139138480506561157)
      ·
        refine ⟨4664755901088465094980217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24878698139138480506561157 4664755901088465094980217)
        ·
          refine ⟨3498566925816348821235163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4664755901088465094980217 3498566925816348821235163)
          ·
            refine ⟨5247850388724523231852745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3498566925816348821235163 5247850388724523231852745)
            ·
              refine ⟨3935887791543392423889559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5247850388724523231852745 3935887791543392423889559)
              ·
                refine ⟨5903831687315088635834339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3935887791543392423889559 5903831687315088635834339)
                ·
                  refine ⟨8855747530972632953751509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5903831687315088635834339 8855747530972632953751509)
                  ·
                    refine ⟨207556582757171084853551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8855747530972632953751509 207556582757171084853551)
                    ·
                      rfl

theorem cell23_1212645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_1212645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212645 prefixEnd_1212645 := by exact prefixLift 1212645
  have htrace : WordTrace (prefixWord ++ tailWord_1212645) baseStart_1212645 baseEnd_1212645 := by
    simpa [prefixWord, tailWord_1212645, baseEnd_1212645] using wordTrace_append hprefix tailTrace_1212645
  have hstable : (prefixWord ++ tailWord_1212645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212645).length < 2 ^ (prefixWord ++ tailWord_1212645).sum := by decide
  have hdescent : baseEnd_1212645 < baseStart_1212645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212682 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2]
def baseStart_1212682 : Nat := 118140960795 + 1212682 * 2 ^ 59
def prefixEnd_1212682 : Nat := 4983230072969 + 3 ^ 40 * 1212682 * 2
def baseEnd_1212682 : Nat := 622688747055729609797983

theorem tailTrace_1212682 : CollatzResearch.WordTrace tailWord_1212682 prefixEnd_1212682 622688747055729609797983 := by
  unfold tailWord_1212682
  simp only [CollatzResearch.WordTrace]
  refine ⟨11057536548166924610468075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29486764128445132294581533 11057536548166924610468075)
  ·
    refine ⟨16586304822250386915702113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11057536548166924610468075 16586304822250386915702113)
    ·
      refine ⟨12439728616687790186776585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16586304822250386915702113 12439728616687790186776585)
      ·
        refine ⟨9329796462515842640082439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12439728616687790186776585 9329796462515842640082439)
        ·
          refine ⟨13994694693773763960123659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9329796462515842640082439 13994694693773763960123659)
          ·
            refine ⟨20992042040660645940185489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13994694693773763960123659 20992042040660645940185489)
            ·
              refine ⟨15744031530495484455139117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20992042040660645940185489 15744031530495484455139117)
              ·
                refine ⟨5904011823935806670677169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15744031530495484455139117 5904011823935806670677169)
                ·
                  refine ⟨4428008867951855003007877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5904011823935806670677169 4428008867951855003007877)
                  ·
                    refine ⟨830251662740972813063977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4428008867951855003007877 830251662740972813063977)
                    ·
                      refine ⟨622688747055729609797983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 830251662740972813063977 622688747055729609797983)
                      ·
                        rfl

theorem cell23_1212682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_1212682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212682 prefixEnd_1212682 := by exact prefixLift 1212682
  have htrace : WordTrace (prefixWord ++ tailWord_1212682) baseStart_1212682 baseEnd_1212682 := by
    simpa [prefixWord, tailWord_1212682, baseEnd_1212682] using wordTrace_append hprefix tailTrace_1212682
  have hstable : (prefixWord ++ tailWord_1212682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212682).length < 2 ^ (prefixWord ++ tailWord_1212682).sum := by decide
  have hdescent : baseEnd_1212682 < baseStart_1212682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212725 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_1212725 : Nat := 118140960795 + 1212725 * 2 ^ 59
def prefixEnd_1212725 : Nat := 4983230072969 + 3 ^ 40 * 1212725 * 2
def baseEnd_1212725 : Nat := 622710826723872941560285

theorem tailTrace_1212725 : CollatzResearch.WordTrace tailWord_1212725 prefixEnd_1212725 622710826723872941560285 := by
  unfold tailWord_1212725
  simp only [CollatzResearch.WordTrace]
  refine ⟨44231714531511916785687629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29487809687674611190458419 44231714531511916785687629)
  ·
    refine ⟨16586892949316968794632861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44231714531511916785687629 16586892949316968794632861)
    ·
      refine ⟨6220084855993863297987323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16586892949316968794632861 6220084855993863297987323)
      ·
        refine ⟨9330127283990794946980985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6220084855993863297987323 9330127283990794946980985)
        ·
          refine ⟨6997595462993096210235739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9330127283990794946980985 6997595462993096210235739)
          ·
            refine ⟨10496393194489644315353609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6997595462993096210235739 10496393194489644315353609)
            ·
              refine ⟨7872294895867233236515207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10496393194489644315353609 7872294895867233236515207)
              ·
                refine ⟨11808442343800849854772811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7872294895867233236515207 11808442343800849854772811)
                ·
                  refine ⟨17712663515701274782159217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11808442343800849854772811 17712663515701274782159217)
                  ·
                    refine ⟨13284497636775956086619413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17712663515701274782159217 13284497636775956086619413)
                    ·
                      refine ⟨622710826723872941560285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13284497636775956086619413 622710826723872941560285)
                      ·
                        rfl

theorem cell23_1212725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_1212725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212725 prefixEnd_1212725 := by exact prefixLift 1212725
  have htrace : WordTrace (prefixWord ++ tailWord_1212725) baseStart_1212725 baseEnd_1212725 := by
    simpa [prefixWord, tailWord_1212725, baseEnd_1212725] using wordTrace_append hprefix tailTrace_1212725
  have hstable : (prefixWord ++ tailWord_1212725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212725).length < 2 ^ (prefixWord ++ tailWord_1212725).sum := by decide
  have hdescent : baseEnd_1212725 < baseStart_1212725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212735 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 5, 5]
def baseStart_1212735 : Nat := 118140960795 + 1212735 * 2 ^ 59
def prefixEnd_1212735 : Nat := 4983230072969 + 3 ^ 40 * 1212735 * 2
def baseEnd_1212735 : Nat := 207571987176805967478413

theorem tailTrace_1212735 : CollatzResearch.WordTrace tailWord_1212735 prefixEnd_1212735 207571987176805967478413 := by
  unfold tailWord_1212735
  simp only [CollatzResearch.WordTrace]
  refine ⟨44232079261475688493551659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29488052840983792329034439 44232079261475688493551659)
  ·
    refine ⟨66348118892213532740327489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44232079261475688493551659 66348118892213532740327489)
    ·
      refine ⟨49761089169160149555245617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66348118892213532740327489 49761089169160149555245617)
      ·
        refine ⟨37320816876870112166434213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49761089169160149555245617 37320816876870112166434213)
        ·
          refine ⟨6997653164413146031206415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37320816876870112166434213 6997653164413146031206415)
          ·
            refine ⟨10496479746619719046809623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6997653164413146031206415 10496479746619719046809623)
            ·
              refine ⟨15744719619929578570214435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10496479746619719046809623 15744719619929578570214435)
              ·
                refine ⟨23617079429894367855321653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15744719619929578570214435 23617079429894367855321653)
                ·
                  refine ⟨2214101196552596986436405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23617079429894367855321653 2214101196552596986436405)
                  ·
                    refine ⟨207571987176805967478413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2214101196552596986436405 207571987176805967478413)
                    ·
                      rfl

theorem cell23_1212735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 5].length) (baseStart_1212735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212735 prefixEnd_1212735 := by exact prefixLift 1212735
  have htrace : WordTrace (prefixWord ++ tailWord_1212735) baseStart_1212735 baseEnd_1212735 := by
    simpa [prefixWord, tailWord_1212735, baseEnd_1212735] using wordTrace_append hprefix tailTrace_1212735
  have hstable : (prefixWord ++ tailWord_1212735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212735).length < 2 ^ (prefixWord ++ tailWord_1212735).sum := by decide
  have hdescent : baseEnd_1212735 < baseStart_1212735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212785 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_1212785 : Nat := 118140960795 + 1212785 * 2 ^ 59
def prefixEnd_1212785 : Nat := 4983230072969 + 3 ^ 40 * 1212785 * 2
def baseEnd_1212785 : Nat := 622741635563142706810009

theorem tailTrace_1212785 : CollatzResearch.WordTrace tailWord_1212785 prefixEnd_1212785 622741635563142706810009 := by
  unfold tailWord_1212785
  simp only [CollatzResearch.WordTrace]
  refine ⟨44233902911294547032871809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29489268607529698021914539 44233902911294547032871809)
  ·
    refine ⟨33175427183470910274653857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44233902911294547032871809 33175427183470910274653857)
    ·
      refine ⟨24881570387603182705990393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33175427183470910274653857 24881570387603182705990393)
      ·
        refine ⟨18661177790702387029492795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24881570387603182705990393 18661177790702387029492795)
        ·
          refine ⟨27991766686053580544239193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18661177790702387029492795 27991766686053580544239193)
          ·
            refine ⟨20993825014540185408179395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27991766686053580544239193 20993825014540185408179395)
            ·
              refine ⟨31490737521810278112269093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20993825014540185408179395 31490737521810278112269093)
              ·
                refine ⟨5904513285339427146050455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31490737521810278112269093 5904513285339427146050455)
                ·
                  refine ⟨8856769928009140719075683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5904513285339427146050455 8856769928009140719075683)
                  ·
                    refine ⟨13285154892013711078613525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8856769928009140719075683 13285154892013711078613525)
                    ·
                      refine ⟨622741635563142706810009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13285154892013711078613525 622741635563142706810009)
                      ·
                        rfl

theorem cell23_1212785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_1212785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212785 prefixEnd_1212785 := by exact prefixLift 1212785
  have htrace : WordTrace (prefixWord ++ tailWord_1212785) baseStart_1212785 baseEnd_1212785 := by
    simpa [prefixWord, tailWord_1212785, baseEnd_1212785] using wordTrace_append hprefix tailTrace_1212785
  have hstable : (prefixWord ++ tailWord_1212785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212785).length < 2 ^ (prefixWord ++ tailWord_1212785).sum := by decide
  have hdescent : baseEnd_1212785 < baseStart_1212785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212809 : List Nat := [1, 2, 1, 1, 6, 1, 1, 4, 1, 2, 3]
def baseStart_1212809 : Nat := 118140960795 + 1212809 * 2 ^ 59
def prefixEnd_1212809 : Nat := 4983230072969 + 3 ^ 40 * 1212809 * 2
def baseEnd_1212809 : Nat := 622753959098850612909899

theorem tailTrace_1212809 : CollatzResearch.WordTrace tailWord_1212809 prefixEnd_1212809 622753959098850612909899 := by
  unfold tailWord_1212809
  simp only [CollatzResearch.WordTrace]
  refine ⟨44234778263207599131745481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29489852175471732754496987 44234778263207599131745481)
  ·
    refine ⟨33176083697405699348809111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44234778263207599131745481 33176083697405699348809111)
    ·
      refine ⟨49764125546108549023213667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33176083697405699348809111 49764125546108549023213667)
      ·
        refine ⟨74646188319162823534820501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49764125546108549023213667 74646188319162823534820501)
        ·
          refine ⟨3499040077460757353194711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74646188319162823534820501 3499040077460757353194711)
          ·
            refine ⟨5248560116191136029792067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3499040077460757353194711 5248560116191136029792067)
            ·
              refine ⟨7872840174286704044688101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5248560116191136029792067 7872840174286704044688101)
              ·
                refine ⟨1476157532678757008379019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7872840174286704044688101 1476157532678757008379019)
                ·
                  refine ⟨2214236299018135512568529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1476157532678757008379019 2214236299018135512568529)
                  ·
                    refine ⟨1660677224263601634426397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2214236299018135512568529 1660677224263601634426397)
                    ·
                      refine ⟨622753959098850612909899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1660677224263601634426397 622753959098850612909899)
                      ·
                        rfl

theorem cell23_1212809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 2, 3].length) (baseStart_1212809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212809 prefixEnd_1212809 := by exact prefixLift 1212809
  have htrace : WordTrace (prefixWord ++ tailWord_1212809) baseStart_1212809 baseEnd_1212809 := by
    simpa [prefixWord, tailWord_1212809, baseEnd_1212809] using wordTrace_append hprefix tailTrace_1212809
  have hstable : (prefixWord ++ tailWord_1212809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212809).length < 2 ^ (prefixWord ++ tailWord_1212809).sum := by decide
  have hdescent : baseEnd_1212809 < baseStart_1212809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212812 : List Nat := [2, 2, 1, 2, 1, 4, 4, 7]
def baseStart_1212812 : Nat := 118140960795 + 1212812 * 2 ^ 59
def prefixEnd_1212812 : Nat := 4983230072969 + 3 ^ 40 * 1212812 * 2
def baseEnd_1212812 : Nat := 23065018501511633376755

theorem tailTrace_1212812 : CollatzResearch.WordTrace tailWord_1212812 prefixEnd_1212812 23065018501511633376755 := by
  unfold tailWord_1212812
  simp only [CollatzResearch.WordTrace]
  refine ⟨22117443841098365322052345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29489925121464487096069793 22117443841098365322052345)
  ·
    refine ⟨16588082880823773991539259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22117443841098365322052345 16588082880823773991539259)
    ·
      refine ⟨24882124321235660987308889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16588082880823773991539259 24882124321235660987308889)
      ·
        refine ⟨18661593240926745740481667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24882124321235660987308889 18661593240926745740481667)
        ·
          refine ⟨27992389861390118610722501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18661593240926745740481667 27992389861390118610722501)
          ·
            refine ⟨5248573099010647239510469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27992389861390118610722501 5248573099010647239510469)
            ·
              refine ⟨984107456064496357408213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5248573099010647239510469 984107456064496357408213)
              ·
                refine ⟨23065018501511633376755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 984107456064496357408213 23065018501511633376755)
                ·
                  rfl

theorem cell23_1212812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 7].length) (baseStart_1212812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212812 prefixEnd_1212812 := by exact prefixLift 1212812
  have htrace : WordTrace (prefixWord ++ tailWord_1212812) baseStart_1212812 baseEnd_1212812 := by
    simpa [prefixWord, tailWord_1212812, baseEnd_1212812] using wordTrace_append hprefix tailTrace_1212812
  have hstable : (prefixWord ++ tailWord_1212812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212812).length < 2 ^ (prefixWord ++ tailWord_1212812).sum := by decide
  have hdescent : baseEnd_1212812 < baseStart_1212812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212823 : List Nat := [1, 1, 3, 3, 1, 1, 5, 3, 1, 2, 2]
def baseStart_1212823 : Nat := 118140960795 + 1212823 * 2 ^ 59
def prefixEnd_1212823 : Nat := 4983230072969 + 3 ^ 40 * 1212823 * 2
def baseEnd_1212823 : Nat := 622761147828013558134835

theorem tailTrace_1212823 : CollatzResearch.WordTrace tailWord_1212823 prefixEnd_1212823 622761147828013558134835 := by
  unfold tailWord_1212823
  simp only [CollatzResearch.WordTrace]
  refine ⟨44235288885156879522755123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29490192590104586348503415 44235288885156879522755123)
  ·
    refine ⟨66352933327735319284132685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44235288885156879522755123 66352933327735319284132685)
    ·
      refine ⟨24882349997900744731549757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66352933327735319284132685 24882349997900744731549757)
      ·
        refine ⟨9330881249212779274331159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24882349997900744731549757 9330881249212779274331159)
        ·
          refine ⟨13996321873819168911496739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9330881249212779274331159 13996321873819168911496739)
          ·
            refine ⟨20994482810728753367245109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13996321873819168911496739 20994482810728753367245109)
            ·
              refine ⟨1968232763505820628179229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20994482810728753367245109 1968232763505820628179229)
              ·
                refine ⟨738087286314682735567211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1968232763505820628179229 738087286314682735567211)
                ·
                  refine ⟨1107130929472024103350817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738087286314682735567211 1107130929472024103350817)
                  ·
                    refine ⟨830348197104018077513113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1107130929472024103350817 830348197104018077513113)
                    ·
                      refine ⟨622761147828013558134835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 830348197104018077513113 622761147828013558134835)
                      ·
                        rfl

theorem cell23_1212823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_1212823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212823 prefixEnd_1212823 := by exact prefixLift 1212823
  have htrace : WordTrace (prefixWord ++ tailWord_1212823) baseStart_1212823 baseEnd_1212823 := by
    simpa [prefixWord, tailWord_1212823, baseEnd_1212823] using wordTrace_append hprefix tailTrace_1212823
  have hstable : (prefixWord ++ tailWord_1212823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212823).length < 2 ^ (prefixWord ++ tailWord_1212823).sum := by decide
  have hdescent : baseEnd_1212823 < baseStart_1212823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212829 : List Nat := [1, 4, 2, 1, 5, 1, 9]
def baseStart_1212829 : Nat := 118140960795 + 1212829 * 2 ^ 59
def prefixEnd_1212829 : Nat := 4983230072969 + 3 ^ 40 * 1212829 * 2
def baseEnd_1212829 : Nat := 7688447268048648576047

theorem tailTrace_1212829 : CollatzResearch.WordTrace tailWord_1212829 prefixEnd_1212829 7688447268048648576047 := by
  unfold tailWord_1212829
  simp only [CollatzResearch.WordTrace]
  refine ⟨44235507723135142547473541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29490338482090095031649027 44235507723135142547473541)
  ·
    refine ⟨8294157698087839227651289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44235507723135142547473541 8294157698087839227651289)
    ·
      refine ⟨6220618273565879420738467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8294157698087839227651289 6220618273565879420738467)
      ·
        refine ⟨9330927410348819131107701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6220618273565879420738467 9330927410348819131107701)
        ·
          refine ⟨874774444720201793541347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9330927410348819131107701 874774444720201793541347)
          ·
            refine ⟨1312161667080302690312021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874774444720201793541347 1312161667080302690312021)
            ·
              refine ⟨7688447268048648576047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1312161667080302690312021 7688447268048648576047)
              ·
                rfl

theorem cell23_1212829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 9].length) (baseStart_1212829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212829 prefixEnd_1212829 := by exact prefixLift 1212829
  have htrace : WordTrace (prefixWord ++ tailWord_1212829) baseStart_1212829 baseEnd_1212829 := by
    simpa [prefixWord, tailWord_1212829, baseEnd_1212829] using wordTrace_append hprefix tailTrace_1212829
  have hstable : (prefixWord ++ tailWord_1212829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212829).length < 2 ^ (prefixWord ++ tailWord_1212829).sum := by decide
  have hdescent : baseEnd_1212829 < baseStart_1212829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212840 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_1212840 : Nat := 118140960795 + 1212840 * 2 ^ 59
def prefixEnd_1212840 : Nat := 4983230072969 + 3 ^ 40 * 1212840 * 2
def baseEnd_1212840 : Nat := 622769876999139991622257

theorem tailTrace_1212840 : CollatzResearch.WordTrace tailWord_1212840 prefixEnd_1212840 622769876999139991622257 := by
  unfold tailWord_1212840
  simp only [CollatzResearch.WordTrace]
  refine ⟨22117954463047645713061987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29490605950730194284082649 22117954463047645713061987)
  ·
    refine ⟨33176931694571468569592981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22117954463047645713061987 33176931694571468569592981)
    ·
      refine ⟨1555168673183037589199671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33176931694571468569592981 1555168673183037589199671)
      ·
        refine ⟨2332753009774556383799507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1555168673183037589199671 2332753009774556383799507)
        ·
          refine ⟨3499129514661834575699261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2332753009774556383799507 3499129514661834575699261)
          ·
            refine ⟨1312173567998187965887223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3499129514661834575699261 1312173567998187965887223)
            ·
              refine ⟨1968260351997281948830835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1312173567998187965887223 1968260351997281948830835)
              ·
                refine ⟨2952390527995922923246253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1968260351997281948830835 2952390527995922923246253)
                ·
                  refine ⟨1107146447998471096217345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2952390527995922923246253 1107146447998471096217345)
                  ·
                    refine ⟨830359835998853322163009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1107146447998471096217345 830359835998853322163009)
                    ·
                      refine ⟨622769876999139991622257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 830359835998853322163009 622769876999139991622257)
                      ·
                        rfl

theorem cell23_1212840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_1212840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212840 prefixEnd_1212840 := by exact prefixLift 1212840
  have htrace : WordTrace (prefixWord ++ tailWord_1212840) baseStart_1212840 baseEnd_1212840 := by
    simpa [prefixWord, tailWord_1212840, baseEnd_1212840] using wordTrace_append hprefix tailTrace_1212840
  have hstable : (prefixWord ++ tailWord_1212840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212840).length < 2 ^ (prefixWord ++ tailWord_1212840).sum := by decide
  have hdescent : baseEnd_1212840 < baseStart_1212840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212909 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1212909 : Nat := 118140960795 + 1212909 * 2 ^ 59
def prefixEnd_1212909 : Nat := 4983230072969 + 3 ^ 40 * 1212909 * 2
def baseEnd_1212909 : Nat := 622805307164300221659439

theorem tailTrace_1212909 : CollatzResearch.WordTrace tailWord_1212909 prefixEnd_1212909 622805307164300221659439 := by
  unfold tailWord_1212909
  simp only [CollatzResearch.WordTrace]
  refine ⟨44238425562845316210385781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29492283708563544140257187 44238425562845316210385781)
  ·
    refine ⟨4147352396516748394723667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44238425562845316210385781 4147352396516748394723667)
    ·
      refine ⟨6221028594775122592085501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4147352396516748394723667 6221028594775122592085501)
      ·
        refine ⟨2332885723040670972032063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6221028594775122592085501 2332885723040670972032063)
        ·
          refine ⟨3499328584561006458048095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2332885723040670972032063 3499328584561006458048095)
          ·
            refine ⟨5248992876841509687072143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3499328584561006458048095 5248992876841509687072143)
            ·
              refine ⟨7873489315262264530608215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5248992876841509687072143 7873489315262264530608215)
              ·
                refine ⟨11810233972893396795912323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7873489315262264530608215 11810233972893396795912323)
                ·
                  refine ⟨17715350959340095193868485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11810233972893396795912323 17715350959340095193868485)
                  ·
                    refine ⟨3321628304876267848850341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17715350959340095193868485 3321628304876267848850341)
                    ·
                      refine ⟨622805307164300221659439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3321628304876267848850341 622805307164300221659439)
                      ·
                        rfl

theorem cell23_1212909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1212909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212909 prefixEnd_1212909 := by exact prefixLift 1212909
  have htrace : WordTrace (prefixWord ++ tailWord_1212909) baseStart_1212909 baseEnd_1212909 := by
    simpa [prefixWord, tailWord_1212909, baseEnd_1212909] using wordTrace_append hprefix tailTrace_1212909
  have hstable : (prefixWord ++ tailWord_1212909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212909).length < 2 ^ (prefixWord ++ tailWord_1212909).sum := by decide
  have hdescent : baseEnd_1212909 < baseStart_1212909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212934 : List Nat := [6, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_1212934 : Nat := 118140960795 + 1212934 * 2 ^ 59
def prefixEnd_1212934 : Nat := 4983230072969 + 3 ^ 40 * 1212934 * 2
def baseEnd_1212934 : Nat := 622818144180662623846825

theorem tailTrace_1212934 : CollatzResearch.WordTrace tailWord_1212934 prefixEnd_1212934 622818144180662623846825 := by
  unfold tailWord_1212934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1382479293367335796251433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29492891591836496986697237 1382479293367335796251433)
  ·
    refine ⟨1036859470025501847188575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1382479293367335796251433 1036859470025501847188575)
    ·
      refine ⟨1555289205038252770782863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1036859470025501847188575 1555289205038252770782863)
      ·
        refine ⟨2332933807557379156174295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1555289205038252770782863 2332933807557379156174295)
        ·
          refine ⟨3499400711336068734261443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2332933807557379156174295 3499400711336068734261443)
          ·
            refine ⟨5249101067004103101392165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3499400711336068734261443 5249101067004103101392165)
            ·
              refine ⟨984206450063269331511031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5249101067004103101392165 984206450063269331511031)
              ·
                refine ⟨1476309675094903997266547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984206450063269331511031 1476309675094903997266547)
                ·
                  refine ⟨2214464512642355995899821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1476309675094903997266547 2214464512642355995899821)
                  ·
                    refine ⟨830424192240883498462433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2214464512642355995899821 830424192240883498462433)
                    ·
                      refine ⟨622818144180662623846825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 830424192240883498462433 622818144180662623846825)
                      ·
                        rfl

theorem cell23_1212934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_1212934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212934 prefixEnd_1212934 := by exact prefixLift 1212934
  have htrace : WordTrace (prefixWord ++ tailWord_1212934) baseStart_1212934 baseEnd_1212934 := by
    simpa [prefixWord, tailWord_1212934, baseEnd_1212934] using wordTrace_append hprefix tailTrace_1212934
  have hstable : (prefixWord ++ tailWord_1212934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212934).length < 2 ^ (prefixWord ++ tailWord_1212934).sum := by decide
  have hdescent : baseEnd_1212934 < baseStart_1212934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212979 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 3, 4]
def baseStart_1212979 : Nat := 118140960795 + 1212979 * 2 ^ 59
def prefixEnd_1212979 : Nat := 4983230072969 + 3 ^ 40 * 1212979 * 2
def baseEnd_1212979 : Nat := 207613750270038315928039

theorem tailTrace_1212979 : CollatzResearch.WordTrace tailWord_1212979 prefixEnd_1212979 207613750270038315928039 := by
  unfold tailWord_1212979
  simp only [CollatzResearch.WordTrace]
  refine ⟨44240978672591718165433991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29493985781727812110289327 44240978672591718165433991)
  ·
    refine ⟨66361468008887577248150987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44240978672591718165433991 66361468008887577248150987)
    ·
      refine ⟨99542202013331365872226481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66361468008887577248150987 99542202013331365872226481)
      ·
        refine ⟨74656651509998524404169861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99542202013331365872226481 74656651509998524404169861)
        ·
          refine ⟨13998122158124723325781849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74656651509998524404169861 13998122158124723325781849)
          ·
            refine ⟨10498591618593542494336387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13998122158124723325781849 10498591618593542494336387)
            ·
              refine ⟨15747887427890313741504581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10498591618593542494336387 15747887427890313741504581)
              ·
                refine ⟨2952728892729433826532109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15747887427890313741504581 2952728892729433826532109)
                ·
                  refine ⟨1107273334773537684949541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2952728892729433826532109 1107273334773537684949541)
                  ·
                    refine ⟨207613750270038315928039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1107273334773537684949541 207613750270038315928039)
                    ·
                      rfl

theorem cell23_1212979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 4].length) (baseStart_1212979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212979 prefixEnd_1212979 := by exact prefixLift 1212979
  have htrace : WordTrace (prefixWord ++ tailWord_1212979) baseStart_1212979 baseEnd_1212979 := by
    simpa [prefixWord, tailWord_1212979, baseEnd_1212979] using wordTrace_append hprefix tailTrace_1212979
  have hstable : (prefixWord ++ tailWord_1212979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212979).length < 2 ^ (prefixWord ++ tailWord_1212979).sum := by decide
  have hdescent : baseEnd_1212979 < baseStart_1212979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212992 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 8]
def baseStart_1212992 : Nat := 118140960795 + 1212992 * 2 ^ 59
def prefixEnd_1212992 : Nat := 4983230072969 + 3 ^ 40 * 1212992 * 2
def baseEnd_1212992 : Nat := 69205325117624821880173

theorem tailTrace_1212992 : CollatzResearch.WordTrace tailWord_1212992 prefixEnd_1212992 69205325117624821880173 := by
  unfold tailWord_1212992
  simp only [CollatzResearch.WordTrace]
  refine ⟨22120726410772310692828615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29494301881029747590438153 22120726410772310692828615)
  ·
    refine ⟨33181089616158466039242923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22120726410772310692828615 33181089616158466039242923)
    ·
      refine ⟨49771634424237699058864385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33181089616158466039242923 49771634424237699058864385)
      ·
        refine ⟨37328725818178274294148289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49771634424237699058864385 37328725818178274294148289)
        ·
          refine ⟨27996544363633705720611217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37328725818178274294148289 27996544363633705720611217)
          ·
            refine ⟨20997408272725279290458413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27996544363633705720611217 20997408272725279290458413)
            ·
              refine ⟨7874028102271979733921905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20997408272725279290458413 7874028102271979733921905)
              ·
                refine ⟨5905521076703984800441429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7874028102271979733921905 5905521076703984800441429)
                ·
                  refine ⟨69205325117624821880173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5905521076703984800441429 69205325117624821880173)
                  ·
                    rfl

theorem cell23_1212992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 8].length) (baseStart_1212992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1212992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1212992 prefixEnd_1212992 := by exact prefixLift 1212992
  have htrace : WordTrace (prefixWord ++ tailWord_1212992) baseStart_1212992 baseEnd_1212992 := by
    simpa [prefixWord, tailWord_1212992, baseEnd_1212992] using wordTrace_append hprefix tailTrace_1212992
  have hstable : (prefixWord ++ tailWord_1212992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212992).length < 2 ^ (prefixWord ++ tailWord_1212992).sum := by decide
  have hdescent : baseEnd_1212992 < baseStart_1212992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
