import V185TrunkScan23Chunk0178

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1059449 : List Nat := [1, 2, 1, 3, 3, 2, 1, 4, 2, 2, 2]
def baseStart_1059449 : Nat := 118140960795 + 1059449 * 2 ^ 59
def prefixEnd_1059449 : Nat := 4983230072969 + 3 ^ 40 * 1059449 * 2
def baseEnd_1059449 : Nat := 544006565925330634615189

theorem tailTrace_1059449 : CollatzResearch.WordTrace tailWord_1059449 prefixEnd_1059449 544006565925330634615189 := by
  unfold tailWord_1059449
  simp only [CollatzResearch.WordTrace]
  refine ⟨38641279538804687328981401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25760853025869791552654267 38641279538804687328981401)
  ·
    refine ⟨28980959654103515496736051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38641279538804687328981401 28980959654103515496736051)
    ·
      refine ⟨43471439481155273245104077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28980959654103515496736051 43471439481155273245104077)
      ·
        refine ⟨16301789805433227466914029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43471439481155273245104077 16301789805433227466914029)
        ·
          refine ⟨6113171177037460300092761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16301789805433227466914029 6113171177037460300092761)
          ·
            refine ⟨4584878382778095225069571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6113171177037460300092761 4584878382778095225069571)
            ·
              refine ⟨6877317574167142837604357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4584878382778095225069571 6877317574167142837604357)
              ·
                refine ⟨1289497045156339282050817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6877317574167142837604357 1289497045156339282050817)
                ·
                  refine ⟨967122783867254461538113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1289497045156339282050817 967122783867254461538113)
                  ·
                    refine ⟨725342087900440846153585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 967122783867254461538113 725342087900440846153585)
                    ·
                      refine ⟨544006565925330634615189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 725342087900440846153585 544006565925330634615189)
                      ·
                        rfl

theorem cell23_1059449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_1059449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059449 prefixEnd_1059449 := by exact prefixLift 1059449
  have htrace : WordTrace (prefixWord ++ tailWord_1059449) baseStart_1059449 baseEnd_1059449 := by
    simpa [prefixWord, tailWord_1059449, baseEnd_1059449] using wordTrace_append hprefix tailTrace_1059449
  have hstable : (prefixWord ++ tailWord_1059449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059449).length < 2 ^ (prefixWord ++ tailWord_1059449).sum := by decide
  have hdescent : baseEnd_1059449 < baseStart_1059449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059489 : List Nat := [1, 2, 3, 3, 3, 1, 2, 3, 5]
def baseStart_1059489 : Nat := 118140960795 + 1059489 * 2 ^ 59
def prefixEnd_1059489 : Nat := 4983230072969 + 3 ^ 40 * 1059489 * 2
def baseEnd_1059489 : Nat := 60447456127945608679445

theorem tailTrace_1059489 : CollatzResearch.WordTrace tailWord_1059489 prefixEnd_1059489 60447456127945608679445 := by
  unfold tailWord_1059489
  simp only [CollatzResearch.WordTrace]
  refine ⟨38642738458659774160437521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25761825639106516106958347 38642738458659774160437521)
  ·
    refine ⟨28982053843994830620328141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38642738458659774160437521 28982053843994830620328141)
    ·
      refine ⟨10868270191498061482623053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28982053843994830620328141 10868270191498061482623053)
      ·
        refine ⟨4075601321811773055983645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10868270191498061482623053 4075601321811773055983645)
        ·
          refine ⟨1528350495679414895993867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4075601321811773055983645 1528350495679414895993867)
          ·
            refine ⟨2292525743519122343990801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1528350495679414895993867 2292525743519122343990801)
            ·
              refine ⟨1719394307639341757993101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2292525743519122343990801 1719394307639341757993101)
              ·
                refine ⟨644772865364753159247413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1719394307639341757993101 644772865364753159247413)
                ·
                  refine ⟨60447456127945608679445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 644772865364753159247413 60447456127945608679445)
                  ·
                    rfl

theorem cell23_1059489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 5].length) (baseStart_1059489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059489 prefixEnd_1059489 := by exact prefixLift 1059489
  have htrace : WordTrace (prefixWord ++ tailWord_1059489) baseStart_1059489 baseEnd_1059489 := by
    simpa [prefixWord, tailWord_1059489, baseEnd_1059489] using wordTrace_append hprefix tailTrace_1059489
  have hstable : (prefixWord ++ tailWord_1059489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059489).length < 2 ^ (prefixWord ++ tailWord_1059489).sum := by decide
  have hdescent : baseEnd_1059489 < baseStart_1059489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059575 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 3, 5]
def baseStart_1059575 : Nat := 118140960795 + 1059575 * 2 ^ 59
def prefixEnd_1059575 : Nat := 4983230072969 + 3 ^ 40 * 1059575 * 2
def baseEnd_1059575 : Nat := 181357088162599047213203

theorem tailTrace_1059575 : CollatzResearch.WordTrace tailWord_1059575 prefixEnd_1059575 181357088162599047213203 := by
  unfold tailWord_1059575
  simp only [CollatzResearch.WordTrace]
  refine ⟨38645875136348210848068179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25763916757565473898712119 38645875136348210848068179)
  ·
    refine ⟨57968812704522316272102269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38645875136348210848068179 57968812704522316272102269)
    ·
      refine ⟨21738304764195868602038351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57968812704522316272102269 21738304764195868602038351)
      ·
        refine ⟨32607457146293802903057527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21738304764195868602038351 32607457146293802903057527)
        ·
          refine ⟨48911185719440704354586291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32607457146293802903057527 48911185719440704354586291)
          ·
            refine ⟨73366778579161056531879437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48911185719440704354586291 73366778579161056531879437)
            ·
              refine ⟨27512541967185396199454789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73366778579161056531879437 27512541967185396199454789)
              ·
                refine ⟨5158601618847261787397773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27512541967185396199454789 5158601618847261787397773)
                ·
                  refine ⟨1934475607067723170274165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5158601618847261787397773 1934475607067723170274165)
                  ·
                    refine ⟨181357088162599047213203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1934475607067723170274165 181357088162599047213203)
                    ·
                      rfl

theorem cell23_1059575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_1059575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059575 prefixEnd_1059575 := by exact prefixLift 1059575
  have htrace : WordTrace (prefixWord ++ tailWord_1059575) baseStart_1059575 baseEnd_1059575 := by
    simpa [prefixWord, tailWord_1059575, baseEnd_1059575] using wordTrace_append hprefix tailTrace_1059575
  have hstable : (prefixWord ++ tailWord_1059575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059575).length < 2 ^ (prefixWord ++ tailWord_1059575).sum := by decide
  have hdescent : baseEnd_1059575 < baseStart_1059575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059592 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 3, 5]
def baseStart_1059592 : Nat := 118140960795 + 1059592 * 2 ^ 59
def prefixEnd_1059592 : Nat := 4983230072969 + 3 ^ 40 * 1059592 * 2
def baseEnd_1059592 : Nat := 181359997886307858375677

theorem tailTrace_1059592 : CollatzResearch.WordTrace tailWord_1059592 prefixEnd_1059592 181359997886307858375677 := by
  unfold tailWord_1059592
  simp only [CollatzResearch.WordTrace]
  refine ⟨19323247588643311375718515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25764330118191081834291353 19323247588643311375718515)
  ·
    refine ⟨28984871382964967063577773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19323247588643311375718515 28984871382964967063577773)
    ·
      refine ⟨10869326768611862648841665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28984871382964967063577773 10869326768611862648841665)
      ·
        refine ⟨8151995076458896986631249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10869326768611862648841665 8151995076458896986631249)
        ·
          refine ⟨6113996307344172739973437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8151995076458896986631249 6113996307344172739973437)
          ·
            refine ⟨2292748615254064777490039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6113996307344172739973437 2292748615254064777490039)
            ·
              refine ⟨3439122922881097166235059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2292748615254064777490039 3439122922881097166235059)
              ·
                refine ⟨5158684384321645749352589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3439122922881097166235059 5158684384321645749352589)
                ·
                  refine ⟨1934506644120617156007221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5158684384321645749352589 1934506644120617156007221)
                  ·
                    refine ⟨181359997886307858375677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1934506644120617156007221 181359997886307858375677)
                    ·
                      rfl

theorem cell23_1059592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_1059592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059592 prefixEnd_1059592 := by exact prefixLift 1059592
  have htrace : WordTrace (prefixWord ++ tailWord_1059592) baseStart_1059592 baseEnd_1059592 := by
    simpa [prefixWord, tailWord_1059592, baseEnd_1059592] using wordTrace_append hprefix tailTrace_1059592
  have hstable : (prefixWord ++ tailWord_1059592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059592).length < 2 ^ (prefixWord ++ tailWord_1059592).sum := by decide
  have hdescent : baseEnd_1059592 < baseStart_1059592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059599 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 2, 3, 2]
def baseStart_1059599 : Nat := 118140960795 + 1059599 * 2 ^ 59
def prefixEnd_1059599 : Nat := 4983230072969 + 3 ^ 40 * 1059599 * 2
def baseEnd_1059599 : Nat := 544083588023505047739499

theorem tailTrace_1059599 : CollatzResearch.WordTrace tailWord_1059599 prefixEnd_1059599 544083588023505047739499 := by
  unfold tailWord_1059599
  simp only [CollatzResearch.WordTrace]
  refine ⟨38646750488261262946941851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25764500325507508631294567 38646750488261262946941851)
  ·
    refine ⟨57970125732391894420412777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38646750488261262946941851 57970125732391894420412777)
    ·
      refine ⟨43477594299293920815309583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57970125732391894420412777 43477594299293920815309583)
      ·
        refine ⟨65216391448940881222964375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43477594299293920815309583 65216391448940881222964375)
        ·
          refine ⟨97824587173411321834446563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65216391448940881222964375 97824587173411321834446563)
          ·
            refine ⟨146736880760116982751669845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97824587173411321834446563 146736880760116982751669845)
            ·
              refine ⟨1719572821407620891621131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 146736880760116982751669845 1719572821407620891621131)
              ·
                refine ⟨2579359232111431337431697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719572821407620891621131 2579359232111431337431697)
                ·
                  refine ⟨1934519424083573503073773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2579359232111431337431697 1934519424083573503073773)
                  ·
                    refine ⟨725444784031340063652665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1934519424083573503073773 725444784031340063652665)
                    ·
                      refine ⟨544083588023505047739499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 725444784031340063652665 544083588023505047739499)
                      ·
                        rfl

theorem cell23_1059599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 3, 2].length) (baseStart_1059599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059599 prefixEnd_1059599 := by exact prefixLift 1059599
  have htrace : WordTrace (prefixWord ++ tailWord_1059599) baseStart_1059599 baseEnd_1059599 := by
    simpa [prefixWord, tailWord_1059599, baseEnd_1059599] using wordTrace_append hprefix tailTrace_1059599
  have hstable : (prefixWord ++ tailWord_1059599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059599).length < 2 ^ (prefixWord ++ tailWord_1059599).sum := by decide
  have hdescent : baseEnd_1059599 < baseStart_1059599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059679 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 4, 1, 3]
def baseStart_1059679 : Nat := 118140960795 + 1059679 * 2 ^ 59
def prefixEnd_1059679 : Nat := 4983230072969 + 3 ^ 40 * 1059679 * 2
def baseEnd_1059679 : Nat := 544124666475864734739131

theorem tailTrace_1059679 : CollatzResearch.WordTrace tailWord_1059679 prefixEnd_1059679 544124666475864734739131 := by
  unfold tailWord_1059679
  simp only [CollatzResearch.WordTrace]
  refine ⟨38649668327971436609854091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25766445551980957739902727 38649668327971436609854091)
  ·
    refine ⟨57974502491957154914781137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38649668327971436609854091 57974502491957154914781137)
    ·
      refine ⟨43480876868967866186085853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57974502491957154914781137 43480876868967866186085853)
      ·
        refine ⟨16305328825862949819782195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43480876868967866186085853 16305328825862949819782195)
        ·
          refine ⟨24457993238794424729673293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16305328825862949819782195 24457993238794424729673293)
          ·
            refine ⟨9171747464547909273627485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24457993238794424729673293 9171747464547909273627485)
            ·
              refine ⟨3439405299205465977610307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9171747464547909273627485 3439405299205465977610307)
              ·
                refine ⟨5159107948808198966415461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3439405299205465977610307 5159107948808198966415461)
                ·
                  refine ⟨967332740401537306202899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5159107948808198966415461 967332740401537306202899)
                  ·
                    refine ⟨1450999110602305959304349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 967332740401537306202899 1450999110602305959304349)
                    ·
                      refine ⟨544124666475864734739131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1450999110602305959304349 544124666475864734739131)
                      ·
                        rfl

theorem cell23_1059679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_1059679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059679 prefixEnd_1059679 := by exact prefixLift 1059679
  have htrace : WordTrace (prefixWord ++ tailWord_1059679) baseStart_1059679 baseEnd_1059679 := by
    simpa [prefixWord, tailWord_1059679, baseEnd_1059679] using wordTrace_append hprefix tailTrace_1059679
  have hstable : (prefixWord ++ tailWord_1059679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059679).length < 2 ^ (prefixWord ++ tailWord_1059679).sum := by decide
  have hdescent : baseEnd_1059679 < baseStart_1059679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059757 : List Nat := [1, 5, 2, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1059757 : Nat := 118140960795 + 1059757 * 2 ^ 59
def prefixEnd_1059757 : Nat := 4983230072969 + 3 ^ 40 * 1059757 * 2
def baseEnd_1059757 : Nat := 544164717966915429563773

theorem tailTrace_1059757 : CollatzResearch.WordTrace tailWord_1059757 prefixEnd_1059757 544164717966915429563773 := by
  unfold tailWord_1059757
  simp only [CollatzResearch.WordTrace]
  refine ⟨38652513221688855931193525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25768342147792570620795683 38652513221688855931193525)
  ·
    refine ⟨3623673114533330243549393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38652513221688855931193525 3623673114533330243549393)
    ·
      refine ⟨2717754835899997682662045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3623673114533330243549393 2717754835899997682662045)
      ·
        refine ⟨1019158063462499130998267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2717754835899997682662045 1019158063462499130998267)
        ·
          refine ⟨1528737095193748696497401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019158063462499130998267 1528737095193748696497401)
          ·
            refine ⟨1146552821395311522373051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1528737095193748696497401 1146552821395311522373051)
            ·
              refine ⟨1719829232092967283559577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146552821395311522373051 1719829232092967283559577)
              ·
                refine ⟨1289871924069725462669683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1719829232092967283559577 1289871924069725462669683)
                ·
                  refine ⟨1934807886104588194004525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1289871924069725462669683 1934807886104588194004525)
                  ·
                    refine ⟨725552957289220572751697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1934807886104588194004525 725552957289220572751697)
                    ·
                      refine ⟨544164717966915429563773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 725552957289220572751697 544164717966915429563773)
                      ·
                        rfl

theorem cell23_1059757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1059757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059757 prefixEnd_1059757 := by exact prefixLift 1059757
  have htrace : WordTrace (prefixWord ++ tailWord_1059757) baseStart_1059757 baseEnd_1059757 := by
    simpa [prefixWord, tailWord_1059757, baseEnd_1059757] using wordTrace_append hprefix tailTrace_1059757
  have hstable : (prefixWord ++ tailWord_1059757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059757).length < 2 ^ (prefixWord ++ tailWord_1059757).sum := by decide
  have hdescent : baseEnd_1059757 < baseStart_1059757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059792 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 4]
def baseStart_1059792 : Nat := 118140960795 + 1059792 * 2 ^ 59
def prefixEnd_1059792 : Nat := 4983230072969 + 3 ^ 40 * 1059792 * 2
def baseEnd_1059792 : Nat := 544182689789822792626111

theorem tailTrace_1059792 : CollatzResearch.WordTrace tailWord_1059792 prefixEnd_1059792 544182689789822792626111 := by
  unfold tailWord_1059792
  simp only [CollatzResearch.WordTrace]
  refine ⟨19326894888281028454358815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25769193184374704605811753 19326894888281028454358815)
  ·
    refine ⟨28990342332421542681538223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19326894888281028454358815 28990342332421542681538223)
    ·
      refine ⟨43485513498632314022307335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28990342332421542681538223 43485513498632314022307335)
      ·
        refine ⟨65228270247948471033461003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43485513498632314022307335 65228270247948471033461003)
        ·
          refine ⟨97842405371922706550191505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65228270247948471033461003 97842405371922706550191505)
          ·
            refine ⟨73381804028942029912643629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97842405371922706550191505 73381804028942029912643629)
            ·
              refine ⟨27518176510853261217241361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73381804028942029912643629 27518176510853261217241361)
              ·
                refine ⟨20638632383139945912931021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27518176510853261217241361 20638632383139945912931021)
                ·
                  refine ⟨7739487143677479717349133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20638632383139945912931021 7739487143677479717349133)
                  ·
                    refine ⟨2902307678879054894005925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7739487143677479717349133 2902307678879054894005925)
                    ·
                      refine ⟨544182689789822792626111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2902307678879054894005925 544182689789822792626111)
                      ·
                        rfl

theorem cell23_1059792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_1059792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059792 prefixEnd_1059792 := by exact prefixLift 1059792
  have htrace : WordTrace (prefixWord ++ tailWord_1059792) baseStart_1059792 baseEnd_1059792 := by
    simpa [prefixWord, tailWord_1059792, baseEnd_1059792] using wordTrace_append hprefix tailTrace_1059792
  have hstable : (prefixWord ++ tailWord_1059792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059792).length < 2 ^ (prefixWord ++ tailWord_1059792).sum := by decide
  have hdescent : baseEnd_1059792 < baseStart_1059792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059796 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_1059796 : Nat := 118140960795 + 1059796 * 2 ^ 59
def prefixEnd_1059796 : Nat := 4983230072969 + 3 ^ 40 * 1059796 * 2
def baseEnd_1059796 : Nat := 544184743712440776976093

theorem tailTrace_1059796 : CollatzResearch.WordTrace tailWord_1059796 prefixEnd_1059796 544184743712440776976093 := by
  unfold tailWord_1059796
  simp only [CollatzResearch.WordTrace]
  refine ⟨19326967834273782795931621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25769290445698377061242161 19326967834273782795931621)
  ·
    refine ⟨3623806468926334274237179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19326967834273782795931621 3623806468926334274237179)
    ·
      refine ⟨5435709703389501411355769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3623806468926334274237179 5435709703389501411355769)
      ·
        refine ⟨4076782277542126058516827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5435709703389501411355769 4076782277542126058516827)
        ·
          refine ⟨6115173416313189087775241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4076782277542126058516827 6115173416313189087775241)
          ·
            refine ⟨4586380062234891815831431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6115173416313189087775241 4586380062234891815831431)
            ·
              refine ⟨6879570093352337723747147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4586380062234891815831431 6879570093352337723747147)
              ·
                refine ⟨10319355140028506585620721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6879570093352337723747147 10319355140028506585620721)
                ·
                  refine ⟨7739516355021379939215541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10319355140028506585620721 7739516355021379939215541)
                  ·
                    refine ⟨725579658283254369301457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7739516355021379939215541 725579658283254369301457)
                    ·
                      refine ⟨544184743712440776976093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 725579658283254369301457 544184743712440776976093)
                      ·
                        rfl

theorem cell23_1059796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_1059796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059796 prefixEnd_1059796 := by exact prefixLift 1059796
  have htrace : WordTrace (prefixWord ++ tailWord_1059796) baseStart_1059796 baseEnd_1059796 := by
    simpa [prefixWord, tailWord_1059796, baseEnd_1059796] using wordTrace_append hprefix tailTrace_1059796
  have hstable : (prefixWord ++ tailWord_1059796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059796).length < 2 ^ (prefixWord ++ tailWord_1059796).sum := by decide
  have hdescent : baseEnd_1059796 < baseStart_1059796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059832 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 8]
def baseStart_1059832 : Nat := 118140960795 + 1059832 * 2 ^ 59
def prefixEnd_1059832 : Nat := 4983230072969 + 3 ^ 40 * 1059832 * 2
def baseEnd_1059832 : Nat := 60467025446222515125103

theorem tailTrace_1059832 : CollatzResearch.WordTrace tailWord_1059832 prefixEnd_1059832 60467025446222515125103 := by
  unfold tailWord_1059832
  simp only [CollatzResearch.WordTrace]
  refine ⟨19327624348208571870086875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25770165797611429160115833 19327624348208571870086875)
  ·
    refine ⟨28991436522312857805130313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19327624348208571870086875 28991436522312857805130313)
    ·
      refine ⟨21743577391734643353847735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28991436522312857805130313 21743577391734643353847735)
      ·
        refine ⟨32615366087601965030771603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21743577391734643353847735 32615366087601965030771603)
        ·
          refine ⟨48923049131402947546157405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32615366087601965030771603 48923049131402947546157405)
          ·
            refine ⟨18346143424276105329809027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48923049131402947546157405 18346143424276105329809027)
            ·
              refine ⟨27519215136414157994713541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18346143424276105329809027 27519215136414157994713541)
              ·
                refine ⟨5159852838077654624008789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27519215136414157994713541 5159852838077654624008789)
                ·
                  refine ⟨60467025446222515125103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5159852838077654624008789 60467025446222515125103)
                  ·
                    rfl

theorem cell23_1059832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 8].length) (baseStart_1059832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059832 prefixEnd_1059832 := by exact prefixLift 1059832
  have htrace : WordTrace (prefixWord ++ tailWord_1059832) baseStart_1059832 baseEnd_1059832 := by
    simpa [prefixWord, tailWord_1059832, baseEnd_1059832] using wordTrace_append hprefix tailTrace_1059832
  have hstable : (prefixWord ++ tailWord_1059832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059832).length < 2 ^ (prefixWord ++ tailWord_1059832).sum := by decide
  have hdescent : baseEnd_1059832 < baseStart_1059832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059866 : List Nat := [3, 1, 1, 3, 1, 2, 5, 1, 6]
def baseStart_1059866 : Nat := 118140960795 + 1059866 * 2 ^ 59
def prefixEnd_1059866 : Nat := 4983230072969 + 3 ^ 40 * 1059866 * 2
def baseEnd_1059866 : Nat := 60468965262028389233419

theorem tailTrace_1059866 : CollatzResearch.WordTrace tailWord_1059866 prefixEnd_1059866 60468965262028389233419 := by
  unfold tailWord_1059866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9664122194573491886727863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25770992518862645031274301 9664122194573491886727863)
  ·
    refine ⟨14496183291860237830091795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9664122194573491886727863 14496183291860237830091795)
    ·
      refine ⟨21744274937790356745137693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14496183291860237830091795 21744274937790356745137693)
      ·
        refine ⟨8154103101671383779426635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21744274937790356745137693 8154103101671383779426635)
        ·
          refine ⟨12231154652507075669139953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8154103101671383779426635 12231154652507075669139953)
          ·
            refine ⟨9173365989380306751854965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12231154652507075669139953 9173365989380306751854965)
            ·
              refine ⟨860003061504403757986403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9173365989380306751854965 860003061504403757986403)
              ·
                refine ⟨1290004592256605636979605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860003061504403757986403 1290004592256605636979605)
                ·
                  refine ⟨60468965262028389233419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1290004592256605636979605 60468965262028389233419)
                  ·
                    rfl

theorem cell23_1059866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 6].length) (baseStart_1059866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059866 prefixEnd_1059866 := by exact prefixLift 1059866
  have htrace : WordTrace (prefixWord ++ tailWord_1059866) baseStart_1059866 baseEnd_1059866 := by
    simpa [prefixWord, tailWord_1059866, baseEnd_1059866] using wordTrace_append hprefix tailTrace_1059866
  have hstable : (prefixWord ++ tailWord_1059866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059866).length < 2 ^ (prefixWord ++ tailWord_1059866).sum := by decide
  have hdescent : baseEnd_1059866 < baseStart_1059866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059896 : List Nat := [2, 1, 2, 1, 5, 1, 2, 3, 1, 5]
def baseStart_1059896 : Nat := 118140960795 + 1059896 * 2 ^ 59
def prefixEnd_1059896 : Nat := 4983230072969 + 3 ^ 40 * 1059896 * 2
def baseEnd_1059896 : Nat := 181412030592630128575211

theorem tailTrace_1059896 : CollatzResearch.WordTrace tailWord_1059896 prefixEnd_1059896 181412030592630128575211 := by
  unfold tailWord_1059896
  simp only [CollatzResearch.WordTrace]
  refine ⟨19328791484092641335251771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25771721978790188447002361 19328791484092641335251771)
  ·
    refine ⟨28993187226138962002877657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19328791484092641335251771 28993187226138962002877657)
    ·
      refine ⟨21744890419604221502158243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28993187226138962002877657 21744890419604221502158243)
      ·
        refine ⟨32617335629406332253237365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21744890419604221502158243 32617335629406332253237365)
        ·
          refine ⟨3057875215256843648741003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32617335629406332253237365 3057875215256843648741003)
          ·
            refine ⟨4586812822885265473111505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3057875215256843648741003 4586812822885265473111505)
            ·
              refine ⟨3440109617163949104833629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4586812822885265473111505 3440109617163949104833629)
              ·
                refine ⟨1290041106436480914312611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3440109617163949104833629 1290041106436480914312611)
                ·
                  refine ⟨1935061659654721371468917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290041106436480914312611 1935061659654721371468917)
                  ·
                    refine ⟨181412030592630128575211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1935061659654721371468917 181412030592630128575211)
                    ·
                      rfl

theorem cell23_1059896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_1059896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059896 prefixEnd_1059896 := by exact prefixLift 1059896
  have htrace : WordTrace (prefixWord ++ tailWord_1059896) baseStart_1059896 baseEnd_1059896 := by
    simpa [prefixWord, tailWord_1059896, baseEnd_1059896] using wordTrace_append hprefix tailTrace_1059896
  have hstable : (prefixWord ++ tailWord_1059896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059896).length < 2 ^ (prefixWord ++ tailWord_1059896).sum := by decide
  have hdescent : baseEnd_1059896 < baseStart_1059896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059936 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 3]
def baseStart_1059936 : Nat := 118140960795 + 1059936 * 2 ^ 59
def prefixEnd_1059936 : Nat := 4983230072969 + 3 ^ 40 * 1059936 * 2
def baseEnd_1059936 : Nat := 544256631004070229225449

theorem tailTrace_1059936 : CollatzResearch.WordTrace tailWord_1059936 prefixEnd_1059936 544256631004070229225449 := by
  unfold tailWord_1059936
  simp only [CollatzResearch.WordTrace]
  refine ⟨19329520944020184750979831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25772694592026913001306441 19329520944020184750979831)
  ·
    refine ⟨28994281416030277126469747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19329520944020184750979831 28994281416030277126469747)
    ·
      refine ⟨43491422124045415689704621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28994281416030277126469747 43491422124045415689704621)
      ·
        refine ⟨16309283296517030883639233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43491422124045415689704621 16309283296517030883639233)
        ·
          refine ⟨12231962472387773162729425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16309283296517030883639233 12231962472387773162729425)
          ·
            refine ⟨9173971854290829872047069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12231962472387773162729425 9173971854290829872047069)
            ·
              refine ⟨3440239445359061202017651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9173971854290829872047069 3440239445359061202017651)
              ·
                refine ⟨5160359168038591803026477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3440239445359061202017651 5160359168038591803026477)
                ·
                  refine ⟨1935134688014471926134929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5160359168038591803026477 1935134688014471926134929)
                  ·
                    refine ⟨1451351016010853944601197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1935134688014471926134929 1451351016010853944601197)
                    ·
                      refine ⟨544256631004070229225449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1451351016010853944601197 544256631004070229225449)
                      ·
                        rfl

theorem cell23_1059936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_1059936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059936 prefixEnd_1059936 := by exact prefixLift 1059936
  have htrace : WordTrace (prefixWord ++ tailWord_1059936) baseStart_1059936 baseEnd_1059936 := by
    simpa [prefixWord, tailWord_1059936, baseEnd_1059936] using wordTrace_append hprefix tailTrace_1059936
  have hstable : (prefixWord ++ tailWord_1059936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059936).length < 2 ^ (prefixWord ++ tailWord_1059936).sum := by decide
  have hdescent : baseEnd_1059936 < baseStart_1059936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059946 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1059946 : Nat := 118140960795 + 1059946 * 2 ^ 59
def prefixEnd_1059946 : Nat := 4983230072969 + 3 ^ 40 * 1059946 * 2
def baseEnd_1059946 : Nat := 544261765810615190100403

theorem tailTrace_1059946 : CollatzResearch.WordTrace tailWord_1059946 prefixEnd_1059946 544261765810615190100403 := by
  unfold tailWord_1059946
  simp only [CollatzResearch.WordTrace]
  refine ⟨9664851654501035302455923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25772937745336094139882461 9664851654501035302455923)
  ·
    refine ⟨14497277481751552953683885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9664851654501035302455923 14497277481751552953683885)
    ·
      refine ⟨5436479055656832357631457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14497277481751552953683885 5436479055656832357631457)
      ·
        refine ⟨4077359291742624268223593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5436479055656832357631457 4077359291742624268223593)
        ·
          refine ⟨3058019468806968201167695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4077359291742624268223593 3058019468806968201167695)
          ·
            refine ⟨4587029203210452301751543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3058019468806968201167695 4587029203210452301751543)
            ·
              refine ⟨6880543804815678452627315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4587029203210452301751543 6880543804815678452627315)
              ·
                refine ⟨10320815707223517678940973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6880543804815678452627315 10320815707223517678940973)
                ·
                  refine ⟨3870305890208819129602865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10320815707223517678940973 3870305890208819129602865)
                  ·
                    refine ⟨2902729417656614347202149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3870305890208819129602865 2902729417656614347202149)
                    ·
                      refine ⟨544261765810615190100403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2902729417656614347202149 544261765810615190100403)
                      ·
                        rfl

theorem cell23_1059946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1059946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059946 prefixEnd_1059946 := by exact prefixLift 1059946
  have htrace : WordTrace (prefixWord ++ tailWord_1059946) baseStart_1059946 baseEnd_1059946 := by
    simpa [prefixWord, tailWord_1059946, baseEnd_1059946] using wordTrace_append hprefix tailTrace_1059946
  have hstable : (prefixWord ++ tailWord_1059946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059946).length < 2 ^ (prefixWord ++ tailWord_1059946).sum := by decide
  have hdescent : baseEnd_1059946 < baseStart_1059946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059950 : List Nat := [4, 1, 2, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_1059950 : Nat := 118140960795 + 1059950 * 2 ^ 59
def prefixEnd_1059950 : Nat := 4983230072969 + 3 ^ 40 * 1059950 * 2
def baseEnd_1059950 : Nat := 544263819733233174450385

theorem tailTrace_1059950 : CollatzResearch.WordTrace tailWord_1059950 prefixEnd_1059950 544263819733233174450385 := by
  unfold tailWord_1059950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4832444063748706236621163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25773035006659766595312869 4832444063748706236621163)
  ·
    refine ⟨7248666095623059354931745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4832444063748706236621163 7248666095623059354931745)
    ·
      refine ⟨5436499571717294516198809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7248666095623059354931745 5436499571717294516198809)
      ·
        refine ⟨4077374678787970887149107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5436499571717294516198809 4077374678787970887149107)
        ·
          refine ⟨6116062018181956330723661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4077374678787970887149107 6116062018181956330723661)
          ·
            refine ⟨2293523256818233624021373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6116062018181956330723661 2293523256818233624021373)
            ·
              refine ⟨860071221306837609008015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2293523256818233624021373 860071221306837609008015)
              ·
                refine ⟨1290106831960256413512023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860071221306837609008015 1290106831960256413512023)
                ·
                  refine ⟨1935160247940384620268035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290106831960256413512023 1935160247940384620268035)
                  ·
                    refine ⟨2902740371910576930402053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1935160247940384620268035 2902740371910576930402053)
                    ·
                      refine ⟨544263819733233174450385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2902740371910576930402053 544263819733233174450385)
                      ·
                        rfl

theorem cell23_1059950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_1059950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059950 prefixEnd_1059950 := by exact prefixLift 1059950
  have htrace : WordTrace (prefixWord ++ tailWord_1059950) baseStart_1059950 baseEnd_1059950 := by
    simpa [prefixWord, tailWord_1059950, baseEnd_1059950] using wordTrace_append hprefix tailTrace_1059950
  have hstable : (prefixWord ++ tailWord_1059950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059950).length < 2 ^ (prefixWord ++ tailWord_1059950).sum := by decide
  have hdescent : baseEnd_1059950 < baseStart_1059950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1059973 : List Nat := [1, 3, 1, 1, 7, 1, 1, 8]
def baseStart_1059973 : Nat := 118140960795 + 1059973 * 2 ^ 59
def prefixEnd_1059973 : Nat := 4983230072969 + 3 ^ 40 * 1059973 * 2
def baseEnd_1059973 : Nat := 20158356658825429054177

theorem tailTrace_1059973 : CollatzResearch.WordTrace tailWord_1059973 prefixEnd_1059973 20158356658825429054177 := by
  unfold tailWord_1059973
  simp only [CollatzResearch.WordTrace]
  refine ⟨38660391388906324821056573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25773594259270883214037715 38660391388906324821056573)
  ·
    refine ⟨14497646770839871807896215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38660391388906324821056573 14497646770839871807896215)
    ·
      refine ⟨21746470156259807711844323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14497646770839871807896215 21746470156259807711844323)
      ·
        refine ⟨32619705234389711567766485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21746470156259807711844323 32619705234389711567766485)
        ·
          refine ⟨764524341431008864869527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 32619705234389711567766485 764524341431008864869527)
          ·
            refine ⟨1146786512146513297304291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764524341431008864869527 1146786512146513297304291)
            ·
              refine ⟨1720179768219769945956437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146786512146513297304291 1720179768219769945956437)
              ·
                refine ⟨20158356658825429054177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1720179768219769945956437 20158356658825429054177)
                ·
                  rfl

theorem cell23_1059973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 8].length) (baseStart_1059973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1059973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1059973 prefixEnd_1059973 := by exact prefixLift 1059973
  have htrace : WordTrace (prefixWord ++ tailWord_1059973) baseStart_1059973 baseEnd_1059973 := by
    simpa [prefixWord, tailWord_1059973, baseEnd_1059973] using wordTrace_append hprefix tailTrace_1059973
  have hstable : (prefixWord ++ tailWord_1059973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1059973).length < 2 ^ (prefixWord ++ tailWord_1059973).sum := by decide
  have hdescent : baseEnd_1059973 < baseStart_1059973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1059973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060017 : List Nat := [1, 2, 2, 5, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1060017 : Nat := 118140960795 + 1060017 * 2 ^ 59
def prefixEnd_1060017 : Nat := 4983230072969 + 3 ^ 40 * 1060017 * 2
def baseEnd_1060017 : Nat := 544298222937084412312577

theorem tailTrace_1060017 : CollatzResearch.WordTrace tailWord_1060017 prefixEnd_1060017 544298222937084412312577 := by
  unfold tailWord_1060017
  simp only [CollatzResearch.WordTrace]
  refine ⟨38661996200746920335658305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25774664133831280223772203 38661996200746920335658305)
  ·
    refine ⟨28996497150560190251743729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38661996200746920335658305 28996497150560190251743729)
    ·
      refine ⟨21747372862920142688807797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28996497150560190251743729 21747372862920142688807797)
      ·
        refine ⟨2038816205898763377075731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21747372862920142688807797 2038816205898763377075731)
        ·
          refine ⟨3058224308848145065613597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2038816205898763377075731 3058224308848145065613597)
          ·
            refine ⟨1146834115818054399605099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3058224308848145065613597 1146834115818054399605099)
            ·
              refine ⟨1720251173727081599407649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146834115818054399605099 1720251173727081599407649)
              ·
                refine ⟨1290188380295311199555737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1720251173727081599407649 1290188380295311199555737)
                ·
                  refine ⟨967641285221483399666803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1290188380295311199555737 967641285221483399666803)
                  ·
                    refine ⟨1451461927832225099500205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 967641285221483399666803 1451461927832225099500205)
                    ·
                      refine ⟨544298222937084412312577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1451461927832225099500205 544298222937084412312577)
                      ·
                        rfl

theorem cell23_1060017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1060017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060017 prefixEnd_1060017 := by exact prefixLift 1060017
  have htrace : WordTrace (prefixWord ++ tailWord_1060017) baseStart_1060017 baseEnd_1060017 := by
    simpa [prefixWord, tailWord_1060017, baseEnd_1060017] using wordTrace_append hprefix tailTrace_1060017
  have hstable : (prefixWord ++ tailWord_1060017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060017).length < 2 ^ (prefixWord ++ tailWord_1060017).sum := by decide
  have hdescent : baseEnd_1060017 < baseStart_1060017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060033 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1060033 : Nat := 118140960795 + 1060033 * 2 ^ 59
def prefixEnd_1060033 : Nat := 4983230072969 + 3 ^ 40 * 1060033 * 2
def baseEnd_1060033 : Nat := 181435479542518783237501

theorem tailTrace_1060033 : CollatzResearch.WordTrace tailWord_1060033 prefixEnd_1060033 181435479542518783237501 := by
  unfold tailWord_1060033
  simp only [CollatzResearch.WordTrace]
  refine ⟨38662579768688955068240753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25775053179125970045493835 38662579768688955068240753)
  ·
    refine ⟨28996934826516716301180565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38662579768688955068240753 28996934826516716301180565)
    ·
      refine ⟨1359231319992971076617839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28996934826516716301180565 1359231319992971076617839)
      ·
        refine ⟨2038846979989456614926759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359231319992971076617839 2038846979989456614926759)
        ·
          refine ⟨3058270469984184922390139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2038846979989456614926759 3058270469984184922390139)
          ·
            refine ⟨4587405704976277383585209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3058270469984184922390139 4587405704976277383585209)
            ·
              refine ⟨3440554278732208037688907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4587405704976277383585209 3440554278732208037688907)
              ·
                refine ⟨5160831418098312056533361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3440554278732208037688907 5160831418098312056533361)
                ·
                  refine ⟨3870623563573734042400021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5160831418098312056533361 3870623563573734042400021)
                  ·
                    refine ⟨181435479542518783237501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3870623563573734042400021 181435479542518783237501)
                    ·
                      rfl

theorem cell23_1060033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1060033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060033 prefixEnd_1060033 := by exact prefixLift 1060033
  have htrace : WordTrace (prefixWord ++ tailWord_1060033) baseStart_1060033 baseEnd_1060033 := by
    simpa [prefixWord, tailWord_1060033, baseEnd_1060033] using wordTrace_append hprefix tailTrace_1060033
  have hstable : (prefixWord ++ tailWord_1060033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060033).length < 2 ^ (prefixWord ++ tailWord_1060033).sum := by decide
  have hdescent : baseEnd_1060033 < baseStart_1060033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060034 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_1060034 : Nat := 118140960795 + 1060034 * 2 ^ 59
def prefixEnd_1060034 : Nat := 4983230072969 + 3 ^ 40 * 1060034 * 2
def baseEnd_1060034 : Nat := 544306952108210845799999

theorem tailTrace_1060034 : CollatzResearch.WordTrace tailWord_1060034 prefixEnd_1060034 544306952108210845799999 := by
  unfold tailWord_1060034
  simp only [CollatzResearch.WordTrace]
  refine ⟨9665654060421333059756789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25775077494456888159351437 9665654060421333059756789)
  ·
    refine ⟨906155068164499974352199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9665654060421333059756789 906155068164499974352199)
    ·
      refine ⟨1359232602246749961528299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 906155068164499974352199 1359232602246749961528299)
      ·
        refine ⟨2038848903370124942292449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359232602246749961528299 2038848903370124942292449)
        ·
          refine ⟨1529136677527593706719337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2038848903370124942292449 1529136677527593706719337)
          ·
            refine ⟨1146852508145695280039503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1529136677527593706719337 1146852508145695280039503)
            ·
              refine ⟨1720278762218542920059255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1146852508145695280039503 1720278762218542920059255)
              ·
                refine ⟨2580418143327814380088883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1720278762218542920059255 2580418143327814380088883)
                ·
                  refine ⟨3870627214991721570133325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2580418143327814380088883 3870627214991721570133325)
                  ·
                    refine ⟨1451485205621895588799997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3870627214991721570133325 1451485205621895588799997)
                    ·
                      refine ⟨544306952108210845799999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1451485205621895588799997 544306952108210845799999)
                      ·
                        rfl

theorem cell23_1060034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_1060034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060034 prefixEnd_1060034 := by exact prefixLift 1060034
  have htrace : WordTrace (prefixWord ++ tailWord_1060034) baseStart_1060034 baseEnd_1060034 := by
    simpa [prefixWord, tailWord_1060034, baseEnd_1060034] using wordTrace_append hprefix tailTrace_1060034
  have hstable : (prefixWord ++ tailWord_1060034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060034).length < 2 ^ (prefixWord ++ tailWord_1060034).sum := by decide
  have hdescent : baseEnd_1060034 < baseStart_1060034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060039 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_1060039 : Nat := 118140960795 + 1060039 * 2 ^ 59
def prefixEnd_1060039 : Nat := 4983230072969 + 3 ^ 40 * 1060039 * 2
def baseEnd_1060039 : Nat := 544309519511483326237475

theorem tailTrace_1060039 : CollatzResearch.WordTrace tailWord_1060039 prefixEnd_1060039 544309519511483326237475 := by
  unfold tailWord_1060039
  simp only [CollatzResearch.WordTrace]
  refine ⟨38662798606667218092959171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25775199071111478728639447 38662798606667218092959171)
  ·
    refine ⟨57994197910000827139438757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38662798606667218092959171 57994197910000827139438757)
    ·
      refine ⟨10873912108125155088644767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57994197910000827139438757 10873912108125155088644767)
      ·
        refine ⟨16310868162187732632967151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10873912108125155088644767 16310868162187732632967151)
        ·
          refine ⟨24466302243281598949450727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16310868162187732632967151 24466302243281598949450727)
          ·
            refine ⟨36699453364922398424176091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24466302243281598949450727 36699453364922398424176091)
            ·
              refine ⟨55049180047383597636264137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36699453364922398424176091 55049180047383597636264137)
              ·
                refine ⟨41286885035537698227198103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55049180047383597636264137 41286885035537698227198103)
                ·
                  refine ⟨61930327553306547340797155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41286885035537698227198103 61930327553306547340797155)
                  ·
                    refine ⟨92895491329959821011195733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61930327553306547340797155 92895491329959821011195733)
                    ·
                      refine ⟨544309519511483326237475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 92895491329959821011195733 544309519511483326237475)
                      ·
                        rfl

theorem cell23_1060039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_1060039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060039 prefixEnd_1060039 := by exact prefixLift 1060039
  have htrace : WordTrace (prefixWord ++ tailWord_1060039) baseStart_1060039 baseEnd_1060039 := by
    simpa [prefixWord, tailWord_1060039, baseEnd_1060039] using wordTrace_append hprefix tailTrace_1060039
  have hstable : (prefixWord ++ tailWord_1060039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060039).length < 2 ^ (prefixWord ++ tailWord_1060039).sum := by decide
  have hdescent : baseEnd_1060039 < baseStart_1060039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060040 : List Nat := [2, 1, 3, 1, 2, 1, 2, 5, 2, 2, 2]
def baseStart_1060040 : Nat := 118140960795 + 1060040 * 2 ^ 59
def prefixEnd_1060040 : Nat := 4983230072969 + 3 ^ 40 * 1060040 * 2
def baseEnd_1060040 : Nat := 544310032992137822324971

theorem tailTrace_1060040 : CollatzResearch.WordTrace tailWord_1060040 prefixEnd_1060040 544310032992137822324971 := by
  unfold tailWord_1060040
  simp only [CollatzResearch.WordTrace]
  refine ⟨19331417539831797631872787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25775223386442396842497049 19331417539831797631872787)
  ·
    refine ⟨28997126309747696447809181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19331417539831797631872787 28997126309747696447809181)
    ·
      refine ⟨10873922366155386167928443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28997126309747696447809181 10873922366155386167928443)
      ·
        refine ⟨16310883549233079251892665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10873922366155386167928443 16310883549233079251892665)
        ·
          refine ⟨12233162661924809438919499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16310883549233079251892665 12233162661924809438919499)
          ·
            refine ⟨18349743992887214158379249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12233162661924809438919499 18349743992887214158379249)
            ·
              refine ⟨13762307994665410618784437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18349743992887214158379249 13762307994665410618784437)
              ·
                refine ⟨1290216374499882245511041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13762307994665410618784437 1290216374499882245511041)
                ·
                  refine ⟨967662280874911684133281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1290216374499882245511041 967662280874911684133281)
                  ·
                    refine ⟨725746710656183763099961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 967662280874911684133281 725746710656183763099961)
                    ·
                      refine ⟨544310032992137822324971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 725746710656183763099961 544310032992137822324971)
                      ·
                        rfl

theorem cell23_1060040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_1060040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060040 prefixEnd_1060040 := by exact prefixLift 1060040
  have htrace : WordTrace (prefixWord ++ tailWord_1060040) baseStart_1060040 baseEnd_1060040 := by
    simpa [prefixWord, tailWord_1060040, baseEnd_1060040] using wordTrace_append hprefix tailTrace_1060040
  have hstable : (prefixWord ++ tailWord_1060040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060040).length < 2 ^ (prefixWord ++ tailWord_1060040).sum := by decide
  have hdescent : baseEnd_1060040 < baseStart_1060040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060059 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 5, 7]
def baseStart_1060059 : Nat := 118140960795 + 1060059 * 2 ^ 59
def prefixEnd_1060059 : Nat := 4983230072969 + 3 ^ 40 * 1060059 * 2
def baseEnd_1060059 : Nat := 181439929708191082662461

theorem tailTrace_1060059 : CollatzResearch.WordTrace tailWord_1060059 prefixEnd_1060059 181439929708191082662461 := by
  unfold tailWord_1060059
  simp only [CollatzResearch.WordTrace]
  refine ⟨38663528066594761508687231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25775685377729841005791487 38663528066594761508687231)
  ·
    refine ⟨57995292099892142263030847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38663528066594761508687231 57995292099892142263030847)
    ·
      refine ⟨86992938149838213394546271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57995292099892142263030847 86992938149838213394546271)
      ·
        refine ⟨130489407224757320091819407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86992938149838213394546271 130489407224757320091819407)
        ·
          refine ⟨195734110837135980137729111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130489407224757320091819407 195734110837135980137729111)
          ·
            refine ⟨293601166255703970206593667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195734110837135980137729111 293601166255703970206593667)
            ·
              refine ⟨440401749383555955309890501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293601166255703970206593667 440401749383555955309890501)
              ·
                refine ⟨82575328009416741620604469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 440401749383555955309890501 82575328009416741620604469)
                ·
                  refine ⟨7741437000882819526931669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82575328009416741620604469 7741437000882819526931669)
                  ·
                    refine ⟨181439929708191082662461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7741437000882819526931669 181439929708191082662461)
                    ·
                      rfl

theorem cell23_1060059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 7].length) (baseStart_1060059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060059 prefixEnd_1060059 := by exact prefixLift 1060059
  have htrace : WordTrace (prefixWord ++ tailWord_1060059) baseStart_1060059 baseEnd_1060059 := by
    simpa [prefixWord, tailWord_1060059, baseEnd_1060059] using wordTrace_append hprefix tailTrace_1060059
  have hstable : (prefixWord ++ tailWord_1060059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060059).length < 2 ^ (prefixWord ++ tailWord_1060059).sum := by decide
  have hdescent : baseEnd_1060059 < baseStart_1060059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060063 : List Nat := [1, 1, 2, 3, 2, 1, 5, 3, 5]
def baseStart_1060063 : Nat := 118140960795 + 1060063 * 2 ^ 59
def prefixEnd_1060063 : Nat := 4983230072969 + 3 ^ 40 * 1060063 * 2
def baseEnd_1060063 : Nat := 60480204783021248037485

theorem tailTrace_1060063 : CollatzResearch.WordTrace tailWord_1060063 prefixEnd_1060063 60480204783021248037485 := by
  unfold tailWord_1060063
  simp only [CollatzResearch.WordTrace]
  refine ⟨38663673958580270191832843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25775782639053513461221895 38663673958580270191832843)
  ·
    refine ⟨57995510937870405287749265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38663673958580270191832843 57995510937870405287749265)
    ·
      refine ⟨43496633203402803965811949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57995510937870405287749265 43496633203402803965811949)
      ·
        refine ⟨16311237451276051487179481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43496633203402803965811949 16311237451276051487179481)
        ·
          refine ⟨12233428088457038615384611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16311237451276051487179481 12233428088457038615384611)
          ·
            refine ⟨18350142132685557923076917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12233428088457038615384611 18350142132685557923076917)
            ·
              refine ⟨1720325824939271055288461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18350142132685557923076917 1720325824939271055288461)
              ·
                refine ⟨645122184352226645733173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1720325824939271055288461 645122184352226645733173)
                ·
                  refine ⟨60480204783021248037485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 645122184352226645733173 60480204783021248037485)
                  ·
                    rfl

theorem cell23_1060063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 5].length) (baseStart_1060063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060063 prefixEnd_1060063 := by exact prefixLift 1060063
  have htrace : WordTrace (prefixWord ++ tailWord_1060063) baseStart_1060063 baseEnd_1060063 := by
    simpa [prefixWord, tailWord_1060063, baseEnd_1060063] using wordTrace_append hprefix tailTrace_1060063
  have hstable : (prefixWord ++ tailWord_1060063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060063).length < 2 ^ (prefixWord ++ tailWord_1060063).sum := by decide
  have hdescent : baseEnd_1060063 < baseStart_1060063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060076 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 4, 5]
def baseStart_1060076 : Nat := 118140960795 + 1060076 * 2 ^ 59
def prefixEnd_1060076 : Nat := 4983230072969 + 3 ^ 40 * 1060076 * 2
def baseEnd_1060076 : Nat := 181442839431899893824935

theorem tailTrace_1060076 : CollatzResearch.WordTrace tailWord_1060076 prefixEnd_1060076 181442839431899893824935 := by
  unfold tailWord_1060076
  simp only [CollatzResearch.WordTrace]
  refine ⟨19332074053766586706028041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25776098738355448941370721 19332074053766586706028041)
  ·
    refine ⟨14499055540324940029521031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19332074053766586706028041 14499055540324940029521031)
    ·
      refine ⟨21748583310487410044281547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14499055540324940029521031 21748583310487410044281547)
      ·
        refine ⟨32622874965731115066422321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21748583310487410044281547 32622874965731115066422321)
        ·
          refine ⟨24467156224298336299816741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32622874965731115066422321 24467156224298336299816741)
          ·
            refine ⟨4587591792055938056215639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24467156224298336299816741 4587591792055938056215639)
            ·
              refine ⟨6881387688083907084323459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4587591792055938056215639 6881387688083907084323459)
              ·
                refine ⟨10322081532125860626485189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6881387688083907084323459 10322081532125860626485189)
                ·
                  refine ⟨1935390287273598867465973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10322081532125860626485189 1935390287273598867465973)
                  ·
                    refine ⟨181442839431899893824935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1935390287273598867465973 181442839431899893824935)
                    ·
                      rfl

theorem cell23_1060076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_1060076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060076 prefixEnd_1060076 := by exact prefixLift 1060076
  have htrace : WordTrace (prefixWord ++ tailWord_1060076) baseStart_1060076 baseEnd_1060076 := by
    simpa [prefixWord, tailWord_1060076, baseEnd_1060076] using wordTrace_append hprefix tailTrace_1060076
  have hstable : (prefixWord ++ tailWord_1060076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060076).length < 2 ^ (prefixWord ++ tailWord_1060076).sum := by decide
  have hdescent : baseEnd_1060076 < baseStart_1060076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060096 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 4]
def baseStart_1060096 : Nat := 118140960795 + 1060096 * 2 ^ 59
def prefixEnd_1060096 : Nat := 4983230072969 + 3 ^ 40 * 1060096 * 2
def baseEnd_1060096 : Nat := 544338787908789603224713

theorem tailTrace_1060096 : CollatzResearch.WordTrace tailWord_1060096 prefixEnd_1060096 544338787908789603224713 := by
  unfold tailWord_1060096
  simp only [CollatzResearch.WordTrace]
  refine ⟨19332438783730358413892071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25776585044973811218522761 19332438783730358413892071)
  ·
    refine ⟨28998658175595537620838107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19332438783730358413892071 28998658175595537620838107)
    ·
      refine ⟨43497987263393306431257161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28998658175595537620838107 43497987263393306431257161)
      ·
        refine ⟨32623490447544979823442871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43497987263393306431257161 32623490447544979823442871)
        ·
          refine ⟨48935235671317469735164307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32623490447544979823442871 48935235671317469735164307)
          ·
            refine ⟨73402853506976204602746461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48935235671317469735164307 73402853506976204602746461)
            ·
              refine ⟨27526070065116076726029923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73402853506976204602746461 27526070065116076726029923)
              ·
                refine ⟨41289105097674115089044885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27526070065116076726029923 41289105097674115089044885)
                ·
                  refine ⟨1935426801453474144798979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41289105097674115089044885 1935426801453474144798979)
                  ·
                    refine ⟨2903140202180211217198469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1935426801453474144798979 2903140202180211217198469)
                    ·
                      refine ⟨544338787908789603224713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2903140202180211217198469 544338787908789603224713)
                      ·
                        rfl

theorem cell23_1060096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_1060096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060096 prefixEnd_1060096 := by exact prefixLift 1060096
  have htrace : WordTrace (prefixWord ++ tailWord_1060096) baseStart_1060096 baseEnd_1060096 := by
    simpa [prefixWord, tailWord_1060096, baseEnd_1060096] using wordTrace_append hprefix tailTrace_1060096
  have hstable : (prefixWord ++ tailWord_1060096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060096).length < 2 ^ (prefixWord ++ tailWord_1060096).sum := by decide
  have hdescent : baseEnd_1060096 < baseStart_1060096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060113 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 4]
def baseStart_1060113 : Nat := 118140960795 + 1060113 * 2 ^ 59
def prefixEnd_1060113 : Nat := 4983230072969 + 3 ^ 40 * 1060113 * 2
def baseEnd_1060113 : Nat := 544347517079916036712135

theorem tailTrace_1060113 : CollatzResearch.WordTrace tailWord_1060113 prefixEnd_1060113 544347517079916036712135 := by
  unfold tailWord_1060113
  simp only [CollatzResearch.WordTrace]
  refine ⟨38665497608399128731152993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25776998405599419154101995 38665497608399128731152993)
  ·
    refine ⟨28999123206299346548364745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38665497608399128731152993 28999123206299346548364745)
    ·
      refine ⟨21749342404724509911273559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28999123206299346548364745 21749342404724509911273559)
      ·
        refine ⟨32624013607086764866910339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21749342404724509911273559 32624013607086764866910339)
        ·
          refine ⟨48936020410630147300365509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32624013607086764866910339 48936020410630147300365509)
          ·
            refine ⟨9175503826993152618818533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48936020410630147300365509 9175503826993152618818533)
            ·
              refine ⟨1720406967561216116028475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9175503826993152618818533 1720406967561216116028475)
              ·
                refine ⟨2580610451341824174042713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1720406967561216116028475 2580610451341824174042713)
                ·
                  refine ⟨1935457838506368130532035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2580610451341824174042713 1935457838506368130532035)
                  ·
                    refine ⟨2903186757759552195798053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1935457838506368130532035 2903186757759552195798053)
                    ·
                      refine ⟨544347517079916036712135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2903186757759552195798053 544347517079916036712135)
                      ·
                        rfl

theorem cell23_1060113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_1060113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060113 prefixEnd_1060113 := by exact prefixLift 1060113
  have htrace : WordTrace (prefixWord ++ tailWord_1060113) baseStart_1060113 baseEnd_1060113 := by
    simpa [prefixWord, tailWord_1060113, baseEnd_1060113] using wordTrace_append hprefix tailTrace_1060113
  have hstable : (prefixWord ++ tailWord_1060113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060113).length < 2 ^ (prefixWord ++ tailWord_1060113).sum := by decide
  have hdescent : baseEnd_1060113 < baseStart_1060113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060157 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_1060157 : Nat := 118140960795 + 1060157 * 2 ^ 59
def prefixEnd_1060157 : Nat := 4983230072969 + 3 ^ 40 * 1060157 * 2
def baseEnd_1060157 : Nat := 181456703409571288187311

theorem tailTrace_1060157 : CollatzResearch.WordTrace tailWord_1060157 prefixEnd_1060157 181456703409571288187311 := by
  unfold tailWord_1060157
  simp only [CollatzResearch.WordTrace]
  refine ⟨38667102420239724245754725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25778068280159816163836483 38667102420239724245754725)
  ·
    refine ⟨7250081703794948296079011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38667102420239724245754725 7250081703794948296079011)
    ·
      refine ⟨10875122555692422444118517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7250081703794948296079011 10875122555692422444118517)
      ·
        refine ⟨1019542739596164604136111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10875122555692422444118517 1019542739596164604136111)
        ·
          refine ⟨1529314109394246906204167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019542739596164604136111 1529314109394246906204167)
          ·
            refine ⟨2293971164091370359306251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529314109394246906204167 2293971164091370359306251)
            ·
              refine ⟨3440956746137055538959377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2293971164091370359306251 3440956746137055538959377)
              ·
                refine ⟨2580717559602791654219533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3440956746137055538959377 2580717559602791654219533)
                ·
                  refine ⟨967769084851046870332325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2580717559602791654219533 967769084851046870332325)
                  ·
                    refine ⟨181456703409571288187311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 967769084851046870332325 181456703409571288187311)
                    ·
                      rfl

theorem cell23_1060157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_1060157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060157 prefixEnd_1060157 := by exact prefixLift 1060157
  have htrace : WordTrace (prefixWord ++ tailWord_1060157) baseStart_1060157 baseEnd_1060157 := by
    simpa [prefixWord, tailWord_1060157, baseEnd_1060157] using wordTrace_append hprefix tailTrace_1060157
  have hstable : (prefixWord ++ tailWord_1060157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060157).length < 2 ^ (prefixWord ++ tailWord_1060157).sum := by decide
  have hdescent : baseEnd_1060157 < baseStart_1060157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060180 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_1060180 : Nat := 118140960795 + 1060180 * 2 ^ 59
def prefixEnd_1060180 : Nat := 4983230072969 + 3 ^ 40 * 1060180 * 2
def baseEnd_1060180 : Nat := 544381920283767274574327

theorem tailTrace_1060180 : CollatzResearch.WordTrace tailWord_1060180 prefixEnd_1060180 544381920283767274574327 := by
  unfold tailWord_1060180
  simp only [CollatzResearch.WordTrace]
  refine ⟨19333970649578199586920997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25778627532770932782561329 19333970649578199586920997)
  ·
    refine ⟨3625119496795912422547687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19333970649578199586920997 3625119496795912422547687)
    ·
      refine ⟨5437679245193868633821531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3625119496795912422547687 5437679245193868633821531)
      ·
        refine ⟨8156518867790802950732297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5437679245193868633821531 8156518867790802950732297)
        ·
          refine ⟨6117389150843102213049223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8156518867790802950732297 6117389150843102213049223)
          ·
            refine ⟨9176083726264653319573835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6117389150843102213049223 9176083726264653319573835)
            ·
              refine ⟨13764125589396979979360753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9176083726264653319573835 13764125589396979979360753)
              ·
                refine ⟨10323094192047734984520565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13764125589396979979360753 10323094192047734984520565)
                ·
                  refine ⟨967790080504475154798803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10323094192047734984520565 967790080504475154798803)
                  ·
                    refine ⟨1451685120756712732198205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 967790080504475154798803 1451685120756712732198205)
                    ·
                      refine ⟨544381920283767274574327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1451685120756712732198205 544381920283767274574327)
                      ·
                        rfl

theorem cell23_1060180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_1060180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060180 prefixEnd_1060180 := by exact prefixLift 1060180
  have htrace : WordTrace (prefixWord ++ tailWord_1060180) baseStart_1060180 baseEnd_1060180 := by
    simpa [prefixWord, tailWord_1060180, baseEnd_1060180] using wordTrace_append hprefix tailTrace_1060180
  have hstable : (prefixWord ++ tailWord_1060180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060180).length < 2 ^ (prefixWord ++ tailWord_1060180).sum := by decide
  have hdescent : baseEnd_1060180 < baseStart_1060180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060197 : List Nat := [1, 3, 1, 3, 1, 2, 1, 6, 1, 1, 3]
def baseStart_1060197 : Nat := 118140960795 + 1060197 * 2 ^ 59
def prefixEnd_1060197 : Nat := 4983230072969 + 3 ^ 40 * 1060197 * 2
def baseEnd_1060197 : Nat := 544390649454893708061749

theorem tailTrace_1060197 : CollatzResearch.WordTrace tailWord_1060197 prefixEnd_1060197 544390649454893708061749 := by
  unfold tailWord_1060197
  simp only [CollatzResearch.WordTrace]
  refine ⟨38668561340094811077210845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25779040893396540718140563 38668561340094811077210845)
  ·
    refine ⟨14500710502535554153954067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38668561340094811077210845 14500710502535554153954067)
    ·
      refine ⟨21751065753803331230931101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14500710502535554153954067 21751065753803331230931101)
      ·
        refine ⟨8156649657676249211599163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21751065753803331230931101 8156649657676249211599163)
        ·
          refine ⟨12234974486514373817398745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8156649657676249211599163 12234974486514373817398745)
          ·
            refine ⟨9176230864885780363049059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12234974486514373817398745 9176230864885780363049059)
            ·
              refine ⟨13764346297328670544573589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9176230864885780363049059 13764346297328670544573589)
              ·
                refine ⟨645203732687281431776887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13764346297328670544573589 645203732687281431776887)
                ·
                  refine ⟨967805599030922147665331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645203732687281431776887 967805599030922147665331)
                  ·
                    refine ⟨1451708398546383221497997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 967805599030922147665331 1451708398546383221497997)
                    ·
                      refine ⟨544390649454893708061749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1451708398546383221497997 544390649454893708061749)
                      ·
                        rfl

theorem cell23_1060197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_1060197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060197 prefixEnd_1060197 := by exact prefixLift 1060197
  have htrace : WordTrace (prefixWord ++ tailWord_1060197) baseStart_1060197 baseEnd_1060197 := by
    simpa [prefixWord, tailWord_1060197, baseEnd_1060197] using wordTrace_append hprefix tailTrace_1060197
  have hstable : (prefixWord ++ tailWord_1060197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060197).length < 2 ^ (prefixWord ++ tailWord_1060197).sum := by decide
  have hdescent : baseEnd_1060197 < baseStart_1060197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060203 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 4, 6, 2]
def baseStart_1060203 : Nat := 118140960795 + 1060203 * 2 ^ 59
def prefixEnd_1060203 : Nat := 4983230072969 + 3 ^ 40 * 1060203 * 2
def baseEnd_1060203 : Nat := 544393730338820684586721

theorem tailTrace_1060203 : CollatzResearch.WordTrace tailWord_1060203 prefixEnd_1060203 544393730338820684586721 := by
  unfold tailWord_1060203
  simp only [CollatzResearch.WordTrace]
  refine ⟨38668780178073074101929263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25779186785382049401286175 38668780178073074101929263)
  ·
    refine ⟨58003170267109611152893895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38668780178073074101929263 58003170267109611152893895)
    ·
      refine ⟨87004755400664416729340843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58003170267109611152893895 87004755400664416729340843)
      ·
        refine ⟨130507133100996625094011265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87004755400664416729340843 130507133100996625094011265)
        ·
          refine ⟨97880349825747468820508449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130507133100996625094011265 97880349825747468820508449)
          ·
            refine ⟨73410262369310601615381337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97880349825747468820508449 73410262369310601615381337)
            ·
              refine ⟨55057696776982951211536003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73410262369310601615381337 55057696776982951211536003)
              ·
                refine ⟨82586545165474426817304005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55057696776982951211536003 82586545165474426817304005)
                ·
                  refine ⟨15484977218526455028244501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82586545165474426817304005 15484977218526455028244501)
                  ·
                    refine ⟨725858307118427579448961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15484977218526455028244501 725858307118427579448961)
                    ·
                      refine ⟨544393730338820684586721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 725858307118427579448961 544393730338820684586721)
                      ·
                        rfl

theorem cell23_1060203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 6, 2].length) (baseStart_1060203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060203 prefixEnd_1060203 := by exact prefixLift 1060203
  have htrace : WordTrace (prefixWord ++ tailWord_1060203) baseStart_1060203 baseEnd_1060203 := by
    simpa [prefixWord, tailWord_1060203, baseEnd_1060203] using wordTrace_append hprefix tailTrace_1060203
  have hstable : (prefixWord ++ tailWord_1060203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060203).length < 2 ^ (prefixWord ++ tailWord_1060203).sum := by decide
  have hdescent : baseEnd_1060203 < baseStart_1060203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060220 : List Nat := [2, 2, 2, 1, 1, 1, 6, 2, 1, 1, 4]
def baseStart_1060220 : Nat := 118140960795 + 1060220 * 2 ^ 59
def prefixEnd_1060220 : Nat := 4983230072969 + 3 ^ 40 * 1060220 * 2
def baseEnd_1060220 : Nat := 544402459509947118074143

theorem tailTrace_1060220 : CollatzResearch.WordTrace tailWord_1060220 prefixEnd_1060220 544402459509947118074143 := by
  unfold tailWord_1060220
  simp only [CollatzResearch.WordTrace]
  refine ⟨19334700109505743002649057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25779600146007657336865409 19334700109505743002649057)
  ·
    refine ⟨14501025082129307251986793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19334700109505743002649057 14501025082129307251986793)
    ·
      refine ⟨10875768811596980438990095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14501025082129307251986793 10875768811596980438990095)
      ·
        refine ⟨16313653217395470658485143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10875768811596980438990095 16313653217395470658485143)
        ·
          refine ⟨24470479826093205987727715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16313653217395470658485143 24470479826093205987727715)
          ·
            refine ⟨36705719739139808981591573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24470479826093205987727715 36705719739139808981591573)
            ·
              refine ⟨1720580612772178546012105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36705719739139808981591573 1720580612772178546012105)
              ·
                refine ⟨1290435459579133909509079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1720580612772178546012105 1290435459579133909509079)
                ·
                  refine ⟨1935653189368700864263619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290435459579133909509079 1935653189368700864263619)
                  ·
                    refine ⟨2903479784053051296395429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1935653189368700864263619 2903479784053051296395429)
                    ·
                      refine ⟨544402459509947118074143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2903479784053051296395429 544402459509947118074143)
                      ·
                        rfl

theorem cell23_1060220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_1060220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060220 prefixEnd_1060220 := by exact prefixLift 1060220
  have htrace : WordTrace (prefixWord ++ tailWord_1060220) baseStart_1060220 baseEnd_1060220 := by
    simpa [prefixWord, tailWord_1060220, baseEnd_1060220] using wordTrace_append hprefix tailTrace_1060220
  have hstable : (prefixWord ++ tailWord_1060220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060220).length < 2 ^ (prefixWord ++ tailWord_1060220).sum := by decide
  have hdescent : baseEnd_1060220 < baseStart_1060220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060263 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1060263 : Nat := 118140960795 + 1060263 * 2 ^ 59
def prefixEnd_1060263 : Nat := 4983230072969 + 3 ^ 40 * 1060263 * 2
def baseEnd_1060263 : Nat := 544424539178090449836445

theorem tailTrace_1060263 : CollatzResearch.WordTrace tailWord_1060263 prefixEnd_1060263 544424539178090449836445 := by
  unfold tailWord_1060263
  simp only [CollatzResearch.WordTrace]
  refine ⟨38670968557855704349113443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25780645705237136232742295 38670968557855704349113443)
  ·
    refine ⟨58006452836783556523670165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38670968557855704349113443 58006452836783556523670165)
    ·
      refine ⟨2719052476724229212047039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58006452836783556523670165 2719052476724229212047039)
      ·
        refine ⟨4078578715086343818070559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2719052476724229212047039 4078578715086343818070559)
        ·
          refine ⟨6117868072629515727105839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4078578715086343818070559 6117868072629515727105839)
          ·
            refine ⟨9176802108944273590658759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6117868072629515727105839 9176802108944273590658759)
            ·
              refine ⟨13765203163416410385988139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9176802108944273590658759 13765203163416410385988139)
              ·
                refine ⟨20647804745124615578982209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13765203163416410385988139 20647804745124615578982209)
                ·
                  refine ⟨15485853558843461684236657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20647804745124615578982209 15485853558843461684236657)
                  ·
                    refine ⟨11614390169132596263177493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15485853558843461684236657 11614390169132596263177493)
                    ·
                      refine ⟨544424539178090449836445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11614390169132596263177493 544424539178090449836445)
                      ·
                        rfl

theorem cell23_1060263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1060263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060263 prefixEnd_1060263 := by exact prefixLift 1060263
  have htrace : WordTrace (prefixWord ++ tailWord_1060263) baseStart_1060263 baseEnd_1060263 := by
    simpa [prefixWord, tailWord_1060263, baseEnd_1060263] using wordTrace_append hprefix tailTrace_1060263
  have hstable : (prefixWord ++ tailWord_1060263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060263).length < 2 ^ (prefixWord ++ tailWord_1060263).sum := by decide
  have hdescent : baseEnd_1060263 < baseStart_1060263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060264 : List Nat := [2, 1, 6, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1060264 : Nat := 118140960795 + 1060264 * 2 ^ 59
def prefixEnd_1060264 : Nat := 4983230072969 + 3 ^ 40 * 1060264 * 2
def baseEnd_1060264 : Nat := 181475017552914981974647

theorem tailTrace_1060264 : CollatzResearch.WordTrace tailWord_1060264 prefixEnd_1060264 181475017552914981974647 := by
  unfold tailWord_1060264
  simp only [CollatzResearch.WordTrace]
  refine ⟨19335502515426040759949923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25780670020568054346599897 19335502515426040759949923)
  ·
    refine ⟨29003253773139061139924885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19335502515426040759949923 29003253773139061139924885)
    ·
      refine ⟨1359527520615893490933979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29003253773139061139924885 1359527520615893490933979)
      ·
        refine ⟨2039291280923840236400969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359527520615893490933979 2039291280923840236400969)
        ·
          refine ⟨1529468460692880177300727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2039291280923840236400969 1529468460692880177300727)
          ·
            refine ⟨2294202691039320265951091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529468460692880177300727 2294202691039320265951091)
            ·
              refine ⟨3441304036558980398926637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2294202691039320265951091 3441304036558980398926637)
              ·
                refine ⟨1290489013709617649597489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3441304036558980398926637 1290489013709617649597489)
                ·
                  refine ⟨967866760282213237198117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1290489013709617649597489 967866760282213237198117)
                  ·
                    refine ⟨181475017552914981974647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 967866760282213237198117 181475017552914981974647)
                    ·
                      rfl

theorem cell23_1060264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1060264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060264 prefixEnd_1060264 := by exact prefixLift 1060264
  have htrace : WordTrace (prefixWord ++ tailWord_1060264) baseStart_1060264 baseEnd_1060264 := by
    simpa [prefixWord, tailWord_1060264, baseEnd_1060264] using wordTrace_append hprefix tailTrace_1060264
  have hstable : (prefixWord ++ tailWord_1060264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060264).length < 2 ^ (prefixWord ++ tailWord_1060264).sum := by decide
  have hdescent : baseEnd_1060264 < baseStart_1060264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060327 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_1060327 : Nat := 118140960795 + 1060327 * 2 ^ 59
def prefixEnd_1060327 : Nat := 4983230072969 + 3 ^ 40 * 1060327 * 2
def baseEnd_1060327 : Nat := 544457401939978199436151

theorem tailTrace_1060327 : CollatzResearch.WordTrace tailWord_1060327 prefixEnd_1060327 544457401939978199436151 := by
  unfold tailWord_1060327
  simp only [CollatzResearch.WordTrace]
  refine ⟨38673302829623843279443235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25782201886415895519628823 38673302829623843279443235)
  ·
    refine ⟨58009954244435764919164853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38673302829623843279443235 58009954244435764919164853)
    ·
      refine ⟨5438433210415852961171705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58009954244435764919164853 5438433210415852961171705)
      ·
        refine ⟨4078824907811889720878779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5438433210415852961171705 4078824907811889720878779)
        ·
          refine ⟨6118237361717834581318169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4078824907811889720878779 6118237361717834581318169)
          ·
            refine ⟨4588678021288375935988627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6118237361717834581318169 4588678021288375935988627)
            ·
              refine ⟨6883017031932563903982941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4588678021288375935988627 6883017031932563903982941)
              ·
                refine ⟨2581131386974711463993603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6883017031932563903982941 2581131386974711463993603)
                ·
                  refine ⟨3871697080462067195990405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581131386974711463993603 3871697080462067195990405)
                  ·
                    refine ⟨725943202586637599248201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3871697080462067195990405 725943202586637599248201)
                    ·
                      refine ⟨544457401939978199436151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 725943202586637599248201 544457401939978199436151)
                      ·
                        rfl

theorem cell23_1060327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_1060327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060327 prefixEnd_1060327 := by exact prefixLift 1060327
  have htrace : WordTrace (prefixWord ++ tailWord_1060327) baseStart_1060327 baseEnd_1060327 := by
    simpa [prefixWord, tailWord_1060327, baseEnd_1060327] using wordTrace_append hprefix tailTrace_1060327
  have hstable : (prefixWord ++ tailWord_1060327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060327).length < 2 ^ (prefixWord ++ tailWord_1060327).sum := by decide
  have hdescent : baseEnd_1060327 < baseStart_1060327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060360 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_1060360 : Nat := 118140960795 + 1060360 * 2 ^ 59
def prefixEnd_1060360 : Nat := 4983230072969 + 3 ^ 40 * 1060360 * 2
def baseEnd_1060360 : Nat := 544474346801576570323499

theorem tailTrace_1060360 : CollatzResearch.WordTrace tailWord_1060360 prefixEnd_1060360 544474346801576570323499 := by
  unfold tailWord_1060360
  simp only [CollatzResearch.WordTrace]
  refine ⟨19337253219252144957697267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25783004292336193276929689 19337253219252144957697267)
  ·
    refine ⟨29005879828878217436545901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19337253219252144957697267 29005879828878217436545901)
    ·
      refine ⟨10877204935829331538704713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29005879828878217436545901 10877204935829331538704713)
      ·
        refine ⟨8157903701871998654028535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10877204935829331538704713 8157903701871998654028535)
        ·
          refine ⟨12236855552807997981042803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8157903701871998654028535 12236855552807997981042803)
          ·
            refine ⟨18355283329211996971564205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12236855552807997981042803 18355283329211996971564205)
            ·
              refine ⟨6883231248454498864336577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18355283329211996971564205 6883231248454498864336577)
              ·
                refine ⟨5162423436340874148252433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6883231248454498864336577 5162423436340874148252433)
                ·
                  refine ⟨3871817577255655611189325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5162423436340874148252433 3871817577255655611189325)
                  ·
                    refine ⟨1451931591470870854195997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3871817577255655611189325 1451931591470870854195997)
                    ·
                      refine ⟨544474346801576570323499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1451931591470870854195997 544474346801576570323499)
                      ·
                        rfl

theorem cell23_1060360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_1060360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060360 prefixEnd_1060360 := by exact prefixLift 1060360
  have htrace : WordTrace (prefixWord ++ tailWord_1060360) baseStart_1060360 baseEnd_1060360 := by
    simpa [prefixWord, tailWord_1060360, baseEnd_1060360] using wordTrace_append hprefix tailTrace_1060360
  have hstable : (prefixWord ++ tailWord_1060360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060360).length < 2 ^ (prefixWord ++ tailWord_1060360).sum := by decide
  have hdescent : baseEnd_1060360 < baseStart_1060360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060400 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 4]
def baseStart_1060400 : Nat := 118140960795 + 1060400 * 2 ^ 59
def prefixEnd_1060400 : Nat := 4983230072969 + 3 ^ 40 * 1060400 * 2
def baseEnd_1060400 : Nat := 544494886027756413823315

theorem tailTrace_1060400 : CollatzResearch.WordTrace tailWord_1060400 prefixEnd_1060400 544494886027756413823315 := by
  unfold tailWord_1060400
  simp only [CollatzResearch.WordTrace]
  refine ⟨19337982679179688373425327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25783976905572917831233769 19337982679179688373425327)
  ·
    refine ⟨29006974018769532560137991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19337982679179688373425327 29006974018769532560137991)
    ·
      refine ⟨43510461028154298840206987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29006974018769532560137991 43510461028154298840206987)
      ·
        refine ⟨65265691542231448260310481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43510461028154298840206987 65265691542231448260310481)
        ·
          refine ⟨48949268656673586195232861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65265691542231448260310481 48949268656673586195232861)
          ·
            refine ⟨18355975746252594823212323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48949268656673586195232861 18355975746252594823212323)
            ·
              refine ⟨27533963619378892234818485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18355975746252594823212323 27533963619378892234818485)
              ·
                refine ⟨2581309089316771147014233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27533963619378892234818485 2581309089316771147014233)
                ·
                  refine ⟨1935981816987578360260675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2581309089316771147014233 1935981816987578360260675)
                  ·
                    refine ⟨2903972725481367540391013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1935981816987578360260675 2903972725481367540391013)
                    ·
                      refine ⟨544494886027756413823315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2903972725481367540391013 544494886027756413823315)
                      ·
                        rfl

theorem cell23_1060400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_1060400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060400 prefixEnd_1060400 := by exact prefixLift 1060400
  have htrace : WordTrace (prefixWord ++ tailWord_1060400) baseStart_1060400 baseEnd_1060400 := by
    simpa [prefixWord, tailWord_1060400, baseEnd_1060400] using wordTrace_append hprefix tailTrace_1060400
  have hstable : (prefixWord ++ tailWord_1060400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060400).length < 2 ^ (prefixWord ++ tailWord_1060400).sum := by decide
  have hdescent : baseEnd_1060400 < baseStart_1060400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060417 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1060417 : Nat := 118140960795 + 1060417 * 2 ^ 59
def prefixEnd_1060417 : Nat := 4983230072969 + 3 ^ 40 * 1060417 * 2
def baseEnd_1060417 : Nat := 544503615198882847310737

theorem tailTrace_1060417 : CollatzResearch.WordTrace tailWord_1060417 prefixEnd_1060417 544503615198882847310737 := by
  unfold tailWord_1060417
  simp only [CollatzResearch.WordTrace]
  refine ⟨38676585399297788650219505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25784390266198525766813003 38676585399297788650219505)
  ·
    refine ⟨29007439049473341487664629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38676585399297788650219505 29007439049473341487664629)
    ·
      refine ⟨2719447410888125764468559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29007439049473341487664629 2719447410888125764468559)
      ·
        refine ⟨4079171116332188646702839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2719447410888125764468559 4079171116332188646702839)
        ·
          refine ⟨6118756674498282970054259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4079171116332188646702839 6118756674498282970054259)
          ·
            refine ⟨9178135011747424455081389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6118756674498282970054259 9178135011747424455081389)
            ·
              refine ⟨3441800629405284170655521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9178135011747424455081389 3441800629405284170655521)
              ·
                refine ⟨2581350472053963127991641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3441800629405284170655521 2581350472053963127991641)
                ·
                  refine ⟨1936012854040472345993731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2581350472053963127991641 1936012854040472345993731)
                  ·
                    refine ⟨2904019281060708518990597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1936012854040472345993731 2904019281060708518990597)
                    ·
                      refine ⟨544503615198882847310737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2904019281060708518990597 544503615198882847310737)
                      ·
                        rfl

theorem cell23_1060417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1060417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060417 prefixEnd_1060417 := by exact prefixLift 1060417
  have htrace : WordTrace (prefixWord ++ tailWord_1060417) baseStart_1060417 baseEnd_1060417 := by
    simpa [prefixWord, tailWord_1060417, baseEnd_1060417] using wordTrace_append hprefix tailTrace_1060417
  have hstable : (prefixWord ++ tailWord_1060417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060417).length < 2 ^ (prefixWord ++ tailWord_1060417).sum := by decide
  have hdescent : baseEnd_1060417 < baseStart_1060417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060511 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 1, 5, 2]
def baseStart_1060511 : Nat := 118140960795 + 1060511 * 2 ^ 59
def prefixEnd_1060511 : Nat := 4983230072969 + 3 ^ 40 * 1060511 * 2
def baseEnd_1060511 : Nat := 544551882380405479535305

theorem tailTrace_1060511 : CollatzResearch.WordTrace tailWord_1060511 prefixEnd_1060511 544551882380405479535305 := by
  unfold tailWord_1060511
  simp only [CollatzResearch.WordTrace]
  refine ⟨38680013860957242704141387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25786675907304828469427591 38680013860957242704141387)
  ·
    refine ⟨58020020791435864056212081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38680013860957242704141387 58020020791435864056212081)
    ·
      refine ⟨43515015593576898042159061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58020020791435864056212081 43515015593576898042159061)
      ·
        refine ⟨1019883177974458547863103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 43515015593576898042159061 1019883177974458547863103)
        ·
          refine ⟨1529824766961687821794655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019883177974458547863103 1529824766961687821794655)
          ·
            refine ⟨2294737150442531732691983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529824766961687821794655 2294737150442531732691983)
            ·
              refine ⟨3442105725663797599037975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2294737150442531732691983 3442105725663797599037975)
              ·
                refine ⟨5163158588495696398556963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3442105725663797599037975 5163158588495696398556963)
                ·
                  refine ⟨7744737882743544597835445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5163158588495696398556963 7744737882743544597835445)
                  ·
                    refine ⟨726069176507207306047073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7744737882743544597835445 726069176507207306047073)
                    ·
                      refine ⟨544551882380405479535305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726069176507207306047073 544551882380405479535305)
                      ·
                        rfl

theorem cell23_1060511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_1060511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060511 prefixEnd_1060511 := by exact prefixLift 1060511
  have htrace : WordTrace (prefixWord ++ tailWord_1060511) baseStart_1060511 baseEnd_1060511 := by
    simpa [prefixWord, tailWord_1060511, baseEnd_1060511] using wordTrace_append hprefix tailTrace_1060511
  have hstable : (prefixWord ++ tailWord_1060511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060511).length < 2 ^ (prefixWord ++ tailWord_1060511).sum := by decide
  have hdescent : baseEnd_1060511 < baseStart_1060511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060541 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 3, 2, 2]
def baseStart_1060541 : Nat := 118140960795 + 1060541 * 2 ^ 59
def prefixEnd_1060541 : Nat := 4983230072969 + 3 ^ 40 * 1060541 * 2
def baseEnd_1060541 : Nat := 544567286800040362160167

theorem tailTrace_1060541 : CollatzResearch.WordTrace tailWord_1060541 prefixEnd_1060541 544567286800040362160167 := by
  unfold tailWord_1060541
  simp only [CollatzResearch.WordTrace]
  refine ⟨38681108050848557827733477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25787405367232371885155651 38681108050848557827733477)
  ·
    refine ⟨7252707759534104592700027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38681108050848557827733477 7252707759534104592700027)
    ·
      refine ⟨10879061639301156889050041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7252707759534104592700027 10879061639301156889050041)
      ·
        refine ⟨8159296229475867666787531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10879061639301156889050041 8159296229475867666787531)
        ·
          refine ⟨12238944344213801500181297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8159296229475867666787531 12238944344213801500181297)
          ·
            refine ⟨9179208258160351125135973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12238944344213801500181297 9179208258160351125135973)
            ·
              refine ⟨1721101548405065835962995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9179208258160351125135973 1721101548405065835962995)
              ·
                refine ⟨2581652322607598753944493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1721101548405065835962995 2581652322607598753944493)
                ·
                  refine ⟨968119620977849532729185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2581652322607598753944493 968119620977849532729185)
                  ·
                    refine ⟨726089715733387149546889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 968119620977849532729185 726089715733387149546889)
                    ·
                      refine ⟨544567286800040362160167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726089715733387149546889 544567286800040362160167)
                      ·
                        rfl

theorem cell23_1060541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_1060541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060541 prefixEnd_1060541 := by exact prefixLift 1060541
  have htrace : WordTrace (prefixWord ++ tailWord_1060541) baseStart_1060541 baseEnd_1060541 := by
    simpa [prefixWord, tailWord_1060541, baseEnd_1060541] using wordTrace_append hprefix tailTrace_1060541
  have hstable : (prefixWord ++ tailWord_1060541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060541).length < 2 ^ (prefixWord ++ tailWord_1060541).sum := by decide
  have hdescent : baseEnd_1060541 < baseStart_1060541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060564 : List Nat := [2, 4, 1, 3, 1, 1, 4, 7]
def baseStart_1060564 : Nat := 118140960795 + 1060564 * 2 ^ 59
def prefixEnd_1060564 : Nat := 4983230072969 + 3 ^ 40 * 1060564 * 2
def baseEnd_1060564 : Nat := 20169596179818287858243

theorem tailTrace_1060564 : CollatzResearch.WordTrace tailWord_1060564 prefixEnd_1060564 20169596179818287858243 := by
  unfold tailWord_1060564
  simp only [CollatzResearch.WordTrace]
  refine ⟨19340973464882616377910373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25787964619843488503880497 19340973464882616377910373)
  ·
    refine ⟨3626432524665490570858195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19340973464882616377910373 3626432524665490570858195)
    ·
      refine ⟨5439648786998235856287293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3626432524665490570858195 5439648786998235856287293)
      ·
        refine ⟨2039868295124338446107735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5439648786998235856287293 2039868295124338446107735)
        ·
          refine ⟨3059802442686507669161603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2039868295124338446107735 3059802442686507669161603)
          ·
            refine ⟨4589703664029761503742405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059802442686507669161603 4589703664029761503742405)
            ·
              refine ⟨860569437005580281951701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4589703664029761503742405 860569437005580281951701)
              ·
                refine ⟨20169596179818287858243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 860569437005580281951701 20169596179818287858243)
                ·
                  rfl

theorem cell23_1060564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 7].length) (baseStart_1060564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060564 prefixEnd_1060564 := by exact prefixLift 1060564
  have htrace : WordTrace (prefixWord ++ tailWord_1060564) baseStart_1060564 baseEnd_1060564 := by
    simpa [prefixWord, tailWord_1060564, baseEnd_1060564] using wordTrace_append hprefix tailTrace_1060564
  have hstable : (prefixWord ++ tailWord_1060564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060564).length < 2 ^ (prefixWord ++ tailWord_1060564).sum := by decide
  have hdescent : baseEnd_1060564 < baseStart_1060564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060618 : List Nat := [3, 1, 2, 2, 1, 5, 1, 2, 1, 3, 2]
def baseStart_1060618 : Nat := 118140960795 + 1060618 * 2 ^ 59
def prefixEnd_1060618 : Nat := 4983230072969 + 3 ^ 40 * 1060618 * 2
def baseEnd_1060618 : Nat := 544606824810436560897313

theorem tailTrace_1060618 : CollatzResearch.WordTrace tailWord_1060618 prefixEnd_1060618 544606824810436560897313 := by
  unfold tailWord_1060618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9670979117892399994571627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25789277647713066652191005 9670979117892399994571627)
  ·
    refine ⟨14506468676838599991857441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9670979117892399994571627 14506468676838599991857441)
    ·
      refine ⟨10879851507628949993893081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14506468676838599991857441 10879851507628949993893081)
      ·
        refine ⟨8159888630721712495419811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10879851507628949993893081 8159888630721712495419811)
        ·
          refine ⟨12239832946082568743129717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8159888630721712495419811 12239832946082568743129717)
          ·
            refine ⟨1147484338695240819668411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12239832946082568743129717 1147484338695240819668411)
            ·
              refine ⟨1721226508042861229502617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147484338695240819668411 1721226508042861229502617)
              ·
                refine ⟨1290919881032145922126963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1721226508042861229502617 1290919881032145922126963)
                ·
                  refine ⟨1936379821548218883190445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290919881032145922126963 1936379821548218883190445)
                  ·
                    refine ⟨726142433080582081196417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1936379821548218883190445 726142433080582081196417)
                    ·
                      refine ⟨544606824810436560897313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726142433080582081196417 544606824810436560897313)
                      ·
                        rfl

theorem cell23_1060618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_1060618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060618 prefixEnd_1060618 := by exact prefixLift 1060618
  have htrace : WordTrace (prefixWord ++ tailWord_1060618) baseStart_1060618 baseEnd_1060618 := by
    simpa [prefixWord, tailWord_1060618, baseEnd_1060618] using wordTrace_append hprefix tailTrace_1060618
  have hstable : (prefixWord ++ tailWord_1060618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060618).length < 2 ^ (prefixWord ++ tailWord_1060618).sum := by decide
  have hdescent : baseEnd_1060618 < baseStart_1060618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060631 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 1, 4, 2]
def baseStart_1060631 : Nat := 118140960795 + 1060631 * 2 ^ 59
def prefixEnd_1060631 : Nat := 4983230072969 + 3 ^ 40 * 1060631 * 2
def baseEnd_1060631 : Nat := 544613500058945010034753

theorem tailTrace_1060631 : CollatzResearch.WordTrace tailWord_1060631 prefixEnd_1060631 544613500058945010034753 := by
  unfold tailWord_1060631
  simp only [CollatzResearch.WordTrace]
  refine ⟨38684390620522503198509747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25789593747015002132339831 38684390620522503198509747)
  ·
    refine ⟨58026585930783754797764621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38684390620522503198509747 58026585930783754797764621)
    ·
      refine ⟨21759969724043908049161733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58026585930783754797764621 21759969724043908049161733)
      ·
        refine ⟨4079994323258232759217825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21759969724043908049161733 4079994323258232759217825)
        ·
          refine ⟨3059995742443674569413369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4079994323258232759217825 3059995742443674569413369)
          ·
            refine ⟨2294996806832755927060027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3059995742443674569413369 2294996806832755927060027)
            ·
              refine ⟨3442495210249133890590041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2294996806832755927060027 3442495210249133890590041)
              ·
                refine ⟨2581871407686850417942531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3442495210249133890590041 2581871407686850417942531)
                ·
                  refine ⟨3872807111530275626913797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581871407686850417942531 3872807111530275626913797)
                  ·
                    refine ⟨726151333411926680046337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3872807111530275626913797 726151333411926680046337)
                    ·
                      refine ⟨544613500058945010034753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726151333411926680046337 544613500058945010034753)
                      ·
                        rfl

theorem cell23_1060631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_1060631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060631 prefixEnd_1060631 := by exact prefixLift 1060631
  have htrace : WordTrace (prefixWord ++ tailWord_1060631) baseStart_1060631 baseEnd_1060631 := by
    simpa [prefixWord, tailWord_1060631, baseEnd_1060631] using wordTrace_append hprefix tailTrace_1060631
  have hstable : (prefixWord ++ tailWord_1060631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060631).length < 2 ^ (prefixWord ++ tailWord_1060631).sum := by decide
  have hdescent : baseEnd_1060631 < baseStart_1060631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060648 : List Nat := [2, 1, 5, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_1060648 : Nat := 118140960795 + 1060648 * 2 ^ 59
def prefixEnd_1060648 : Nat := 4983230072969 + 3 ^ 40 * 1060648 * 2
def baseEnd_1060648 : Nat := 544622229230071443522175

theorem tailTrace_1060648 : CollatzResearch.WordTrace tailWord_1060648 prefixEnd_1060648 544622229230071443522175 := by
  unfold tailWord_1060648
  simp only [CollatzResearch.WordTrace]
  refine ⟨19342505330730457550939299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25790007107640610067919065 19342505330730457550939299)
  ·
    refine ⟨29013757996095686326408949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19342505330730457550939299 29013757996095686326408949)
    ·
      refine ⟨2720039812133970593100839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29013757996095686326408949 2720039812133970593100839)
      ·
        refine ⟨4080059718200955889651259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2720039812133970593100839 4080059718200955889651259)
        ·
          refine ⟨6120089577301433834476889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4080059718200955889651259 6120089577301433834476889)
          ·
            refine ⟨4590067182976075375857667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6120089577301433834476889 4590067182976075375857667)
            ·
              refine ⟨6885100774464113063786501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4590067182976075375857667 6885100774464113063786501)
              ·
                refine ⟨1290956395212021199459969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6885100774464113063786501 1290956395212021199459969)
                ·
                  refine ⟨968217296409015899594977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1290956395212021199459969 968217296409015899594977)
                  ·
                    refine ⟨726162972306761924696233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 968217296409015899594977 726162972306761924696233)
                    ·
                      refine ⟨544622229230071443522175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726162972306761924696233 544622229230071443522175)
                      ·
                        rfl

theorem cell23_1060648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_1060648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060648 prefixEnd_1060648 := by exact prefixLift 1060648
  have htrace : WordTrace (prefixWord ++ tailWord_1060648) baseStart_1060648 baseEnd_1060648 := by
    simpa [prefixWord, tailWord_1060648, baseEnd_1060648] using wordTrace_append hprefix tailTrace_1060648
  have hstable : (prefixWord ++ tailWord_1060648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060648).length < 2 ^ (prefixWord ++ tailWord_1060648).sum := by decide
  have hdescent : baseEnd_1060648 < baseStart_1060648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060664 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 2, 3, 3]
def baseStart_1060664 : Nat := 118140960795 + 1060664 * 2 ^ 59
def prefixEnd_1060664 : Nat := 4983230072969 + 3 ^ 40 * 1060664 * 2
def baseEnd_1060664 : Nat := 544630444920543380922101

theorem tailTrace_1060664 : CollatzResearch.WordTrace tailWord_1060664 prefixEnd_1060664 544630444920543380922101 := by
  unfold tailWord_1060664
  simp only [CollatzResearch.WordTrace]
  refine ⟨19342797114701474917230523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25790396152935299889640697 19342797114701474917230523)
  ·
    refine ⟨29014195672052212375845785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19342797114701474917230523 29014195672052212375845785)
    ·
      refine ⟨21760646754039159281884339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29014195672052212375845785 21760646754039159281884339)
      ·
        refine ⟨32640970131058738922826509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21760646754039159281884339 32640970131058738922826509)
        ·
          refine ⟨12240363799147027096059941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32640970131058738922826509 12240363799147027096059941)
          ·
            refine ⟨2295068212340067580511239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12240363799147027096059941 2295068212340067580511239)
            ·
              refine ⟨3442602318510101370766859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295068212340067580511239 3442602318510101370766859)
              ·
                refine ⟨5163903477765152056150289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3442602318510101370766859 5163903477765152056150289)
                ·
                  refine ⟨3872927608323864042112717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5163903477765152056150289 3872927608323864042112717)
                  ·
                    refine ⟨1452347853121449015792269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3872927608323864042112717 1452347853121449015792269)
                    ·
                      refine ⟨544630444920543380922101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1452347853121449015792269 544630444920543380922101)
                      ·
                        rfl

theorem cell23_1060664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_1060664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060664 prefixEnd_1060664 := by exact prefixLift 1060664
  have htrace : WordTrace (prefixWord ++ tailWord_1060664) baseStart_1060664 baseEnd_1060664 := by
    simpa [prefixWord, tailWord_1060664, baseEnd_1060664] using wordTrace_append hprefix tailTrace_1060664
  have hstable : (prefixWord ++ tailWord_1060664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060664).length < 2 ^ (prefixWord ++ tailWord_1060664).sum := by decide
  have hdescent : baseEnd_1060664 < baseStart_1060664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060684 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 1, 7]
def baseStart_1060684 : Nat := 118140960795 + 1060684 * 2 ^ 59
def prefixEnd_1060684 : Nat := 4983230072969 + 3 ^ 40 * 1060684 * 2
def baseEnd_1060684 : Nat := 181546904844544434224003

theorem tailTrace_1060684 : CollatzResearch.WordTrace tailWord_1060684 prefixEnd_1060684 181546904844544434224003 := by
  unfold tailWord_1060684
  simp only [CollatzResearch.WordTrace]
  refine ⟨19343161844665246625094553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25790882459553662166792737 19343161844665246625094553)
  ·
    refine ⟨14507371383498934968820915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19343161844665246625094553 14507371383498934968820915)
    ·
      refine ⟨21761057075248402453231373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14507371383498934968820915 21761057075248402453231373)
      ·
        refine ⟨8160396403218150919961765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21761057075248402453231373 8160396403218150919961765)
        ·
          refine ⟨1530074325603403297492831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8160396403218150919961765 1530074325603403297492831)
          ·
            refine ⟨2295111488405104946239247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530074325603403297492831 2295111488405104946239247)
            ·
              refine ⟨3442667232607657419358871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2295111488405104946239247 3442667232607657419358871)
              ·
                refine ⟨5164000848911486129038307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3442667232607657419358871 5164000848911486129038307)
                ·
                  refine ⟨7746001273367229193557461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5164000848911486129038307 7746001273367229193557461)
                  ·
                    refine ⟨181546904844544434224003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7746001273367229193557461 181546904844544434224003)
                    ·
                      rfl

theorem cell23_1060684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_1060684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060684 prefixEnd_1060684 := by exact prefixLift 1060684
  have htrace : WordTrace (prefixWord ++ tailWord_1060684) baseStart_1060684 baseEnd_1060684 := by
    simpa [prefixWord, tailWord_1060684, baseEnd_1060684] using wordTrace_append hprefix tailTrace_1060684
  have hstable : (prefixWord ++ tailWord_1060684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060684).length < 2 ^ (prefixWord ++ tailWord_1060684).sum := by decide
  have hdescent : baseEnd_1060684 < baseStart_1060684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060765 : List Nat := [1, 4, 2, 1, 2, 3, 3, 2, 1, 4]
def baseStart_1060765 : Nat := 118140960795 + 1060765 * 2 ^ 59
def prefixEnd_1060765 : Nat := 4983230072969 + 3 ^ 40 * 1060765 * 2
def baseEnd_1060765 : Nat := 181560768822215828586379

theorem tailTrace_1060765 : CollatzResearch.WordTrace tailWord_1060765 prefixEnd_1060765 181560768822215828586379 := by
  unfold tailWord_1060765
  simp only [CollatzResearch.WordTrace]
  refine ⟨38689278002037044083887749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25792852001358029389258499 38689278002037044083887749)
  ·
    refine ⟨7254239625381945765728953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38689278002037044083887749 7254239625381945765728953)
    ·
      refine ⟨5440679719036459324296715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7254239625381945765728953 5440679719036459324296715)
      ·
        refine ⟨8161019578554688986445073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5440679719036459324296715 8161019578554688986445073)
        ·
          refine ⟨6120764683916016739833805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8161019578554688986445073 6120764683916016739833805)
          ·
            refine ⟨2295286756468506277437677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6120764683916016739833805 2295286756468506277437677)
            ·
              refine ⟨860732533675689854039129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2295286756468506277437677 860732533675689854039129)
              ·
                refine ⟨645549400256767390529347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 860732533675689854039129 645549400256767390529347)
                ·
                  refine ⟨968324100385151085794021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645549400256767390529347 968324100385151085794021)
                  ·
                    refine ⟨181560768822215828586379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 968324100385151085794021 181560768822215828586379)
                    ·
                      rfl

theorem cell23_1060765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_1060765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060765 prefixEnd_1060765 := by exact prefixLift 1060765
  have htrace : WordTrace (prefixWord ++ tailWord_1060765) baseStart_1060765 baseEnd_1060765 := by
    simpa [prefixWord, tailWord_1060765, baseEnd_1060765] using wordTrace_append hprefix tailTrace_1060765
  have hstable : (prefixWord ++ tailWord_1060765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060765).length < 2 ^ (prefixWord ++ tailWord_1060765).sum := by decide
  have hdescent : baseEnd_1060765 < baseStart_1060765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060798 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_1060798 : Nat := 118140960795 + 1060798 * 2 ^ 59
def prefixEnd_1060798 : Nat := 4983230072969 + 3 ^ 40 * 1060798 * 2
def baseEnd_1060798 : Nat := 544699251328245856646485

theorem tailTrace_1060798 : CollatzResearch.WordTrace tailWord_1060798 prefixEnd_1060798 544699251328245856646485 := by
  unfold tailWord_1060798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4836310201364686339979881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25793654407278327146559365 4836310201364686339979881)
  ·
    refine ⟨3627232651023514754984911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4836310201364686339979881 3627232651023514754984911)
    ·
      refine ⟨5440848976535272132477367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3627232651023514754984911 5440848976535272132477367)
      ·
        refine ⟨8161273464802908198716051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5440848976535272132477367 8161273464802908198716051)
        ·
          refine ⟨12241910197204362298074077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8161273464802908198716051 12241910197204362298074077)
          ·
            refine ⟨4590716323951635861777779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12241910197204362298074077 4590716323951635861777779)
            ·
              refine ⟨6886074485927453792666669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4590716323951635861777779 6886074485927453792666669)
              ·
                refine ⟨2582277932222795172250001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6886074485927453792666669 2582277932222795172250001)
                ·
                  refine ⟨1936708449167096379187501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2582277932222795172250001 1936708449167096379187501)
                  ·
                    refine ⟨726265668437661142195313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1936708449167096379187501 726265668437661142195313)
                    ·
                      refine ⟨544699251328245856646485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726265668437661142195313 544699251328245856646485)
                      ·
                        rfl

theorem cell23_1060798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_1060798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060798 prefixEnd_1060798 := by exact prefixLift 1060798
  have htrace : WordTrace (prefixWord ++ tailWord_1060798) baseStart_1060798 baseEnd_1060798 := by
    simpa [prefixWord, tailWord_1060798, baseEnd_1060798] using wordTrace_append hprefix tailTrace_1060798
  have hstable : (prefixWord ++ tailWord_1060798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060798).length < 2 ^ (prefixWord ++ tailWord_1060798).sum := by decide
  have hdescent : baseEnd_1060798 < baseStart_1060798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060808 : List Nat := [2, 1, 3, 1, 4, 2, 3, 1, 1, 5]
def baseStart_1060808 : Nat := 118140960795 + 1060808 * 2 ^ 59
def prefixEnd_1060808 : Nat := 4983230072969 + 3 ^ 40 * 1060808 * 2
def baseEnd_1060808 : Nat := 181568128711596939173813

theorem tailTrace_1060808 : CollatzResearch.WordTrace tailWord_1060808 prefixEnd_1060808 181568128711596939173813 := by
  unfold tailWord_1060808
  simp only [CollatzResearch.WordTrace]
  refine ⟨19345423170440631213851539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25793897560587508285135385 19345423170440631213851539)
  ·
    refine ⟨29018134755660946820777309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19345423170440631213851539 29018134755660946820777309)
    ·
      refine ⟨10881800533372855057791491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29018134755660946820777309 10881800533372855057791491)
      ·
        refine ⟨16322700800059282586687237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10881800533372855057791491 16322700800059282586687237)
        ·
          refine ⟨3060506400011115485003857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16322700800059282586687237 3060506400011115485003857)
          ·
            refine ⟨2295379800008336613752893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3060506400011115485003857 2295379800008336613752893)
            ·
              refine ⟨860767425003126230157335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2295379800008336613752893 860767425003126230157335)
              ·
                refine ⟨1291151137504689345236003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860767425003126230157335 1291151137504689345236003)
                ·
                  refine ⟨1936726706257034017854005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291151137504689345236003 1936726706257034017854005)
                  ·
                    refine ⟨181568128711596939173813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1936726706257034017854005 181568128711596939173813)
                    ·
                      rfl

theorem cell23_1060808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_1060808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060808 prefixEnd_1060808 := by exact prefixLift 1060808
  have htrace : WordTrace (prefixWord ++ tailWord_1060808) baseStart_1060808 baseEnd_1060808 := by
    simpa [prefixWord, tailWord_1060808, baseEnd_1060808] using wordTrace_append hprefix tailTrace_1060808
  have hstable : (prefixWord ++ tailWord_1060808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060808).length < 2 ^ (prefixWord ++ tailWord_1060808).sum := by decide
  have hdescent : baseEnd_1060808 < baseStart_1060808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060824 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_1060824 : Nat := 118140960795 + 1060824 * 2 ^ 59
def prefixEnd_1060824 : Nat := 4983230072969 + 3 ^ 40 * 1060824 * 2
def baseEnd_1060824 : Nat := 544712601825262754921365

theorem tailTrace_1060824 : CollatzResearch.WordTrace tailWord_1060824 prefixEnd_1060824 544712601825262754921365 := by
  unfold tailWord_1060824
  simp only [CollatzResearch.WordTrace]
  refine ⟨19345714954411648580142763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25794286605882198106857017 19345714954411648580142763)
  ·
    refine ⟨29018572431617472870214145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19345714954411648580142763 29018572431617472870214145)
    ·
      refine ⟨21763929323713104652660609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29018572431617472870214145 21763929323713104652660609)
      ·
        refine ⟨16322946992784828489495457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21763929323713104652660609 16322946992784828489495457)
        ·
          refine ⟨12242210244588621367121593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16322946992784828489495457 12242210244588621367121593)
          ·
            refine ⟨9181657683441466025341195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12242210244588621367121593 9181657683441466025341195)
            ·
              refine ⟨13772486525162199038011793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9181657683441466025341195 13772486525162199038011793)
              ·
                refine ⟨10329364893871649278508845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13772486525162199038011793 10329364893871649278508845)
                ·
                  refine ⟨3873511835201868479440817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10329364893871649278508845 3873511835201868479440817)
                  ·
                    refine ⟨2905133876401401359580613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3873511835201868479440817 2905133876401401359580613)
                    ·
                      refine ⟨544712601825262754921365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2905133876401401359580613 544712601825262754921365)
                      ·
                        rfl

theorem cell23_1060824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_1060824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060824 prefixEnd_1060824 := by exact prefixLift 1060824
  have htrace : WordTrace (prefixWord ++ tailWord_1060824) baseStart_1060824 baseEnd_1060824 := by
    simpa [prefixWord, tailWord_1060824, baseEnd_1060824] using wordTrace_append hprefix tailTrace_1060824
  have hstable : (prefixWord ++ tailWord_1060824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060824).length < 2 ^ (prefixWord ++ tailWord_1060824).sum := by decide
  have hdescent : baseEnd_1060824 < baseStart_1060824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060831 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 3]
def baseStart_1060831 : Nat := 118140960795 + 1060831 * 2 ^ 59
def prefixEnd_1060831 : Nat := 4983230072969 + 3 ^ 40 * 1060831 * 2
def baseEnd_1060831 : Nat := 544716196189844227533833

theorem tailTrace_1060831 : CollatzResearch.WordTrace tailWord_1060831 prefixEnd_1060831 544716196189844227533833 := by
  unfold tailWord_1060831
  simp only [CollatzResearch.WordTrace]
  refine ⟨38691685219797937355790347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25794456813198624903860231 38691685219797937355790347)
  ·
    refine ⟨58037527829696906033685521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38691685219797937355790347 58037527829696906033685521)
    ·
      refine ⟨43528145872272679525264141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58037527829696906033685521 43528145872272679525264141)
      ·
        refine ⟨16323054702102254821974053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43528145872272679525264141 16323054702102254821974053)
        ·
          refine ⟨3060572756644172779120135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16323054702102254821974053 3060572756644172779120135)
          ·
            refine ⟨4590859134966259168680203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3060572756644172779120135 4590859134966259168680203)
            ·
              refine ⟨6886288702449388753020305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4590859134966259168680203 6886288702449388753020305)
              ·
                refine ⟨5164716526837041564765229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6886288702449388753020305 5164716526837041564765229)
                ·
                  refine ⟨1936768697563890586786961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5164716526837041564765229 1936768697563890586786961)
                  ·
                    refine ⟨1452576523172917940090221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1936768697563890586786961 1452576523172917940090221)
                    ·
                      refine ⟨544716196189844227533833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1452576523172917940090221 544716196189844227533833)
                      ·
                        rfl

theorem cell23_1060831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_1060831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060831 prefixEnd_1060831 := by exact prefixLift 1060831
  have htrace : WordTrace (prefixWord ++ tailWord_1060831) baseStart_1060831 baseEnd_1060831 := by
    simpa [prefixWord, tailWord_1060831, baseEnd_1060831] using wordTrace_append hprefix tailTrace_1060831
  have hstable : (prefixWord ++ tailWord_1060831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060831).length < 2 ^ (prefixWord ++ tailWord_1060831).sum := by decide
  have hdescent : baseEnd_1060831 < baseStart_1060831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060861 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_1060861 : Nat := 118140960795 + 1060861 * 2 ^ 59
def prefixEnd_1060861 : Nat := 4983230072969 + 3 ^ 40 * 1060861 * 2
def baseEnd_1060861 : Nat := 544731600609479110158695

theorem tailTrace_1060861 : CollatzResearch.WordTrace tailWord_1060861 prefixEnd_1060861 544731600609479110158695 := by
  unfold tailWord_1060861
  simp only [CollatzResearch.WordTrace]
  refine ⟨38692779409689252479382437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25795186273126168319588291 38692779409689252479382437)
  ·
    refine ⟨7254896139316734839884207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38692779409689252479382437 7254896139316734839884207)
    ·
      refine ⟨10882344208975102259826311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7254896139316734839884207 10882344208975102259826311)
      ·
        refine ⟨16323516313462653389739467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10882344208975102259826311 16323516313462653389739467)
        ·
          refine ⟨24485274470193980084609201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16323516313462653389739467 24485274470193980084609201)
          ·
            refine ⟨18363955852645485063456901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24485274470193980084609201 18363955852645485063456901)
            ·
              refine ⟨3443241722371028449398169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18363955852645485063456901 3443241722371028449398169)
              ·
                refine ⟨2582431291778271337048627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3443241722371028449398169 2582431291778271337048627)
                ·
                  refine ⟨3873646937667407005572941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2582431291778271337048627 3873646937667407005572941)
                  ·
                    refine ⟨1452617601625277627089853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3873646937667407005572941 1452617601625277627089853)
                    ·
                      refine ⟨544731600609479110158695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1452617601625277627089853 544731600609479110158695)
                      ·
                        rfl

theorem cell23_1060861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_1060861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060861 prefixEnd_1060861 := by exact prefixLift 1060861
  have htrace : WordTrace (prefixWord ++ tailWord_1060861) baseStart_1060861 baseEnd_1060861 := by
    simpa [prefixWord, tailWord_1060861, baseEnd_1060861] using wordTrace_append hprefix tailTrace_1060861
  have hstable : (prefixWord ++ tailWord_1060861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060861).length < 2 ^ (prefixWord ++ tailWord_1060861).sum := by decide
  have hdescent : baseEnd_1060861 < baseStart_1060861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060862 : List Nat := [4, 2, 2, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_1060862 : Nat := 118140960795 + 1060862 * 2 ^ 59
def prefixEnd_1060862 : Nat := 4983230072969 + 3 ^ 40 * 1060862 * 2
def baseEnd_1060862 : Nat := 544732114090133606246191

theorem tailTrace_1060862 : CollatzResearch.WordTrace tailWord_1060862 prefixEnd_1060862 544732114090133606246191 := by
  unfold tailWord_1060862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4836601985335703706271105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25795210588457086433445893 4836601985335703706271105)
  ·
    refine ⟨3627451489001777779703329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4836601985335703706271105 3627451489001777779703329)
    ·
      refine ⟨2720588616751333334777497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3627451489001777779703329 2720588616751333334777497)
      ·
        refine ⟨2040441462563500001083123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2720588616751333334777497 2040441462563500001083123)
        ·
          refine ⟨3060662193845250001624685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2040441462563500001083123 3060662193845250001624685)
          ·
            refine ⟨1147748322691968750609257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3060662193845250001624685 1147748322691968750609257)
            ·
              refine ⟨860811242018976562956943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1147748322691968750609257 860811242018976562956943)
              ·
                refine ⟨1291216863028464844435415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860811242018976562956943 1291216863028464844435415)
                ·
                  refine ⟨1936825294542697266653123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291216863028464844435415 1936825294542697266653123)
                  ·
                    refine ⟨2905237941814045899979685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1936825294542697266653123 2905237941814045899979685)
                    ·
                      refine ⟨544732114090133606246191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2905237941814045899979685 544732114090133606246191)
                      ·
                        rfl

theorem cell23_1060862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_1060862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060862 prefixEnd_1060862 := by exact prefixLift 1060862
  have htrace : WordTrace (prefixWord ++ tailWord_1060862) baseStart_1060862 baseEnd_1060862 := by
    simpa [prefixWord, tailWord_1060862, baseEnd_1060862] using wordTrace_append hprefix tailTrace_1060862
  have hstable : (prefixWord ++ tailWord_1060862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060862).length < 2 ^ (prefixWord ++ tailWord_1060862).sum := by decide
  have hdescent : baseEnd_1060862 < baseStart_1060862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060878 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3]
def baseStart_1060878 : Nat := 118140960795 + 1060878 * 2 ^ 59
def prefixEnd_1060878 : Nat := 4983230072969 + 3 ^ 40 * 1060878 * 2
def baseEnd_1060878 : Nat := 544740329780605543646117

theorem tailTrace_1060878 : CollatzResearch.WordTrace tailWord_1060878 prefixEnd_1060878 544740329780605543646117 := by
  unfold tailWord_1060878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4836674931328458047843911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25795599633751776255167525 4836674931328458047843911)
  ·
    refine ⟨7255012396992687071765867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4836674931328458047843911 7255012396992687071765867)
    ·
      refine ⟨10882518595489030607648801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7255012396992687071765867 10882518595489030607648801)
      ·
        refine ⟨8161888946616772955736601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10882518595489030607648801 8161888946616772955736601)
        ·
          refine ⟨6121416709962579716802451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8161888946616772955736601 6121416709962579716802451)
          ·
            refine ⟨9182125064943869575203677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6121416709962579716802451 9182125064943869575203677)
            ·
              refine ⟨3443296899353951090701379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9182125064943869575203677 3443296899353951090701379)
              ·
                refine ⟨5164945349030926636052069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3443296899353951090701379 5164945349030926636052069)
                ·
                  refine ⟨968427252943298744259763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5164945349030926636052069 968427252943298744259763)
                  ·
                    refine ⟨1452640879414948116389645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 968427252943298744259763 1452640879414948116389645)
                    ·
                      refine ⟨544740329780605543646117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1452640879414948116389645 544740329780605543646117)
                      ·
                        rfl

theorem cell23_1060878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_1060878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060878 prefixEnd_1060878 := by exact prefixLift 1060878
  have htrace : WordTrace (prefixWord ++ tailWord_1060878) baseStart_1060878 baseEnd_1060878 := by
    simpa [prefixWord, tailWord_1060878, baseEnd_1060878] using wordTrace_append hprefix tailTrace_1060878
  have hstable : (prefixWord ++ tailWord_1060878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060878).length < 2 ^ (prefixWord ++ tailWord_1060878).sum := by decide
  have hdescent : baseEnd_1060878 < baseStart_1060878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060895 : List Nat := [1, 1, 2, 4, 1, 2, 5, 1, 2, 1, 3]
def baseStart_1060895 : Nat := 118140960795 + 1060895 * 2 ^ 59
def prefixEnd_1060895 : Nat := 4983230072969 + 3 ^ 40 * 1060895 * 2
def baseEnd_1060895 : Nat := 544749058951731977133539

theorem tailTrace_1060895 : CollatzResearch.WordTrace tailWord_1060895 prefixEnd_1060895 544749058951731977133539 := by
  unfold tailWord_1060895
  simp only [CollatzResearch.WordTrace]
  refine ⟨38694019491566076286120139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25796012994377384190746759 38694019491566076286120139)
  ·
    refine ⟨58041029237349114429180209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38694019491566076286120139 58041029237349114429180209)
    ·
      refine ⟨43530771928011835821885157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58041029237349114429180209 43530771928011835821885157)
      ·
        refine ⟨8162019736502219216603467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43530771928011835821885157 8162019736502219216603467)
        ·
          refine ⟨12243029604753328824905201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8162019736502219216603467 12243029604753328824905201)
          ·
            refine ⟨9182272203564996618678901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12243029604753328824905201 9182272203564996618678901)
            ·
              refine ⟨860838019084218433001147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9182272203564996618678901 860838019084218433001147)
              ·
                refine ⟨1291257028626327649501721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860838019084218433001147 1291257028626327649501721)
                ·
                  refine ⟨968442771469745737126291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1291257028626327649501721 968442771469745737126291)
                  ·
                    refine ⟨1452664157204618605689437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 968442771469745737126291 1452664157204618605689437)
                    ·
                      refine ⟨544749058951731977133539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1452664157204618605689437 544749058951731977133539)
                      ·
                        rfl

theorem cell23_1060895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_1060895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060895 prefixEnd_1060895 := by exact prefixLift 1060895
  have htrace : WordTrace (prefixWord ++ tailWord_1060895) baseStart_1060895 baseEnd_1060895 := by
    simpa [prefixWord, tailWord_1060895, baseEnd_1060895] using wordTrace_append hprefix tailTrace_1060895
  have hstable : (prefixWord ++ tailWord_1060895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060895).length < 2 ^ (prefixWord ++ tailWord_1060895).sum := by decide
  have hdescent : baseEnd_1060895 < baseStart_1060895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060935 : List Nat := [1, 1, 4, 1, 3, 1, 2, 4, 2, 2, 2]
def baseStart_1060935 : Nat := 118140960795 + 1060935 * 2 ^ 59
def prefixEnd_1060935 : Nat := 4983230072969 + 3 ^ 40 * 1060935 * 2
def baseEnd_1060935 : Nat := 544769598177911820633355

theorem tailTrace_1060935 : CollatzResearch.WordTrace tailWord_1060935 prefixEnd_1060935 544769598177911820633355 := by
  unfold tailWord_1060935
  simp only [CollatzResearch.WordTrace]
  refine ⟨38695478411421163117576259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25796985607614108745050839 38695478411421163117576259)
  ·
    refine ⟨58043217617131744676364389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38695478411421163117576259 58043217617131744676364389)
    ·
      refine ⟨10883103303212202126818323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58043217617131744676364389 10883103303212202126818323)
      ·
        refine ⟨16324654954818303190227485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10883103303212202126818323 16324654954818303190227485)
        ·
          refine ⟨6121745608056863696335307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16324654954818303190227485 6121745608056863696335307)
          ·
            refine ⟨9182618412085295544502961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6121745608056863696335307 9182618412085295544502961)
            ·
              refine ⟨6886963809063971658377221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9182618412085295544502961 6886963809063971658377221)
              ·
                refine ⟨1291305714199494685945729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6886963809063971658377221 1291305714199494685945729)
                ·
                  refine ⟨968479285649621014459297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1291305714199494685945729 968479285649621014459297)
                  ·
                    refine ⟨726359464237215760844473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 968479285649621014459297 726359464237215760844473)
                    ·
                      refine ⟨544769598177911820633355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726359464237215760844473 544769598177911820633355)
                      ·
                        rfl

theorem cell23_1060935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_1060935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060935 prefixEnd_1060935 := by exact prefixLift 1060935
  have htrace : WordTrace (prefixWord ++ tailWord_1060935) baseStart_1060935 baseEnd_1060935 := by
    simpa [prefixWord, tailWord_1060935, baseEnd_1060935] using wordTrace_append hprefix tailTrace_1060935
  have hstable : (prefixWord ++ tailWord_1060935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060935).length < 2 ^ (prefixWord ++ tailWord_1060935).sum := by decide
  have hdescent : baseEnd_1060935 < baseStart_1060935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060951 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 3]
def baseStart_1060951 : Nat := 118140960795 + 1060951 * 2 ^ 59
def prefixEnd_1060951 : Nat := 4983230072969 + 3 ^ 40 * 1060951 * 2
def baseEnd_1060951 : Nat := 544777813868383758033281

theorem tailTrace_1060951 : CollatzResearch.WordTrace tailWord_1060951 prefixEnd_1060951 544777813868383758033281 := by
  unfold tailWord_1060951
  simp only [CollatzResearch.WordTrace]
  refine ⟨38696061979363197850158707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25797374652908798566772471 38696061979363197850158707)
  ·
    refine ⟨58044092969044796775238061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38696061979363197850158707 58044092969044796775238061)
    ·
      refine ⟨21766534863391798790714273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58044092969044796775238061 21766534863391798790714273)
      ·
        refine ⟨16324901147543849093035705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21766534863391798790714273 16324901147543849093035705)
        ·
          refine ⟨12243675860657886819776779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16324901147543849093035705 12243675860657886819776779)
          ·
            refine ⟨18365513790986830229665169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12243675860657886819776779 18365513790986830229665169)
            ·
              refine ⟨13774135343240122672248877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18365513790986830229665169 13774135343240122672248877)
              ·
                refine ⟨5165300753715046002093329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13774135343240122672248877 5165300753715046002093329)
                ·
                  refine ⟨3873975565286284501569997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5165300753715046002093329 3873975565286284501569997)
                  ·
                    refine ⟨1452740836982356688088749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3873975565286284501569997 1452740836982356688088749)
                    ·
                      refine ⟨544777813868383758033281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1452740836982356688088749 544777813868383758033281)
                      ·
                        rfl

theorem cell23_1060951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_1060951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060951 prefixEnd_1060951 := by exact prefixLift 1060951
  have htrace : WordTrace (prefixWord ++ tailWord_1060951) baseStart_1060951 baseEnd_1060951 := by
    simpa [prefixWord, tailWord_1060951, baseEnd_1060951] using wordTrace_append hprefix tailTrace_1060951
  have hstable : (prefixWord ++ tailWord_1060951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060951).length < 2 ^ (prefixWord ++ tailWord_1060951).sum := by decide
  have hdescent : baseEnd_1060951 < baseStart_1060951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1060952 : List Nat := [2, 1, 2, 2, 1, 4, 4, 1, 2, 2, 2]
def baseStart_1060952 : Nat := 118140960795 + 1060952 * 2 ^ 59
def prefixEnd_1060952 : Nat := 4983230072969 + 3 ^ 40 * 1060952 * 2
def baseEnd_1060952 : Nat := 544778327349038254120777

theorem tailTrace_1060952 : CollatzResearch.WordTrace tailWord_1060952 prefixEnd_1060952 544778327349038254120777 := by
  unfold tailWord_1060952
  simp only [CollatzResearch.WordTrace]
  refine ⟨19348049226179787510472555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25797398968239716680630073 19348049226179787510472555)
  ·
    refine ⟨29022073839269681265708833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19348049226179787510472555 29022073839269681265708833)
    ·
      refine ⟨21766555379452260949281625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29022073839269681265708833 21766555379452260949281625)
      ·
        refine ⟨16324916534589195711961219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21766555379452260949281625 16324916534589195711961219)
        ·
          refine ⟨24487374801883793567941829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16324916534589195711961219 24487374801883793567941829)
          ·
            refine ⟨4591382775353211293989093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24487374801883793567941829 4591382775353211293989093)
            ·
              refine ⟨860884270378727117622955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4591382775353211293989093 860884270378727117622955)
              ·
                refine ⟨1291326405568090676434433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860884270378727117622955 1291326405568090676434433)
                ·
                  refine ⟨968494804176068007325825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1291326405568090676434433 968494804176068007325825)
                  ·
                    refine ⟨726371103132051005494369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 968494804176068007325825 726371103132051005494369)
                    ·
                      refine ⟨544778327349038254120777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726371103132051005494369 544778327349038254120777)
                      ·
                        rfl

theorem cell23_1060952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_1060952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1060952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1060952 prefixEnd_1060952 := by exact prefixLift 1060952
  have htrace : WordTrace (prefixWord ++ tailWord_1060952) baseStart_1060952 baseEnd_1060952 := by
    simpa [prefixWord, tailWord_1060952, baseEnd_1060952] using wordTrace_append hprefix tailTrace_1060952
  have hstable : (prefixWord ++ tailWord_1060952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1060952).length < 2 ^ (prefixWord ++ tailWord_1060952).sum := by decide
  have hdescent : baseEnd_1060952 < baseStart_1060952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1060952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061008 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 2, 4, 2]
def baseStart_1061008 : Nat := 118140960795 + 1061008 * 2 ^ 59
def prefixEnd_1061008 : Nat := 4983230072969 + 3 ^ 40 * 1061008 * 2
def baseEnd_1061008 : Nat := 544807082265690035020519

theorem tailTrace_1061008 : CollatzResearch.WordTrace tailWord_1061008 prefixEnd_1061008 544807082265690035020519 := by
  unfold tailWord_1061008
  simp only [CollatzResearch.WordTrace]
  refine ⟨19349070470078348292491839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25798760626771131056655785 19349070470078348292491839)
  ·
    refine ⟨29023605705117522438737759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19349070470078348292491839 29023605705117522438737759)
    ·
      refine ⟨43535408557676283658106639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29023605705117522438737759 43535408557676283658106639)
      ·
        refine ⟨65303112836514425487159959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43535408557676283658106639 65303112836514425487159959)
        ·
          refine ⟨97954669254771638230739939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65303112836514425487159959 97954669254771638230739939)
          ·
            refine ⟨146932003882157457346109909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97954669254771638230739939 146932003882157457346109909)
            ·
              refine ⟨3443718840988065406549451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 146932003882157457346109909 3443718840988065406549451)
              ·
                refine ⟨5165578261482098109824177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3443718840988065406549451 5165578261482098109824177)
                ·
                  refine ⟨3874183696111573582368133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5165578261482098109824177 3874183696111573582368133)
                  ·
                    refine ⟨726409443020920046694025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3874183696111573582368133 726409443020920046694025)
                    ·
                      refine ⟨544807082265690035020519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726409443020920046694025 544807082265690035020519)
                      ·
                        rfl

theorem cell23_1061008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 2, 4, 2].length) (baseStart_1061008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061008 prefixEnd_1061008 := by exact prefixLift 1061008
  have htrace : WordTrace (prefixWord ++ tailWord_1061008) baseStart_1061008 baseEnd_1061008 := by
    simpa [prefixWord, tailWord_1061008, baseEnd_1061008] using wordTrace_append hprefix tailTrace_1061008
  have hstable : (prefixWord ++ tailWord_1061008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061008).length < 2 ^ (prefixWord ++ tailWord_1061008).sum := by decide
  have hdescent : baseEnd_1061008 < baseStart_1061008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061011 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 3]
def baseStart_1061011 : Nat := 118140960795 + 1061011 * 2 ^ 59
def prefixEnd_1061011 : Nat := 4983230072969 + 3 ^ 40 * 1061011 * 2
def baseEnd_1061011 : Nat := 544808622707653523283005

theorem tailTrace_1061011 : CollatzResearch.WordTrace tailWord_1061011 prefixEnd_1061011 544808622707653523283005 := by
  unfold tailWord_1061011
  simp only [CollatzResearch.WordTrace]
  refine ⟨38698250359145828097342887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25798833572763885398228591 38698250359145828097342887)
  ·
    refine ⟨58047375538718742146014331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38698250359145828097342887 58047375538718742146014331)
    ·
      refine ⟨87071063308078113219021497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58047375538718742146014331 87071063308078113219021497)
      ·
        refine ⟨65303297481058584914266123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87071063308078113219021497 65303297481058584914266123)
        ·
          refine ⟨97954946221587877371399185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65303297481058584914266123 97954946221587877371399185)
          ·
            refine ⟨73466209666190908028549389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97954946221587877371399185 73466209666190908028549389)
            ·
              refine ⟨27549828624821590510706021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73466209666190908028549389 27549828624821590510706021)
              ·
                refine ⟨5165592867154048220757379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27549828624821590510706021 5165592867154048220757379)
                ·
                  refine ⟨7748389300731072331136069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5165592867154048220757379 7748389300731072331136069)
                  ·
                    refine ⟨1452822993887076062088013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7748389300731072331136069 1452822993887076062088013)
                    ·
                      refine ⟨544808622707653523283005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1452822993887076062088013 544808622707653523283005)
                      ·
                        rfl

theorem cell23_1061011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 3].length) (baseStart_1061011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061011 prefixEnd_1061011 := by exact prefixLift 1061011
  have htrace : WordTrace (prefixWord ++ tailWord_1061011) baseStart_1061011 baseEnd_1061011 := by
    simpa [prefixWord, tailWord_1061011, baseEnd_1061011] using wordTrace_append hprefix tailTrace_1061011
  have hstable : (prefixWord ++ tailWord_1061011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061011).length < 2 ^ (prefixWord ++ tailWord_1061011).sum := by decide
  have hdescent : baseEnd_1061011 < baseStart_1061011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061022 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1061022 : Nat := 118140960795 + 1061022 * 2 ^ 59
def prefixEnd_1061022 : Nat := 4983230072969 + 3 ^ 40 * 1061022 * 2
def baseEnd_1061022 : Nat := 181604756998284326748485

theorem tailTrace_1061022 : CollatzResearch.WordTrace tailWord_1061022 prefixEnd_1061022 181604756998284326748485 := by
  unfold tailWord_1061022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4837331445263247121999165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25799101041403984650662213 4837331445263247121999165)
  ·
    refine ⟨1813999291973717670749687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4837331445263247121999165 1813999291973717670749687)
    ·
      refine ⟨2720998937960576506124531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1813999291973717670749687 2720998937960576506124531)
      ·
        refine ⟨4081498406940864759186797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2720998937960576506124531 4081498406940864759186797)
        ·
          refine ⟨1530561902602824284695049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4081498406940864759186797 1530561902602824284695049)
          ·
            refine ⟨1147921426952118213521287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1530561902602824284695049 1147921426952118213521287)
            ·
              refine ⟨1721882140428177320281931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147921426952118213521287 1721882140428177320281931)
              ·
                refine ⟨2582823210642265980422897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1721882140428177320281931 2582823210642265980422897)
                ·
                  refine ⟨1937117407981699485317173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2582823210642265980422897 1937117407981699485317173)
                  ·
                    refine ⟨181604756998284326748485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1937117407981699485317173 181604756998284326748485)
                    ·
                      rfl

theorem cell23_1061022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1061022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061022 prefixEnd_1061022 := by exact prefixLift 1061022
  have htrace : WordTrace (prefixWord ++ tailWord_1061022) baseStart_1061022 baseEnd_1061022 := by
    simpa [prefixWord, tailWord_1061022, baseEnd_1061022] using wordTrace_append hprefix tailTrace_1061022
  have hstable : (prefixWord ++ tailWord_1061022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061022).length < 2 ^ (prefixWord ++ tailWord_1061022).sum := by decide
  have hdescent : baseEnd_1061022 < baseStart_1061022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061025 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 2, 1, 4]
def baseStart_1061025 : Nat := 118140960795 + 1061025 * 2 ^ 59
def prefixEnd_1061025 : Nat := 4983230072969 + 3 ^ 40 * 1061025 * 2
def baseEnd_1061025 : Nat := 544815811436816468507941

theorem tailTrace_1061025 : CollatzResearch.WordTrace tailWord_1061025 prefixEnd_1061025 544815811436816468507941 := by
  unfold tailWord_1061025
  simp only [CollatzResearch.WordTrace]
  refine ⟨38698760981095108488352529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25799173987396738992235019 38698760981095108488352529)
  ·
    refine ⟨29024070735821331366264397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38698760981095108488352529 29024070735821331366264397)
    ·
      refine ⟨10884026525932999262349149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29024070735821331366264397 10884026525932999262349149)
      ·
        refine ⟨4081509947224874723380931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10884026525932999262349149 4081509947224874723380931)
        ·
          refine ⟨6122264920837312085071397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4081509947224874723380931 6122264920837312085071397)
          ·
            refine ⟨1147924672656996015950887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6122264920837312085071397 1147924672656996015950887)
            ·
              refine ⟨1721887008985494023926331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147924672656996015950887 1721887008985494023926331)
              ·
                refine ⟨2582830513478241035889497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1721887008985494023926331 2582830513478241035889497)
                ·
                  refine ⟨1937122885108680776917123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2582830513478241035889497 1937122885108680776917123)
                  ·
                    refine ⟨2905684327663021165375685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1937122885108680776917123 2905684327663021165375685)
                    ·
                      refine ⟨544815811436816468507941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2905684327663021165375685 544815811436816468507941)
                      ·
                        rfl

theorem cell23_1061025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_1061025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061025 prefixEnd_1061025 := by exact prefixLift 1061025
  have htrace : WordTrace (prefixWord ++ tailWord_1061025) baseStart_1061025 baseEnd_1061025 := by
    simpa [prefixWord, tailWord_1061025, baseEnd_1061025] using wordTrace_append hprefix tailTrace_1061025
  have hstable : (prefixWord ++ tailWord_1061025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061025).length < 2 ^ (prefixWord ++ tailWord_1061025).sum := by decide
  have hdescent : baseEnd_1061025 < baseStart_1061025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061061 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 5, 5]
def baseStart_1061061 : Nat := 118140960795 + 1061061 * 2 ^ 59
def prefixEnd_1061061 : Nat := 4983230072969 + 3 ^ 40 * 1061061 * 2
def baseEnd_1061061 : Nat := 181611432246792775885925

theorem tailTrace_1061061 : CollatzResearch.WordTrace tailWord_1061061 prefixEnd_1061061 181611432246792775885925 := by
  unfold tailWord_1061061
  simp only [CollatzResearch.WordTrace]
  refine ⟨38700074008964686636663037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25800049339309791091108691 38700074008964686636663037)
  ·
    refine ⟨14512527753361757488748639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38700074008964686636663037 14512527753361757488748639)
    ·
      refine ⟨21768791630042636233122959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14512527753361757488748639 21768791630042636233122959)
      ·
        refine ⟨32653187445063954349684439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21768791630042636233122959 32653187445063954349684439)
        ·
          refine ⟨48979781167595931524526659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32653187445063954349684439 48979781167595931524526659)
          ·
            refine ⟨73469671751393897286789989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48979781167595931524526659 73469671751393897286789989)
            ·
              refine ⟨13775563453386355741273123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73469671751393897286789989 13775563453386355741273123)
              ·
                refine ⟨20663345180079533611909685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13775563453386355741273123 20663345180079533611909685)
                ·
                  refine ⟨1937188610632456276116533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20663345180079533611909685 1937188610632456276116533)
                  ·
                    refine ⟨181611432246792775885925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1937188610632456276116533 181611432246792775885925)
                    ·
                      rfl

theorem cell23_1061061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_1061061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061061 prefixEnd_1061061 := by exact prefixLift 1061061
  have htrace : WordTrace (prefixWord ++ tailWord_1061061) baseStart_1061061 baseEnd_1061061 := by
    simpa [prefixWord, tailWord_1061061, baseEnd_1061061] using wordTrace_append hprefix tailTrace_1061061
  have hstable : (prefixWord ++ tailWord_1061061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061061).length < 2 ^ (prefixWord ++ tailWord_1061061).sum := by decide
  have hdescent : baseEnd_1061061 < baseStart_1061061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061095 : List Nat := [1, 1, 5, 3, 1, 1, 2, 3, 1, 5]
def baseStart_1061095 : Nat := 118140960795 + 1061095 * 2 ^ 59
def prefixEnd_1061095 : Nat := 4983230072969 + 3 ^ 40 * 1061095 * 2
def baseEnd_1061095 : Nat := 181617251694210398210873

theorem tailTrace_1061095 : CollatzResearch.WordTrace tailWord_1061095 prefixEnd_1061095 181617251694210398210873 := by
  unfold tailWord_1061095
  simp only [CollatzResearch.WordTrace]
  refine ⟨38701314090841510443400739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25800876060561006962267159 38701314090841510443400739)
  ·
    refine ⟨58051971136262265665101109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38701314090841510443400739 58051971136262265665101109)
    ·
      refine ⟨5442372294024587406103229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58051971136262265665101109 5442372294024587406103229)
      ·
        refine ⟨2040889610259220277288711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5442372294024587406103229 2040889610259220277288711)
        ·
          refine ⟨3061334415388830415933067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2040889610259220277288711 3061334415388830415933067)
          ·
            refine ⟨4592001623083245623899601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3061334415388830415933067 4592001623083245623899601)
            ·
              refine ⟨3444001217312434217924701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4592001623083245623899601 3444001217312434217924701)
              ·
                refine ⟨1291500456492162831721763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3444001217312434217924701 1291500456492162831721763)
                ·
                  refine ⟨1937250684738244247582645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291500456492162831721763 1937250684738244247582645)
                  ·
                    refine ⟨181617251694210398210873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1937250684738244247582645 181617251694210398210873)
                    ·
                      rfl

theorem cell23_1061095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_1061095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061095 prefixEnd_1061095 := by exact prefixLift 1061095
  have htrace : WordTrace (prefixWord ++ tailWord_1061095) baseStart_1061095 baseEnd_1061095 := by
    simpa [prefixWord, tailWord_1061095, baseEnd_1061095] using wordTrace_append hprefix tailTrace_1061095
  have hstable : (prefixWord ++ tailWord_1061095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061095).length < 2 ^ (prefixWord ++ tailWord_1061095).sum := by decide
  have hdescent : baseEnd_1061095 < baseStart_1061095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061111 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_1061111 : Nat := 118140960795 + 1061111 * 2 ^ 59
def prefixEnd_1061111 : Nat := 4983230072969 + 3 ^ 40 * 1061111 * 2
def baseEnd_1061111 : Nat := 544859970773103132032545

theorem tailTrace_1061111 : CollatzResearch.WordTrace tailWord_1061111 prefixEnd_1061111 544859970773103132032545 := by
  unfold tailWord_1061111
  simp only [CollatzResearch.WordTrace]
  refine ⟨38701897658783545175983187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25801265105855696783988791 38701897658783545175983187)
  ·
    refine ⟨58052846488175317763974781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38701897658783545175983187 58052846488175317763974781)
    ·
      refine ⟨21769817433065744161490543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58052846488175317763974781 21769817433065744161490543)
      ·
        refine ⟨32654726149598616242235815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21769817433065744161490543 32654726149598616242235815)
        ·
          refine ⟨48982089224397924363353723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32654726149598616242235815 48982089224397924363353723)
          ·
            refine ⟨73473133836596886545030585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48982089224397924363353723 73473133836596886545030585)
            ·
              refine ⟨55104850377447664908772939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73473133836596886545030585 55104850377447664908772939)
              ·
                refine ⟨82657275566171497363159409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55104850377447664908772939 82657275566171497363159409)
                ·
                  refine ⟨61992956674628623022369557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82657275566171497363159409 61992956674628623022369557)
                  ·
                    refine ⟨2905919844123216704173573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61992956674628623022369557 2905919844123216704173573)
                    ·
                      refine ⟨544859970773103132032545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2905919844123216704173573 544859970773103132032545)
                      ·
                        rfl

theorem cell23_1061111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_1061111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061111 prefixEnd_1061111 := by exact prefixLift 1061111
  have htrace : WordTrace (prefixWord ++ tailWord_1061111) baseStart_1061111 baseEnd_1061111 := by
    simpa [prefixWord, tailWord_1061111, baseEnd_1061111] using wordTrace_append hprefix tailTrace_1061111
  have hstable : (prefixWord ++ tailWord_1061111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061111).length < 2 ^ (prefixWord ++ tailWord_1061111).sum := by decide
  have hdescent : baseEnd_1061111 < baseStart_1061111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061128 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_1061128 : Nat := 118140960795 + 1061128 * 2 ^ 59
def prefixEnd_1061128 : Nat := 4983230072969 + 3 ^ 40 * 1061128 * 2
def baseEnd_1061128 : Nat := 544868699944229565519967

theorem tailTrace_1061128 : CollatzResearch.WordTrace tailWord_1061128 prefixEnd_1061128 544868699944229565519967 := by
  unfold tailWord_1061128
  simp only [CollatzResearch.WordTrace]
  refine ⟨19351258849860978539676019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25801678466481304719568025 19351258849860978539676019)
  ·
    refine ⟨29026888274791467809514029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19351258849860978539676019 29026888274791467809514029)
    ·
      refine ⟨10885083103046800428567761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29026888274791467809514029 10885083103046800428567761)
      ·
        refine ⟨8163812327285100321425821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10885083103046800428567761 8163812327285100321425821)
        ·
          refine ⟨3061429622731912620534683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8163812327285100321425821 3061429622731912620534683)
          ·
            refine ⟨4592144434097868930802025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3061429622731912620534683 4592144434097868930802025)
            ·
              refine ⟨3444108325573401698101519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4592144434097868930802025 3444108325573401698101519)
              ·
                refine ⟨5166162488360102547152279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3444108325573401698101519 5166162488360102547152279)
                ·
                  refine ⟨7749243732540153820728419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5166162488360102547152279 7749243732540153820728419)
                  ·
                    refine ⟨11623865598810230731092629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7749243732540153820728419 11623865598810230731092629)
                    ·
                      refine ⟨544868699944229565519967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11623865598810230731092629 544868699944229565519967)
                      ·
                        rfl

theorem cell23_1061128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_1061128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061128 prefixEnd_1061128 := by exact prefixLift 1061128
  have htrace : WordTrace (prefixWord ++ tailWord_1061128) baseStart_1061128 baseEnd_1061128 := by
    simpa [prefixWord, tailWord_1061128, baseEnd_1061128] using wordTrace_append hprefix tailTrace_1061128
  have hstable : (prefixWord ++ tailWord_1061128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061128).length < 2 ^ (prefixWord ++ tailWord_1061128).sum := by decide
  have hdescent : baseEnd_1061128 < baseStart_1061128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061149 : List Nat := [1, 4, 2, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_1061149 : Nat := 118140960795 + 1061149 * 2 ^ 59
def prefixEnd_1061149 : Nat := 4983230072969 + 3 ^ 40 * 1061149 * 2
def baseEnd_1061149 : Nat := 544879483037973983357371

theorem tailTrace_1061149 : CollatzResearch.WordTrace tailWord_1061149 prefixEnd_1061149 544879483037973983357371 := by
  unfold tailWord_1061149
  simp only [CollatzResearch.WordTrace]
  refine ⟨38703283632645877665866501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25802189088430585110577667 38703283632645877665866501)
  ·
    refine ⟨7256865681121102062349969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38703283632645877665866501 7256865681121102062349969)
    ·
      refine ⟨5442649260840826546762477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7256865681121102062349969 5442649260840826546762477)
      ·
        refine ⟨2040993472815309955035929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5442649260840826546762477 2040993472815309955035929)
        ·
          refine ⟨1530745104611482466276947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2040993472815309955035929 1530745104611482466276947)
          ·
            refine ⟨2296117656917223699415421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530745104611482466276947 2296117656917223699415421)
            ·
              refine ⟨861044121343958887280783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2296117656917223699415421 861044121343958887280783)
              ·
                refine ⟨1291566182015938330921175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 861044121343958887280783 1291566182015938330921175)
                ·
                  refine ⟨1937349273023907496381763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291566182015938330921175 1937349273023907496381763)
                  ·
                    refine ⟨2906023909535861244572645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1937349273023907496381763 2906023909535861244572645)
                    ·
                      refine ⟨544879483037973983357371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2906023909535861244572645 544879483037973983357371)
                      ·
                        rfl

theorem cell23_1061149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_1061149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061149 prefixEnd_1061149 := by exact prefixLift 1061149
  have htrace : WordTrace (prefixWord ++ tailWord_1061149) baseStart_1061149 baseEnd_1061149 := by
    simpa [prefixWord, tailWord_1061149, baseEnd_1061149] using wordTrace_append hprefix tailTrace_1061149
  have hstable : (prefixWord ++ tailWord_1061149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061149).length < 2 ^ (prefixWord ++ tailWord_1061149).sum := by decide
  have hdescent : baseEnd_1061149 < baseStart_1061149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061182 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1061182 : Nat := 118140960795 + 1061182 * 2 ^ 59
def prefixEnd_1061182 : Nat := 4983230072969 + 3 ^ 40 * 1061182 * 2
def baseEnd_1061182 : Nat := 544896427899572354244719

theorem tailTrace_1061182 : CollatzResearch.WordTrace tailWord_1061182 prefixEnd_1061182 544896427899572354244719 := by
  unfold tailWord_1061182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4838060905190790537727225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25802991494350882867878533 4838060905190790537727225)
  ·
    refine ⟨3628545678893092903295419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4838060905190790537727225 3628545678893092903295419)
    ·
      refine ⟨5442818518339639354943129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3628545678893092903295419 5442818518339639354943129)
      ·
        refine ⟨4082113888754729516207347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5442818518339639354943129 4082113888754729516207347)
        ·
          refine ⟨6123170833132094274311021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4082113888754729516207347 6123170833132094274311021)
          ·
            refine ⟨2296189062424535352866633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6123170833132094274311021 2296189062424535352866633)
            ·
              refine ⟨1722141796818401514649975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2296189062424535352866633 1722141796818401514649975)
              ·
                refine ⟨2583212695227602271974963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1722141796818401514649975 2583212695227602271974963)
                ·
                  refine ⟨3874819042841403407962445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2583212695227602271974963 3874819042841403407962445)
                  ·
                    refine ⟨1453057141065526277985917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3874819042841403407962445 1453057141065526277985917)
                    ·
                      refine ⟨544896427899572354244719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1453057141065526277985917 544896427899572354244719)
                      ·
                        rfl

theorem cell23_1061182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1061182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061182 prefixEnd_1061182 := by exact prefixLift 1061182
  have htrace : WordTrace (prefixWord ++ tailWord_1061182) baseStart_1061182 baseEnd_1061182 := by
    simpa [prefixWord, tailWord_1061182, baseEnd_1061182] using wordTrace_append hprefix tailTrace_1061182
  have hstable : (prefixWord ++ tailWord_1061182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061182).length < 2 ^ (prefixWord ++ tailWord_1061182).sum := by decide
  have hdescent : baseEnd_1061182 < baseStart_1061182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061208 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 1, 6, 3]
def baseStart_1061208 : Nat := 118140960795 + 1061208 * 2 ^ 59
def prefixEnd_1061208 : Nat := 4983230072969 + 3 ^ 40 * 1061208 * 2
def baseEnd_1061208 : Nat := 544909778396589252519599

theorem tailTrace_1061208 : CollatzResearch.WordTrace tailWord_1061208 prefixEnd_1061208 544909778396589252519599 := by
  unfold tailWord_1061208
  simp only [CollatzResearch.WordTrace]
  refine ⟨19352717769716065371132139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25803623692954753828176185 19352717769716065371132139)
  ·
    refine ⟨29029076654574098056698209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19352717769716065371132139 29029076654574098056698209)
    ·
      refine ⟨21771807490930573542523657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29029076654574098056698209 21771807490930573542523657)
      ·
        refine ⟨16328855618197930156892743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21771807490930573542523657 16328855618197930156892743)
        ·
          refine ⟨24493283427296895235339115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16328855618197930156892743 24493283427296895235339115)
          ·
            refine ⟨36739925140945342853008673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24493283427296895235339115 36739925140945342853008673)
            ·
              refine ⟨27554943855709007139756505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36739925140945342853008673 27554943855709007139756505)
              ·
                refine ⟨20666207891781755354817379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27554943855709007139756505 20666207891781755354817379)
                ·
                  refine ⟨30999311837672633032226069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20666207891781755354817379 30999311837672633032226069)
                  ·
                    refine ⟨1453092742390904673385597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30999311837672633032226069 1453092742390904673385597)
                    ·
                      refine ⟨544909778396589252519599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1453092742390904673385597 544909778396589252519599)
                      ·
                        rfl

theorem cell23_1061208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_1061208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061208 prefixEnd_1061208 := by exact prefixLift 1061208
  have htrace : WordTrace (prefixWord ++ tailWord_1061208) baseStart_1061208 baseEnd_1061208 := by
    simpa [prefixWord, tailWord_1061208, baseEnd_1061208] using wordTrace_append hprefix tailTrace_1061208
  have hstable : (prefixWord ++ tailWord_1061208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061208).length < 2 ^ (prefixWord ++ tailWord_1061208).sum := by decide
  have hdescent : baseEnd_1061208 < baseStart_1061208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061216 : List Nat := [2, 1, 1, 3, 6, 1, 1, 2, 2, 1, 3]
def baseStart_1061216 : Nat := 118140960795 + 1061216 * 2 ^ 59
def prefixEnd_1061216 : Nat := 4983230072969 + 3 ^ 40 * 1061216 * 2
def baseEnd_1061216 : Nat := 544913886241825221219563

theorem tailTrace_1061216 : CollatzResearch.WordTrace tailWord_1061216 prefixEnd_1061216 544913886241825221219563 := by
  unfold tailWord_1061216
  simp only [CollatzResearch.WordTrace]
  refine ⟨19352863661701574054277751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25803818215602098739037001 19352863661701574054277751)
  ·
    refine ⟨29029295492552361081416627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19352863661701574054277751 29029295492552361081416627)
    ·
      refine ⟨43543943238828541622124941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29029295492552361081416627 43543943238828541622124941)
      ·
        refine ⟨16328978714560703108296853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43543943238828541622124941 16328978714560703108296853)
        ·
          refine ⟨765420877245032958201415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16328978714560703108296853 765420877245032958201415)
          ·
            refine ⟨1148131315867549437302123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765420877245032958201415 1148131315867549437302123)
            ·
              refine ⟨1722196973801324155953185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148131315867549437302123 1722196973801324155953185)
              ·
                refine ⟨1291647730350993116964889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1722196973801324155953185 1291647730350993116964889)
                ·
                  refine ⟨968735797763244837723667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1291647730350993116964889 968735797763244837723667)
                  ·
                    refine ⟨1453103696644867256585501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 968735797763244837723667 1453103696644867256585501)
                    ·
                      refine ⟨544913886241825221219563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1453103696644867256585501 544913886241825221219563)
                      ·
                        rfl

theorem cell23_1061216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_1061216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061216 prefixEnd_1061216 := by exact prefixLift 1061216
  have htrace : WordTrace (prefixWord ++ tailWord_1061216) baseStart_1061216 baseEnd_1061216 := by
    simpa [prefixWord, tailWord_1061216, baseEnd_1061216] using wordTrace_append hprefix tailTrace_1061216
  have hstable : (prefixWord ++ tailWord_1061216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061216).length < 2 ^ (prefixWord ++ tailWord_1061216).sum := by decide
  have hdescent : baseEnd_1061216 < baseStart_1061216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061282 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_1061282 : Nat := 118140960795 + 1061282 * 2 ^ 59
def prefixEnd_1061282 : Nat := 4983230072969 + 3 ^ 40 * 1061282 * 2
def baseEnd_1061282 : Nat := 544947775965021962994259

theorem tailTrace_1061282 : CollatzResearch.WordTrace tailWord_1061282 prefixEnd_1061282 544947775965021962994259 := by
  unfold tailWord_1061282
  simp only [CollatzResearch.WordTrace]
  refine ⟨9677033635291010345114525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25805423027442694253638733 9677033635291010345114525)
  ·
    refine ⟨3628887613234128879417947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9677033635291010345114525 3628887613234128879417947)
    ·
      refine ⟨5443331419851193319126921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3628887613234128879417947 5443331419851193319126921)
      ·
        refine ⟨4082498564888394989345191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5443331419851193319126921 4082498564888394989345191)
        ·
          refine ⟨6123747847332592484017787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4082498564888394989345191 6123747847332592484017787)
          ·
            refine ⟨9185621770998888726026681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6123747847332592484017787 9185621770998888726026681)
            ·
              refine ⟨6889216328249166544520011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9185621770998888726026681 6889216328249166544520011)
              ·
                refine ⟨10333824492373749816780017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6889216328249166544520011 10333824492373749816780017)
                ·
                  refine ⟨7750368369280312362585013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10333824492373749816780017 7750368369280312362585013)
                  ·
                    refine ⟨726597034620029283992345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7750368369280312362585013 726597034620029283992345)
                    ·
                      refine ⟨544947775965021962994259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726597034620029283992345 544947775965021962994259)
                      ·
                        rfl

theorem cell23_1061282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_1061282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061282 prefixEnd_1061282 := by exact prefixLift 1061282
  have htrace : WordTrace (prefixWord ++ tailWord_1061282) baseStart_1061282 baseEnd_1061282 := by
    simpa [prefixWord, tailWord_1061282, baseEnd_1061282] using wordTrace_append hprefix tailTrace_1061282
  have hstable : (prefixWord ++ tailWord_1061282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061282).length < 2 ^ (prefixWord ++ tailWord_1061282).sum := by decide
  have hdescent : baseEnd_1061282 < baseStart_1061282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061290 : List Nat := [3, 1, 6, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_1061290 : Nat := 118140960795 + 1061290 * 2 ^ 59
def prefixEnd_1061290 : Nat := 4983230072969 + 3 ^ 40 * 1061290 * 2
def baseEnd_1061290 : Nat := 544951883810257931694223

theorem tailTrace_1061290 : CollatzResearch.WordTrace tailWord_1061290 prefixEnd_1061290 544951883810257931694223 := by
  unfold tailWord_1061290
  simp only [CollatzResearch.WordTrace]
  refine ⟨9677106581283764686687331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25805617550090039164499549 9677106581283764686687331)
  ·
    refine ⟨14515659871925647030030997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9677106581283764686687331 14515659871925647030030997)
    ·
      refine ⟨680421556496514704532703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14515659871925647030030997 680421556496514704532703)
      ·
        refine ⟨1020632334744772056799055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680421556496514704532703 1020632334744772056799055)
        ·
          refine ⟨1530948502117158085198583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020632334744772056799055 1530948502117158085198583)
          ·
            refine ⟨2296422753175737127797875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530948502117158085198583 2296422753175737127797875)
            ·
              refine ⟨3444634129763605691696813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2296422753175737127797875 3444634129763605691696813)
              ·
                refine ⟨1291737798661352134386305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3444634129763605691696813 1291737798661352134386305)
                ·
                  refine ⟨968803348996014100789729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1291737798661352134386305 968803348996014100789729)
                  ·
                    refine ⟨726602511747010575592297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 968803348996014100789729 726602511747010575592297)
                    ·
                      refine ⟨544951883810257931694223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726602511747010575592297 544951883810257931694223)
                      ·
                        rfl

theorem cell23_1061290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_1061290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061290 prefixEnd_1061290 := by exact prefixLift 1061290
  have htrace : WordTrace (prefixWord ++ tailWord_1061290) baseStart_1061290 baseEnd_1061290 := by
    simpa [prefixWord, tailWord_1061290, baseEnd_1061290] using wordTrace_append hprefix tailTrace_1061290
  have hstable : (prefixWord ++ tailWord_1061290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061290).length < 2 ^ (prefixWord ++ tailWord_1061290).sum := by decide
  have hdescent : baseEnd_1061290 < baseStart_1061290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061385 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 5, 1, 4]
def baseStart_1061385 : Nat := 118140960795 + 1061385 * 2 ^ 59
def prefixEnd_1061385 : Nat := 4983230072969 + 3 ^ 40 * 1061385 * 2
def baseEnd_1061385 : Nat := 545000664472435060006285

theorem tailTrace_1061385 : CollatzResearch.WordTrace tailWord_1061385 prefixEnd_1061385 545000664472435060006285 := by
  unfold tailWord_1061385
  simp only [CollatzResearch.WordTrace]
  refine ⟨38711891259790889971457609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25807927506527259980971739 38711891259790889971457609)
  ·
    refine ⟨29033918444843167478593207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38711891259790889971457609 29033918444843167478593207)
    ·
      refine ⟨43550877667264751217889811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29033918444843167478593207 43550877667264751217889811)
      ·
        refine ⟨65326316500897126826834717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43550877667264751217889811 65326316500897126826834717)
        ·
          refine ⟨24497368687836422560063019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65326316500897126826834717 24497368687836422560063019)
          ·
            refine ⟨36746053031754633840094529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24497368687836422560063019 36746053031754633840094529)
            ·
              refine ⟨27559539773815975380070897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36746053031754633840094529 27559539773815975380070897)
              ·
                refine ⟨20669654830361981535053173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27559539773815975380070897 20669654830361981535053173)
                ·
                  refine ⟨1937780140346435768911235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20669654830361981535053173 1937780140346435768911235)
                  ·
                    refine ⟨2906670210519653653366853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1937780140346435768911235 2906670210519653653366853)
                    ·
                      refine ⟨545000664472435060006285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2906670210519653653366853 545000664472435060006285)
                      ·
                        rfl

theorem cell23_1061385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_1061385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061385 prefixEnd_1061385 := by exact prefixLift 1061385
  have htrace : WordTrace (prefixWord ++ tailWord_1061385) baseStart_1061385 baseEnd_1061385 := by
    simpa [prefixWord, tailWord_1061385, baseEnd_1061385] using wordTrace_append hprefix tailTrace_1061385
  have hstable : (prefixWord ++ tailWord_1061385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061385).length < 2 ^ (prefixWord ++ tailWord_1061385).sum := by decide
  have hdescent : baseEnd_1061385 < baseStart_1061385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061389 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1061389 : Nat := 118140960795 + 1061389 * 2 ^ 59
def prefixEnd_1061389 : Nat := 4983230072969 + 3 ^ 40 * 1061389 * 2
def baseEnd_1061389 : Nat := 545002718395053044356267

theorem tailTrace_1061389 : CollatzResearch.WordTrace tailWord_1061389 prefixEnd_1061389 545002718395053044356267 := by
  unfold tailWord_1061389
  simp only [CollatzResearch.WordTrace]
  refine ⟨38712037151776398654603221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25808024767850932436402147 38712037151776398654603221)
  ·
    refine ⟨907313370744759343467263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 38712037151776398654603221 907313370744759343467263)
    ·
      refine ⟨1360970056117139015200895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 907313370744759343467263 1360970056117139015200895)
      ·
        refine ⟨2041455084175708522801343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1360970056117139015200895 2041455084175708522801343)
        ·
          refine ⟨3062182626263562784202015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2041455084175708522801343 3062182626263562784202015)
          ·
            refine ⟨4593273939395344176303023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062182626263562784202015 4593273939395344176303023)
            ·
              refine ⟨6889910909093016264454535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4593273939395344176303023 6889910909093016264454535)
              ·
                refine ⟨10334866363639524396681803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6889910909093016264454535 10334866363639524396681803)
                ·
                  refine ⟨15502299545459286595022705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10334866363639524396681803 15502299545459286595022705)
                  ·
                    refine ⟨11626724659094464946267029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15502299545459286595022705 11626724659094464946267029)
                    ·
                      refine ⟨545002718395053044356267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11626724659094464946267029 545002718395053044356267)
                      ·
                        rfl

theorem cell23_1061389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1061389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061389 prefixEnd_1061389 := by exact prefixLift 1061389
  have htrace : WordTrace (prefixWord ++ tailWord_1061389) baseStart_1061389 baseEnd_1061389 := by
    simpa [prefixWord, tailWord_1061389, baseEnd_1061389] using wordTrace_append hprefix tailTrace_1061389
  have hstable : (prefixWord ++ tailWord_1061389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061389).length < 2 ^ (prefixWord ++ tailWord_1061389).sum := by decide
  have hdescent : baseEnd_1061389 < baseStart_1061389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061396 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1061396 : Nat := 118140960795 + 1061396 * 2 ^ 59
def prefixEnd_1061396 : Nat := 4983230072969 + 3 ^ 40 * 1061396 * 2
def baseEnd_1061396 : Nat := 545006312759634516968735

theorem tailTrace_1061396 : CollatzResearch.WordTrace tailWord_1061396 prefixEnd_1061396 545006312759634516968735 := by
  unfold tailWord_1061396
  simp only [CollatzResearch.WordTrace]
  refine ⟨19356146231375519425054021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25808194975167359233405361 19356146231375519425054021)
  ·
    refine ⟨3629277418382909892197629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19356146231375519425054021 3629277418382909892197629)
    ·
      refine ⟨1360979031893591209574111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3629277418382909892197629 1360979031893591209574111)
      ·
        refine ⟨2041468547840386814361167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1360979031893591209574111 2041468547840386814361167)
        ·
          refine ⟨3062202821760580221541751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2041468547840386814361167 3062202821760580221541751)
          ·
            refine ⟨4593304232640870332312627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062202821760580221541751 4593304232640870332312627)
            ·
              refine ⟨6889956348961305498468941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4593304232640870332312627 6889956348961305498468941)
              ·
                refine ⟨2583733630860489561925853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6889956348961305498468941 2583733630860489561925853)
                ·
                  refine ⟨968900111572683585722195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2583733630860489561925853 968900111572683585722195)
                  ·
                    refine ⟨1453350167359025378583293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 968900111572683585722195 1453350167359025378583293)
                    ·
                      refine ⟨545006312759634516968735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1453350167359025378583293 545006312759634516968735)
                      ·
                        rfl

theorem cell23_1061396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1061396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061396 prefixEnd_1061396 := by exact prefixLift 1061396
  have htrace : WordTrace (prefixWord ++ tailWord_1061396) baseStart_1061396 baseEnd_1061396 := by
    simpa [prefixWord, tailWord_1061396, baseEnd_1061396] using wordTrace_append hprefix tailTrace_1061396
  have hstable : (prefixWord ++ tailWord_1061396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061396).length < 2 ^ (prefixWord ++ tailWord_1061396).sum := by decide
  have hdescent : baseEnd_1061396 < baseStart_1061396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061430 : List Nat := [5, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_1061430 : Nat := 118140960795 + 1061430 * 2 ^ 59
def prefixEnd_1061430 : Nat := 4983230072969 + 3 ^ 40 * 1061430 * 2
def baseEnd_1061430 : Nat := 545023771101887383943579

theorem tailTrace_1061430 : CollatzResearch.WordTrace tailWord_1061430 prefixEnd_1061430 545023771101887383943579 := by
  unfold tailWord_1061430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2419595784039241416052859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25809021696418575104563829 2419595784039241416052859)
  ·
    refine ⟨3629393676058862124079289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2419595784039241416052859 3629393676058862124079289)
    ·
      refine ⟨2722045257044146593059467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3629393676058862124079289 2722045257044146593059467)
      ·
        refine ⟨4083067885566219889589201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2722045257044146593059467 4083067885566219889589201)
        ·
          refine ⟨3062300914174664917191901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4083067885566219889589201 3062300914174664917191901)
          ·
            refine ⟨1148362842815499343946963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3062300914174664917191901 1148362842815499343946963)
            ·
              refine ⟨1722544264223249015920445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148362842815499343946963 1722544264223249015920445)
              ·
                refine ⟨645954099083718380970167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1722544264223249015920445 645954099083718380970167)
                ·
                  refine ⟨968931148625577571455251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645954099083718380970167 968931148625577571455251)
                  ·
                    refine ⟨1453396722938366357182877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 968931148625577571455251 1453396722938366357182877)
                    ·
                      refine ⟨545023771101887383943579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1453396722938366357182877 545023771101887383943579)
                      ·
                        rfl

theorem cell23_1061430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_1061430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061430 prefixEnd_1061430 := by exact prefixLift 1061430
  have htrace : WordTrace (prefixWord ++ tailWord_1061430) baseStart_1061430 baseEnd_1061430 := by
    simpa [prefixWord, tailWord_1061430, baseEnd_1061430] using wordTrace_append hprefix tailTrace_1061430
  have hstable : (prefixWord ++ tailWord_1061430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061430).length < 2 ^ (prefixWord ++ tailWord_1061430).sum := by decide
  have hdescent : baseEnd_1061430 < baseStart_1061430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061446 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1061446 : Nat := 118140960795 + 1061446 * 2 ^ 59
def prefixEnd_1061446 : Nat := 4983230072969 + 3 ^ 40 * 1061446 * 2
def baseEnd_1061446 : Nat := 181677328930786440447835

theorem tailTrace_1061446 : CollatzResearch.WordTrace tailWord_1061446 prefixEnd_1061446 181677328930786440447835 := by
  unfold tailWord_1061446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209816128517809293419631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25809410741713264926285461 1209816128517809293419631)
  ·
    refine ⟨1814724192776713940129447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1209816128517809293419631 1814724192776713940129447)
    ·
      refine ⟨2722086289165070910194171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1814724192776713940129447 2722086289165070910194171)
      ·
        refine ⟨4083129433747606365291257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2722086289165070910194171 4083129433747606365291257)
        ·
          refine ⟨3062347075310704773968443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4083129433747606365291257 3062347075310704773968443)
          ·
            refine ⟨4593520612966057160952665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062347075310704773968443 4593520612966057160952665)
            ·
              refine ⟨3445140459724542870714499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4593520612966057160952665 3445140459724542870714499)
              ·
                refine ⟨5167710689586814306071749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3445140459724542870714499 5167710689586814306071749)
                ·
                  refine ⟨968945754297527682388453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5167710689586814306071749 968945754297527682388453)
                  ·
                    refine ⟨181677328930786440447835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 968945754297527682388453 181677328930786440447835)
                    ·
                      rfl

theorem cell23_1061446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1061446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061446 prefixEnd_1061446 := by exact prefixLift 1061446
  have htrace : WordTrace (prefixWord ++ tailWord_1061446) baseStart_1061446 baseEnd_1061446 := by
    simpa [prefixWord, tailWord_1061446, baseEnd_1061446] using wordTrace_append hprefix tailTrace_1061446
  have hstable : (prefixWord ++ tailWord_1061446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061446).length < 2 ^ (prefixWord ++ tailWord_1061446).sum := by decide
  have hdescent : baseEnd_1061446 < baseStart_1061446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061453 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_1061453 : Nat := 118140960795 + 1061453 * 2 ^ 59
def prefixEnd_1061453 : Nat := 4983230072969 + 3 ^ 40 * 1061453 * 2
def baseEnd_1061453 : Nat := 545035581156940793955973

theorem tailTrace_1061453 : CollatzResearch.WordTrace tailWord_1061453 prefixEnd_1061453 545035581156940793955973 := by
  unfold tailWord_1061453
  simp only [CollatzResearch.WordTrace]
  refine ⟨38714371423544537584933013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25809580949029691723288675 38714371423544537584933013)
  ·
    refine ⟨1814736160478650199293735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38714371423544537584933013 1814736160478650199293735)
    ·
      refine ⟨2722104240717975298940603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1814736160478650199293735 2722104240717975298940603)
      ·
        refine ⟨4083156361076962948410905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2722104240717975298940603 4083156361076962948410905)
        ·
          refine ⟨3062367270807722211308179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4083156361076962948410905 3062367270807722211308179)
          ·
            refine ⟨4593550906211583316962269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062367270807722211308179 4593550906211583316962269)
            ·
              refine ⟨1722581589829343743860851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4593550906211583316962269 1722581589829343743860851)
              ·
                refine ⟨2583872384744015615791277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1722581589829343743860851 2583872384744015615791277)
                ·
                  refine ⟨968952144279005855921729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2583872384744015615791277 968952144279005855921729)
                  ·
                    refine ⟨726714108209254391941297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 968952144279005855921729 726714108209254391941297)
                    ·
                      refine ⟨545035581156940793955973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726714108209254391941297 545035581156940793955973)
                      ·
                        rfl

theorem cell23_1061453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_1061453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061453 prefixEnd_1061453 := by exact prefixLift 1061453
  have htrace : WordTrace (prefixWord ++ tailWord_1061453) baseStart_1061453 baseEnd_1061453 := by
    simpa [prefixWord, tailWord_1061453, baseEnd_1061453] using wordTrace_append hprefix tailTrace_1061453
  have hstable : (prefixWord ++ tailWord_1061453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061453).length < 2 ^ (prefixWord ++ tailWord_1061453).sum := by decide
  have hdescent : baseEnd_1061453 < baseStart_1061453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061532 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 9]
def baseStart_1061532 : Nat := 118140960795 + 1061532 * 2 ^ 59
def prefixEnd_1061532 : Nat := 4983230072969 + 3 ^ 40 * 1061532 * 2
def baseEnd_1061532 : Nat := 60564016236516220540901

theorem tailTrace_1061532 : CollatzResearch.WordTrace tailWord_1061532 prefixEnd_1061532 60564016236516220540901 := by
  unfold tailWord_1061532
  simp only [CollatzResearch.WordTrace]
  refine ⟨19358626395129167038529425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25811501860172222718039233 19358626395129167038529425)
  ·
    refine ⟨14518969796346875278897069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19358626395129167038529425 14518969796346875278897069)
    ·
      refine ⟨5444613673630078229586401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14518969796346875278897069 5444613673630078229586401)
      ·
        refine ⟨4083460255222558672189801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5444613673630078229586401 4083460255222558672189801)
        ·
          refine ⟨3062595191416919004142351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4083460255222558672189801 3062595191416919004142351)
          ·
            refine ⟨4593892787125378506213527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3062595191416919004142351 4593892787125378506213527)
            ·
              refine ⟨6890839180688067759320291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4593892787125378506213527 6890839180688067759320291)
              ·
                refine ⟨10336258771032101638980437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6890839180688067759320291 10336258771032101638980437)
                ·
                  refine ⟨60564016236516220540901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10336258771032101638980437 60564016236516220540901)
                  ·
                    rfl

theorem cell23_1061532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_1061532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061532 prefixEnd_1061532 := by exact prefixLift 1061532
  have htrace : WordTrace (prefixWord ++ tailWord_1061532) baseStart_1061532 baseEnd_1061532 := by
    simpa [prefixWord, tailWord_1061532, baseEnd_1061532] using wordTrace_append hprefix tailTrace_1061532
  have hstable : (prefixWord ++ tailWord_1061532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061532).length < 2 ^ (prefixWord ++ tailWord_1061532).sum := by decide
  have hdescent : baseEnd_1061532 < baseStart_1061532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061562 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 4, 5]
def baseStart_1061562 : Nat := 118140960795 + 1061562 * 2 ^ 59
def prefixEnd_1061562 : Nat := 4983230072969 + 3 ^ 40 * 1061562 * 2
def baseEnd_1061562 : Nat := 181697183516093622497657

theorem tailTrace_1061562 : CollatzResearch.WordTrace tailWord_1061562 prefixEnd_1061562 181697183516093622497657 := by
  unfold tailWord_1061562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9679586745037412300162735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25812231320099766133767293 9679586745037412300162735)
  ·
    refine ⟨14519380117556118450244103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9679586745037412300162735 14519380117556118450244103)
    ·
      refine ⟨21779070176334177675366155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14519380117556118450244103 21779070176334177675366155)
      ·
        refine ⟨32668605264501266513049233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21779070176334177675366155 32668605264501266513049233)
        ·
          refine ⟨24501453948375949884786925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32668605264501266513049233 24501453948375949884786925)
          ·
            refine ⟨9188045230640981206795097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24501453948375949884786925 9188045230640981206795097)
            ·
              refine ⟨6891033922980735905096323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9188045230640981206795097 6891033922980735905096323)
              ·
                refine ⟨10336550884471103857644485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6891033922980735905096323 10336550884471103857644485)
                ·
                  refine ⟨1938103290838331973308341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10336550884471103857644485 1938103290838331973308341)
                  ·
                    refine ⟨181697183516093622497657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1938103290838331973308341 181697183516093622497657)
                    ·
                      rfl

theorem cell23_1061562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_1061562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061562 prefixEnd_1061562 := by exact prefixLift 1061562
  have htrace : WordTrace (prefixWord ++ tailWord_1061562) baseStart_1061562 baseEnd_1061562 := by
    simpa [prefixWord, tailWord_1061562, baseEnd_1061562] using wordTrace_append hprefix tailTrace_1061562
  have hstable : (prefixWord ++ tailWord_1061562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061562).length < 2 ^ (prefixWord ++ tailWord_1061562).sum := by decide
  have hdescent : baseEnd_1061562 < baseStart_1061562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061626 : List Nat := [3, 1, 1, 1, 1, 3, 2, 6, 1, 4]
def baseStart_1061626 : Nat := 118140960795 + 1061626 * 2 ^ 59
def prefixEnd_1061626 : Nat := 4983230072969 + 3 ^ 40 * 1061626 * 2
def baseEnd_1061626 : Nat := 181708137770056205697559

theorem tailTrace_1061626 : CollatzResearch.WordTrace tailWord_1061626 prefixEnd_1061626 181708137770056205697559 := by
  unfold tailWord_1061626
  simp only [CollatzResearch.WordTrace]
  refine ⟨9680170312979447032745183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25813787501278525420653821 9680170312979447032745183)
  ·
    refine ⟨14520255469469170549117775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9680170312979447032745183 14520255469469170549117775)
    ·
      refine ⟨21780383204203755823676663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14520255469469170549117775 21780383204203755823676663)
      ·
        refine ⟨32670574806305633735514995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21780383204203755823676663 32670574806305633735514995)
        ·
          refine ⟨49005862209458450603272493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32670574806305633735514995 49005862209458450603272493)
          ·
            refine ⟨18377198328546918976227185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49005862209458450603272493 18377198328546918976227185)
            ·
              refine ⟨13782898746410189232170389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18377198328546918976227185 13782898746410189232170389)
              ·
                refine ⟨646073378737977620257987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13782898746410189232170389 646073378737977620257987)
                ·
                  refine ⟨969110068106966430386981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646073378737977620257987 969110068106966430386981)
                  ·
                    refine ⟨181708137770056205697559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 969110068106966430386981 181708137770056205697559)
                    ·
                      rfl

theorem cell23_1061626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_1061626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061626 prefixEnd_1061626 := by exact prefixLift 1061626
  have htrace : WordTrace (prefixWord ++ tailWord_1061626) baseStart_1061626 baseEnd_1061626 := by
    simpa [prefixWord, tailWord_1061626, baseEnd_1061626] using wordTrace_append hprefix tailTrace_1061626
  have hstable : (prefixWord ++ tailWord_1061626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061626).length < 2 ^ (prefixWord ++ tailWord_1061626).sum := by decide
  have hdescent : baseEnd_1061626 < baseStart_1061626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061676 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 2, 3, 2]
def baseStart_1061676 : Nat := 118140960795 + 1061676 * 2 ^ 59
def prefixEnd_1061676 : Nat := 4983230072969 + 3 ^ 40 * 1061676 * 2
def baseEnd_1061676 : Nat := 545150087342893421467447

theorem tailTrace_1061676 : CollatzResearch.WordTrace tailWord_1061676 prefixEnd_1061676 545150087342893421467447 := by
  unfold tailWord_1061676
  simp only [CollatzResearch.WordTrace]
  refine ⟨19361252450868323335150441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25815003267824431113533921 19361252450868323335150441)
  ·
    refine ⟨14520939338151242501362831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19361252450868323335150441 14520939338151242501362831)
    ·
      refine ⟨21781409007226863752044247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14520939338151242501362831 21781409007226863752044247)
      ·
        refine ⟨32672113510840295628066371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21781409007226863752044247 32672113510840295628066371)
        ·
          refine ⟨49008170266260443442099557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32672113510840295628066371 49008170266260443442099557)
          ·
            refine ⟨9189031924923833145393667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49008170266260443442099557 9189031924923833145393667)
            ·
              refine ⟨13783547887385749718090501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9189031924923833145393667 13783547887385749718090501)
              ·
                refine ⟨2584415228884828072141969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13783547887385749718090501 2584415228884828072141969)
                ·
                  refine ⟨1938311421663621054106477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2584415228884828072141969 1938311421663621054106477)
                  ·
                    refine ⟨726866783123857895289929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938311421663621054106477 726866783123857895289929)
                    ·
                      refine ⟨545150087342893421467447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726866783123857895289929 545150087342893421467447)
                      ·
                        rfl

theorem cell23_1061676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 3, 2].length) (baseStart_1061676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061676 prefixEnd_1061676 := by exact prefixLift 1061676
  have htrace : WordTrace (prefixWord ++ tailWord_1061676) baseStart_1061676 baseEnd_1061676 := by
    simpa [prefixWord, tailWord_1061676, baseEnd_1061676] using wordTrace_append hprefix tailTrace_1061676
  have hstable : (prefixWord ++ tailWord_1061676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061676).length < 2 ^ (prefixWord ++ tailWord_1061676).sum := by decide
  have hdescent : baseEnd_1061676 < baseStart_1061676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061677 : List Nat := [1, 5, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1061677 : Nat := 118140960795 + 1061677 * 2 ^ 59
def prefixEnd_1061677 : Nat := 4983230072969 + 3 ^ 40 * 1061677 * 2
def baseEnd_1061677 : Nat := 181716866941182639184981

theorem tailTrace_1061677 : CollatzResearch.WordTrace tailWord_1061677 prefixEnd_1061677 181716866941182639184981 := by
  unfold tailWord_1061677
  simp only [CollatzResearch.WordTrace]
  refine ⟨38722541374733023841087285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25815027583155349227391523 38722541374733023841087285)
  ·
    refine ⟨3630238253881220985101933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38722541374733023841087285 3630238253881220985101933)
    ·
      refine ⟨1361339345205457869413225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3630238253881220985101933 1361339345205457869413225)
      ·
        refine ⟨1021004508904093402059919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1361339345205457869413225 1021004508904093402059919)
        ·
          refine ⟨1531506763356140103089879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021004508904093402059919 1531506763356140103089879)
          ·
            refine ⟨2297260145034210154634819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531506763356140103089879 2297260145034210154634819)
            ·
              refine ⟨3445890217551315231952229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297260145034210154634819 3445890217551315231952229)
              ·
                refine ⟨646104415790871605991043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3445890217551315231952229 646104415790871605991043)
                ·
                  refine ⟨969156623686307408986565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646104415790871605991043 969156623686307408986565)
                  ·
                    refine ⟨181716866941182639184981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 969156623686307408986565 181716866941182639184981)
                    ·
                      rfl

theorem cell23_1061677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1061677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061677 prefixEnd_1061677 := by exact prefixLift 1061677
  have htrace : WordTrace (prefixWord ++ tailWord_1061677) baseStart_1061677 baseEnd_1061677 := by
    simpa [prefixWord, tailWord_1061677, baseEnd_1061677] using wordTrace_append hprefix tailTrace_1061677
  have hstable : (prefixWord ++ tailWord_1061677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061677).length < 2 ^ (prefixWord ++ tailWord_1061677).sum := by decide
  have hdescent : baseEnd_1061677 < baseStart_1061677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061699 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 1, 6]
def baseStart_1061699 : Nat := 118140960795 + 1061699 * 2 ^ 59
def prefixEnd_1061699 : Nat := 4983230072969 + 3 ^ 40 * 1061699 * 2
def baseEnd_1061699 : Nat := 181720632465982277159947

theorem tailTrace_1061699 : CollatzResearch.WordTrace tailWord_1061699 prefixEnd_1061699 181720632465982277159947 := by
  unfold tailWord_1061699
  simp only [CollatzResearch.WordTrace]
  refine ⟨38723343780653321598388151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25815562520435547732258767 38723343780653321598388151)
  ·
    refine ⟨58085015670979982397582227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38723343780653321598388151 58085015670979982397582227)
    ·
      refine ⟨87127523506469973596373341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58085015670979982397582227 87127523506469973596373341)
      ·
        refine ⟨32672821314926240098640003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87127523506469973596373341 32672821314926240098640003)
        ·
          refine ⟨49009231972389360147960005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32672821314926240098640003 49009231972389360147960005)
          ·
            refine ⟨9189230994823005027742501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49009231972389360147960005 9189230994823005027742501)
            ·
              refine ⟨1722980811529313442701719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9189230994823005027742501 1722980811529313442701719)
              ·
                refine ⟨2584471217293970164052579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1722980811529313442701719 2584471217293970164052579)
                ·
                  refine ⟨3876706825940955246078869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584471217293970164052579 3876706825940955246078869)
                  ·
                    refine ⟨181720632465982277159947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3876706825940955246078869 181720632465982277159947)
                    ·
                      rfl

theorem cell23_1061699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 6].length) (baseStart_1061699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061699 prefixEnd_1061699 := by exact prefixLift 1061699
  have htrace : WordTrace (prefixWord ++ tailWord_1061699) baseStart_1061699 baseEnd_1061699 := by
    simpa [prefixWord, tailWord_1061699, baseEnd_1061699] using wordTrace_append hprefix tailTrace_1061699
  have hstable : (prefixWord ++ tailWord_1061699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061699).length < 2 ^ (prefixWord ++ tailWord_1061699).sum := by decide
  have hdescent : baseEnd_1061699 < baseStart_1061699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061712 : List Nat := [2, 1, 1, 1, 1, 4, 2, 11]
def baseStart_1061712 : Nat := 118140960795 + 1061712 * 2 ^ 59
def prefixEnd_1061712 : Nat := 4983230072969 + 3 ^ 40 * 1061712 * 2
def baseEnd_1061712 : Nat := 20191428616535380763603

theorem tailTrace_1061712 : CollatzResearch.WordTrace tailWord_1061712 prefixEnd_1061712 20191428616535380763603 := by
  unfold tailWord_1061712
  simp only [CollatzResearch.WordTrace]
  refine ⟨19361908964803112409305695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25815878619737483212407593 19361908964803112409305695)
  ·
    refine ⟨29042863447204668613958543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19361908964803112409305695 29042863447204668613958543)
    ·
      refine ⟨43564295170807002920937815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29042863447204668613958543 43564295170807002920937815)
      ·
        refine ⟨65346442756210504381406723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43564295170807002920937815 65346442756210504381406723)
        ·
          refine ⟨98019664134315756572110085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65346442756210504381406723 98019664134315756572110085)
          ·
            refine ⟨18378687025184204357270641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98019664134315756572110085 18378687025184204357270641)
            ·
              refine ⟨13784015268888153267952981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18378687025184204357270641 13784015268888153267952981)
              ·
                refine ⟨20191428616535380763603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 13784015268888153267952981 20191428616535380763603)
                ·
                  rfl

theorem cell23_1061712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 11].length) (baseStart_1061712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061712 prefixEnd_1061712 := by exact prefixLift 1061712
  have htrace : WordTrace (prefixWord ++ tailWord_1061712) baseStart_1061712 baseEnd_1061712 := by
    simpa [prefixWord, tailWord_1061712, baseEnd_1061712] using wordTrace_append hprefix tailTrace_1061712
  have hstable : (prefixWord ++ tailWord_1061712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061712).length < 2 ^ (prefixWord ++ tailWord_1061712).sum := by decide
  have hdescent : baseEnd_1061712 < baseStart_1061712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061739 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 3]
def baseStart_1061739 : Nat := 118140960795 + 1061739 * 2 ^ 59
def prefixEnd_1061739 : Nat := 4983230072969 + 3 ^ 40 * 1061739 * 2
def baseEnd_1061739 : Nat := 545182436624126674979657

theorem tailTrace_1061739 : CollatzResearch.WordTrace tailWord_1061739 prefixEnd_1061739 545182436624126674979657 := by
  unfold tailWord_1061739
  simp only [CollatzResearch.WordTrace]
  refine ⟨38724802700508408429844271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25816535133672272286562847 38724802700508408429844271)
  ·
    refine ⟨58087204050762612644766407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38724802700508408429844271 58087204050762612644766407)
    ·
      refine ⟨87130806076143918967149611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58087204050762612644766407 87130806076143918967149611)
      ·
        refine ⟨130696209114215878450724417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87130806076143918967149611 130696209114215878450724417)
        ·
          refine ⟨98022156835661908838043313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130696209114215878450724417 98022156835661908838043313)
          ·
            refine ⟨73516617626746431628532485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98022156835661908838043313 73516617626746431628532485)
            ·
              refine ⟨13784365805014955930349841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73516617626746431628532485 13784365805014955930349841)
              ·
                refine ⟨10338274353761216947762381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13784365805014955930349841 10338274353761216947762381)
                ·
                  refine ⟨3876852882660456355410893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10338274353761216947762381 3876852882660456355410893)
                  ·
                    refine ⟨1453819830997671133279085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3876852882660456355410893 1453819830997671133279085)
                    ·
                      refine ⟨545182436624126674979657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1453819830997671133279085 545182436624126674979657)
                      ·
                        rfl

theorem cell23_1061739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 3].length) (baseStart_1061739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061739 prefixEnd_1061739 := by exact prefixLift 1061739
  have htrace : WordTrace (prefixWord ++ tailWord_1061739) baseStart_1061739 baseEnd_1061739 := by
    simpa [prefixWord, tailWord_1061739, baseEnd_1061739] using wordTrace_append hprefix tailTrace_1061739
  have hstable : (prefixWord ++ tailWord_1061739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061739).length < 2 ^ (prefixWord ++ tailWord_1061739).sum := by decide
  have hdescent : baseEnd_1061739 < baseStart_1061739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061740 : List Nat := [2, 2, 1, 1, 4, 1, 1, 6, 1, 2, 2]
def baseStart_1061740 : Nat := 118140960795 + 1061740 * 2 ^ 59
def prefixEnd_1061740 : Nat := 4983230072969 + 3 ^ 40 * 1061740 * 2
def baseEnd_1061740 : Nat := 545182950104781171067153

theorem tailTrace_1061740 : CollatzResearch.WordTrace tailWord_1061740 prefixEnd_1061740 545182950104781171067153 := by
  unfold tailWord_1061740
  simp only [CollatzResearch.WordTrace]
  refine ⟨19362419586752392800315337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25816559449003190400420449 19362419586752392800315337)
  ·
    refine ⟨14521814690064294600236503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19362419586752392800315337 14521814690064294600236503)
    ·
      refine ⟨21782722035096441900354755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14521814690064294600236503 21782722035096441900354755)
      ·
        refine ⟨32674083052644662850532133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21782722035096441900354755 32674083052644662850532133)
        ·
          refine ⟨6126390572370874284474775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32674083052644662850532133 6126390572370874284474775)
          ·
            refine ⟨9189585858556311426712163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6126390572370874284474775 9189585858556311426712163)
            ·
              refine ⟨13784378787834467140068245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9189585858556311426712163 13784378787834467140068245)
              ·
                refine ⟨646142755679740647190699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13784378787834467140068245 646142755679740647190699)
                ·
                  refine ⟨969214133519610970786049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646142755679740647190699 969214133519610970786049)
                  ·
                    refine ⟨726910600139708228089537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 969214133519610970786049 726910600139708228089537)
                    ·
                      refine ⟨545182950104781171067153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726910600139708228089537 545182950104781171067153)
                      ·
                        rfl

theorem cell23_1061740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 1, 2, 2].length) (baseStart_1061740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061740 prefixEnd_1061740 := by exact prefixLift 1061740
  have htrace : WordTrace (prefixWord ++ tailWord_1061740) baseStart_1061740 baseEnd_1061740 := by
    simpa [prefixWord, tailWord_1061740, baseEnd_1061740] using wordTrace_append hprefix tailTrace_1061740
  have hstable : (prefixWord ++ tailWord_1061740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061740).length < 2 ^ (prefixWord ++ tailWord_1061740).sum := by decide
  have hdescent : baseEnd_1061740 < baseStart_1061740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061769 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 2, 2, 5]
def baseStart_1061769 : Nat := 118140960795 + 1061769 * 2 ^ 59
def prefixEnd_1061769 : Nat := 4983230072969 + 3 ^ 40 * 1061769 * 2
def baseEnd_1061769 : Nat := 545197841043761557604519

theorem tailTrace_1061769 : CollatzResearch.WordTrace tailWord_1061769 prefixEnd_1061769 545197841043761557604519 := by
  unfold tailWord_1061769
  simp only [CollatzResearch.WordTrace]
  refine ⟨38725896890399723553436361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25817264593599815702290907 38725896890399723553436361)
  ·
    refine ⟨29044422667799792665077271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38725896890399723553436361 29044422667799792665077271)
    ·
      refine ⟨43566634001699688997615907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29044422667799792665077271 43566634001699688997615907)
      ·
        refine ⟨65349951002549533496423861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43566634001699688997615907 65349951002549533496423861)
        ·
          refine ⟨6126557906489018765289737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65349951002549533496423861 6126557906489018765289737)
          ·
            refine ⟨4594918429866764073967303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6126557906489018765289737 4594918429866764073967303)
            ·
              refine ⟨6892377644800146110950955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594918429866764073967303 6892377644800146110950955)
              ·
                refine ⟨10338566467200219166426433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6892377644800146110950955 10338566467200219166426433)
                ·
                  refine ⟨7753924850400164374819825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10338566467200219166426433 7753924850400164374819825)
                  ·
                    refine ⟨5815443637800123281114869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7753924850400164374819825 5815443637800123281114869)
                    ·
                      refine ⟨545197841043761557604519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5815443637800123281114869 545197841043761557604519)
                      ·
                        rfl

theorem cell23_1061769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_1061769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061769 prefixEnd_1061769 := by exact prefixLift 1061769
  have htrace : WordTrace (prefixWord ++ tailWord_1061769) baseStart_1061769 baseEnd_1061769 := by
    simpa [prefixWord, tailWord_1061769, baseEnd_1061769] using wordTrace_append hprefix tailTrace_1061769
  have hstable : (prefixWord ++ tailWord_1061769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061769).length < 2 ^ (prefixWord ++ tailWord_1061769).sum := by decide
  have hdescent : baseEnd_1061769 < baseStart_1061769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061783 : List Nat := [1, 1, 3, 3, 1, 2, 1, 5, 1, 3, 2]
def baseStart_1061783 : Nat := 118140960795 + 1061783 * 2 ^ 59
def prefixEnd_1061783 : Nat := 4983230072969 + 3 ^ 40 * 1061783 * 2
def baseEnd_1061783 : Nat := 545205029772924502829455

theorem tailTrace_1061783 : CollatzResearch.WordTrace tailWord_1061783 prefixEnd_1061783 545205029772924502829455 := by
  unfold tailWord_1061783
  simp only [CollatzResearch.WordTrace]
  refine ⟨38726407512349003944446003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25817605008232669296297335 38726407512349003944446003)
  ·
    refine ⟨58089611268523505916669005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38726407512349003944446003 58089611268523505916669005)
    ·
      refine ⟨21783604225696314718750877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58089611268523505916669005 21783604225696314718750877)
      ·
        refine ⟨8168851584636118019531579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21783604225696314718750877 8168851584636118019531579)
        ·
          refine ⟨12253277376954177029297369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8168851584636118019531579 12253277376954177029297369)
          ·
            refine ⟨9189958032715632771973027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12253277376954177029297369 9189958032715632771973027)
            ·
              refine ⟨13784937049073449157959541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9189958032715632771973027 13784937049073449157959541)
              ·
                refine ⟨1292337848350635858558707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13784937049073449157959541 1292337848350635858558707)
                ·
                  refine ⟨1938506772525953787838061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292337848350635858558707 1938506772525953787838061)
                  ·
                    refine ⟨726940039697232670439273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938506772525953787838061 726940039697232670439273)
                    ·
                      refine ⟨545205029772924502829455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726940039697232670439273 545205029772924502829455)
                      ·
                        rfl

theorem cell23_1061783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_1061783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061783 prefixEnd_1061783 := by exact prefixLift 1061783
  have htrace : WordTrace (prefixWord ++ tailWord_1061783) baseStart_1061783 baseEnd_1061783 := by
    simpa [prefixWord, tailWord_1061783, baseEnd_1061783] using wordTrace_append hprefix tailTrace_1061783
  have hstable : (prefixWord ++ tailWord_1061783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061783).length < 2 ^ (prefixWord ++ tailWord_1061783).sum := by decide
  have hdescent : baseEnd_1061783 < baseStart_1061783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061813 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_1061813 : Nat := 118140960795 + 1061813 * 2 ^ 59
def prefixEnd_1061813 : Nat := 4983230072969 + 3 ^ 40 * 1061813 * 2
def baseEnd_1061813 : Nat := 545220434192559385454317

theorem tailTrace_1061813 : CollatzResearch.WordTrace tailWord_1061813 prefixEnd_1061813 545220434192559385454317 := by
  unfold tailWord_1061813
  simp only [CollatzResearch.WordTrace]
  refine ⟨38727501702240319068038093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25818334468160212712025395 38727501702240319068038093)
  ·
    refine ⟨14522813138340119650514285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38727501702240319068038093 14522813138340119650514285)
    ·
      refine ⟨5446054926877544868942857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14522813138340119650514285 5446054926877544868942857)
      ·
        refine ⟨4084541195158158651707143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5446054926877544868942857 4084541195158158651707143)
        ·
          refine ⟨6126811792737237977560715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4084541195158158651707143 6126811792737237977560715)
          ·
            refine ⟨9190217689105856966341073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6126811792737237977560715 9190217689105856966341073)
            ·
              refine ⟨6892663266829392724755805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9190217689105856966341073 6892663266829392724755805)
              ·
                refine ⟨2584748725061022271783427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6892663266829392724755805 2584748725061022271783427)
                ·
                  refine ⟨3877123087591533407675141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584748725061022271783427 3877123087591533407675141)
                  ·
                    refine ⟨726960578923412513939089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3877123087591533407675141 726960578923412513939089)
                    ·
                      refine ⟨545220434192559385454317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 726960578923412513939089 545220434192559385454317)
                      ·
                        rfl

theorem cell23_1061813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_1061813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061813 prefixEnd_1061813 := by exact prefixLift 1061813
  have htrace : WordTrace (prefixWord ++ tailWord_1061813) baseStart_1061813 baseEnd_1061813 := by
    simpa [prefixWord, tailWord_1061813, baseEnd_1061813] using wordTrace_append hprefix tailTrace_1061813
  have hstable : (prefixWord ++ tailWord_1061813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061813).length < 2 ^ (prefixWord ++ tailWord_1061813).sum := by decide
  have hdescent : baseEnd_1061813 < baseStart_1061813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061863 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_1061863 : Nat := 118140960795 + 1061863 * 2 ^ 59
def prefixEnd_1061863 : Nat := 4983230072969 + 3 ^ 40 * 1061863 * 2
def baseEnd_1061863 : Nat := 545246108225284189829087

theorem tailTrace_1061863 : CollatzResearch.WordTrace tailWord_1061863 prefixEnd_1061863 545246108225284189829087 := by
  unfold tailWord_1061863
  simp only [CollatzResearch.WordTrace]
  refine ⟨38729325352059177607358243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25819550234706118404905495 38729325352059177607358243)
  ·
    refine ⟨58093988028088766411037365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38729325352059177607358243 58093988028088766411037365)
    ·
      refine ⟨5446311377633321851034753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58093988028088766411037365 5446311377633321851034753)
      ·
        refine ⟨4084733533224991388276065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5446311377633321851034753 4084733533224991388276065)
        ·
          refine ⟨3063550149918743541207049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4084733533224991388276065 3063550149918743541207049)
          ·
            refine ⟨2297662612439057655905287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3063550149918743541207049 2297662612439057655905287)
            ·
              refine ⟨3446493918658586483857931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297662612439057655905287 3446493918658586483857931)
              ·
                refine ⟨5169740877987879725786897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3446493918658586483857931 5169740877987879725786897)
                ·
                  refine ⟨3877305658490909794340173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5169740877987879725786897 3877305658490909794340173)
                  ·
                    refine ⟨1453989621934091172877565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3877305658490909794340173 1453989621934091172877565)
                    ·
                      refine ⟨545246108225284189829087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1453989621934091172877565 545246108225284189829087)
                      ·
                        rfl

theorem cell23_1061863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_1061863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061863 prefixEnd_1061863 := by exact prefixLift 1061863
  have htrace : WordTrace (prefixWord ++ tailWord_1061863) baseStart_1061863 baseEnd_1061863 := by
    simpa [prefixWord, tailWord_1061863, baseEnd_1061863] using wordTrace_append hprefix tailTrace_1061863
  have hstable : (prefixWord ++ tailWord_1061863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061863).length < 2 ^ (prefixWord ++ tailWord_1061863).sum := by decide
  have hdescent : baseEnd_1061863 < baseStart_1061863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061936 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 3]
def baseStart_1061936 : Nat := 118140960795 + 1061936 * 2 ^ 59
def prefixEnd_1061936 : Nat := 4983230072969 + 3 ^ 40 * 1061936 * 2
def baseEnd_1061936 : Nat := 545283592313062404216251

theorem tailTrace_1061936 : CollatzResearch.WordTrace tailWord_1061936 prefixEnd_1061936 545283592313062404216251 := by
  unfold tailWord_1061936
  simp only [CollatzResearch.WordTrace]
  refine ⟨19365993940397355537382831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25821325253863140716510441 19365993940397355537382831)
  ·
    refine ⟨29048990910596033306074247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19365993940397355537382831 29048990910596033306074247)
    ·
      refine ⟨43573486365894049959111371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29048990910596033306074247 43573486365894049959111371)
      ·
        refine ⟨65360229548841074938667057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43573486365894049959111371 65360229548841074938667057)
        ·
          refine ⟨49020172161630806204000293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65360229548841074938667057 49020172161630806204000293)
          ·
            refine ⟨9191282280305776163250055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49020172161630806204000293 9191282280305776163250055)
            ·
              refine ⟨13786923420458664244875083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9191282280305776163250055 13786923420458664244875083)
              ·
                refine ⟨20680385130687996367312625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13786923420458664244875083 20680385130687996367312625)
                ·
                  refine ⟨15510288848015997275484469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20680385130687996367312625 15510288848015997275484469)
                  ·
                    refine ⟨1454089579501499744576669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15510288848015997275484469 1454089579501499744576669)
                    ·
                      refine ⟨545283592313062404216251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1454089579501499744576669 545283592313062404216251)
                      ·
                        rfl

theorem cell23_1061936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 3].length) (baseStart_1061936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061936 prefixEnd_1061936 := by exact prefixLift 1061936
  have htrace : WordTrace (prefixWord ++ tailWord_1061936) baseStart_1061936 baseEnd_1061936 := by
    simpa [prefixWord, tailWord_1061936, baseEnd_1061936] using wordTrace_append hprefix tailTrace_1061936
  have hstable : (prefixWord ++ tailWord_1061936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061936).length < 2 ^ (prefixWord ++ tailWord_1061936).sum := by decide
  have hdescent : baseEnd_1061936 < baseStart_1061936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061940 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1061940 : Nat := 118140960795 + 1061940 * 2 ^ 59
def prefixEnd_1061940 : Nat := 4983230072969 + 3 ^ 40 * 1061940 * 2
def baseEnd_1061940 : Nat := 545285646235680388566233

theorem tailTrace_1061940 : CollatzResearch.WordTrace tailWord_1061940 prefixEnd_1061940 545285646235680388566233 := by
  unfold tailWord_1061940
  simp only [CollatzResearch.WordTrace]
  refine ⟨19366066886390109878955637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25821422515186813171940849 19366066886390109878955637)
  ·
    refine ⟨1815568770599072801152091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19366066886390109878955637 1815568770599072801152091)
    ·
      refine ⟨2723353155898609201728137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1815568770599072801152091 2723353155898609201728137)
      ·
        refine ⟨2042514866923956901296103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2723353155898609201728137 2042514866923956901296103)
        ·
          refine ⟨3063772300385935351944155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2042514866923956901296103 3063772300385935351944155)
          ·
            refine ⟨4595658450578903027916233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063772300385935351944155 4595658450578903027916233)
            ·
              refine ⟨3446743837934177270937175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4595658450578903027916233 3446743837934177270937175)
              ·
                refine ⟨5170115756901265906405763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3446743837934177270937175 5170115756901265906405763)
                ·
                  refine ⟨7755173635351898859608645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5170115756901265906405763 7755173635351898859608645)
                  ·
                    refine ⟨1454095056628481036176621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7755173635351898859608645 1454095056628481036176621)
                    ·
                      refine ⟨545285646235680388566233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1454095056628481036176621 545285646235680388566233)
                      ·
                        rfl

theorem cell23_1061940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1061940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061940 prefixEnd_1061940 := by exact prefixLift 1061940
  have htrace : WordTrace (prefixWord ++ tailWord_1061940) baseStart_1061940 baseEnd_1061940 := by
    simpa [prefixWord, tailWord_1061940, baseEnd_1061940] using wordTrace_append hprefix tailTrace_1061940
  have hstable : (prefixWord ++ tailWord_1061940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061940).length < 2 ^ (prefixWord ++ tailWord_1061940).sum := by decide
  have hdescent : baseEnd_1061940 < baseStart_1061940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061980 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_1061980 : Nat := 118140960795 + 1061980 * 2 ^ 59
def prefixEnd_1061980 : Nat := 4983230072969 + 3 ^ 40 * 1061980 * 2
def baseEnd_1061980 : Nat := 545306185461860232066049

theorem tailTrace_1061980 : CollatzResearch.WordTrace tailWord_1061980 prefixEnd_1061980 545306185461860232066049 := by
  unfold tailWord_1061980
  simp only [CollatzResearch.WordTrace]
  refine ⟨19366796346317653294683697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25822395128423537726244929 19366796346317653294683697)
  ·
    refine ⟨14525097259738239971012773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19366796346317653294683697 14525097259738239971012773)
    ·
      refine ⟨2723455736200919994564895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14525097259738239971012773 2723455736200919994564895)
      ·
        refine ⟨4085183604301379991847343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2723455736200919994564895 4085183604301379991847343)
        ·
          refine ⟨6127775406452069987771015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4085183604301379991847343 6127775406452069987771015)
          ·
            refine ⟨9191663109678104981656523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6127775406452069987771015 9191663109678104981656523)
            ·
              refine ⟨13787494664517157472484785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9191663109678104981656523 13787494664517157472484785)
              ·
                refine ⟨10340620998387868104363589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13787494664517157472484785 10340620998387868104363589)
                ·
                  refine ⟨1938866437197725269568173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10340620998387868104363589 1938866437197725269568173)
                  ·
                    refine ⟨727074913949146976088065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938866437197725269568173 727074913949146976088065)
                    ·
                      refine ⟨545306185461860232066049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727074913949146976088065 545306185461860232066049)
                      ·
                        rfl

theorem cell23_1061980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_1061980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061980 prefixEnd_1061980 := by exact prefixLift 1061980
  have htrace : WordTrace (prefixWord ++ tailWord_1061980) baseStart_1061980 baseEnd_1061980 := by
    simpa [prefixWord, tailWord_1061980, baseEnd_1061980] using wordTrace_append hprefix tailTrace_1061980
  have hstable : (prefixWord ++ tailWord_1061980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061980).length < 2 ^ (prefixWord ++ tailWord_1061980).sum := by decide
  have hdescent : baseEnd_1061980 < baseStart_1061980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061993 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 3, 1, 4]
def baseStart_1061993 : Nat := 118140960795 + 1061993 * 2 ^ 59
def prefixEnd_1061993 : Nat := 4983230072969 + 3 ^ 40 * 1061993 * 2
def baseEnd_1061993 : Nat := 545312860710368681203489

theorem tailTrace_1061993 : CollatzResearch.WordTrace tailWord_1061993 prefixEnd_1061993 545312860710368681203489 := by
  unfold tailWord_1061993
  simp only [CollatzResearch.WordTrace]
  refine ⟨38734066841588209809590633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25822711227725473206393755 38734066841588209809590633)
  ·
    refine ⟨29050550131191157357192975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38734066841588209809590633 29050550131191157357192975)
    ·
      refine ⟨43575825196786736035789463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29050550131191157357192975 43575825196786736035789463)
      ·
        refine ⟨65363737795180104053684195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43575825196786736035789463 65363737795180104053684195)
        ·
          refine ⟨98045606692770156080526293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65363737795180104053684195 98045606692770156080526293)
          ·
            refine ⟨2297943906861800533137335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 98045606692770156080526293 2297943906861800533137335)
            ·
              refine ⟨3446915860292700799706003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297943906861800533137335 3446915860292700799706003)
              ·
                refine ⟨5170373790439051199559005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3446915860292700799706003 5170373790439051199559005)
                ·
                  refine ⟨1938890171414644199834627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5170373790439051199559005 1938890171414644199834627)
                  ·
                    refine ⟨2908335257121966299751941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1938890171414644199834627 2908335257121966299751941)
                    ·
                      refine ⟨545312860710368681203489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2908335257121966299751941 545312860710368681203489)
                      ·
                        rfl

theorem cell23_1061993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_1061993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061993 prefixEnd_1061993 := by exact prefixLift 1061993
  have htrace : WordTrace (prefixWord ++ tailWord_1061993) baseStart_1061993 baseEnd_1061993 := by
    simpa [prefixWord, tailWord_1061993, baseEnd_1061993] using wordTrace_append hprefix tailTrace_1061993
  have hstable : (prefixWord ++ tailWord_1061993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061993).length < 2 ^ (prefixWord ++ tailWord_1061993).sum := by decide
  have hdescent : baseEnd_1061993 < baseStart_1061993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1061997 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_1061997 : Nat := 118140960795 + 1061997 * 2 ^ 59
def prefixEnd_1061997 : Nat := 4983230072969 + 3 ^ 40 * 1061997 * 2
def baseEnd_1061997 : Nat := 545314914632986665553471

theorem tailTrace_1061997 : CollatzResearch.WordTrace tailWord_1061997 prefixEnd_1061997 545314914632986665553471 := by
  unfold tailWord_1061997
  simp only [CollatzResearch.WordTrace]
  refine ⟨38734212733573718492736245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25822808489049145661824163 38734212733573718492736245)
  ·
    refine ⟨3631332443772536108694023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38734212733573718492736245 3631332443772536108694023)
    ·
      refine ⟨5446998665658804163041035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3631332443772536108694023 5446998665658804163041035)
      ·
        refine ⟨8170497998488206244561553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5446998665658804163041035 8170497998488206244561553)
        ·
          refine ⟨6127873498866154683421165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8170497998488206244561553 6127873498866154683421165)
          ·
            refine ⟨2297952562074808006282937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6127873498866154683421165 2297952562074808006282937)
            ·
              refine ⟨1723464421556106004712203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2297952562074808006282937 1723464421556106004712203)
              ·
                refine ⟨2585196632334159007068305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723464421556106004712203 2585196632334159007068305)
                ·
                  refine ⟨1938897474250619255301229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2585196632334159007068305 1938897474250619255301229)
                  ·
                    refine ⟨727086552843982220737961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1938897474250619255301229 727086552843982220737961)
                    ·
                      refine ⟨545314914632986665553471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727086552843982220737961 545314914632986665553471)
                      ·
                        rfl

theorem cell23_1061997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_1061997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1061997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1061997 prefixEnd_1061997 := by exact prefixLift 1061997
  have htrace : WordTrace (prefixWord ++ tailWord_1061997) baseStart_1061997 baseEnd_1061997 := by
    simpa [prefixWord, tailWord_1061997, baseEnd_1061997] using wordTrace_append hprefix tailTrace_1061997
  have hstable : (prefixWord ++ tailWord_1061997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1061997).length < 2 ^ (prefixWord ++ tailWord_1061997).sum := by decide
  have hdescent : baseEnd_1061997 < baseStart_1061997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1061997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062020 : List Nat := [2, 3, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_1062020 : Nat := 118140960795 + 1062020 * 2 ^ 59
def prefixEnd_1062020 : Nat := 4983230072969 + 3 ^ 40 * 1062020 * 2
def baseEnd_1062020 : Nat := 181775574896013358521955

theorem tailTrace_1062020 : CollatzResearch.WordTrace tailWord_1062020 prefixEnd_1062020 181775574896013358521955 := by
  unfold tailWord_1062020
  simp only [CollatzResearch.WordTrace]
  refine ⟨19367525806245196710411757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25823367741660262280549009 19367525806245196710411757)
  ·
    refine ⟨7262822177341948766404409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19367525806245196710411757 7262822177341948766404409)
    ·
      refine ⟨5447116633006461574803307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7262822177341948766404409 5447116633006461574803307)
      ·
        refine ⟨8170674949509692362204961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5447116633006461574803307 8170674949509692362204961)
        ·
          refine ⟨6128006212132269271653721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8170674949509692362204961 6128006212132269271653721)
          ·
            refine ⟨4596004659099201953740291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6128006212132269271653721 4596004659099201953740291)
            ·
              refine ⟨6894006988648802930610437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4596004659099201953740291 6894006988648802930610437)
              ·
                refine ⟨1292626310371650549489457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6894006988648802930610437 1292626310371650549489457)
                ·
                  refine ⟨969469732778737912117093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1292626310371650549489457 969469732778737912117093)
                  ·
                    refine ⟨181775574896013358521955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 969469732778737912117093 181775574896013358521955)
                    ·
                      rfl

theorem cell23_1062020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_1062020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062020 prefixEnd_1062020 := by exact prefixLift 1062020
  have htrace : WordTrace (prefixWord ++ tailWord_1062020) baseStart_1062020 baseEnd_1062020 := by
    simpa [prefixWord, tailWord_1062020, baseEnd_1062020] using wordTrace_append hprefix tailTrace_1062020
  have hstable : (prefixWord ++ tailWord_1062020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062020).length < 2 ^ (prefixWord ++ tailWord_1062020).sum := by decide
  have hdescent : baseEnd_1062020 < baseStart_1062020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062021 : List Nat := [1, 3, 1, 1, 6, 2, 2, 2, 1, 1, 3]
def baseStart_1062021 : Nat := 118140960795 + 1062021 * 2 ^ 59
def prefixEnd_1062021 : Nat := 4983230072969 + 3 ^ 40 * 1062021 * 2
def baseEnd_1062021 : Nat := 545327238168694571653361

theorem tailTrace_1062021 : CollatzResearch.WordTrace tailWord_1062021 prefixEnd_1062021 545327238168694571653361 := by
  unfold tailWord_1062021
  simp only [CollatzResearch.WordTrace]
  refine ⟨38735088085486770591609917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25823392056991180394406611 38735088085486770591609917)
  ·
    refine ⟨14525658032057538971853719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38735088085486770591609917 14525658032057538971853719)
    ·
      refine ⟨21788487048086308457780579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14525658032057538971853719 21788487048086308457780579)
      ·
        refine ⟨32682730572129462686670869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21788487048086308457780579 32682730572129462686670869)
        ·
          refine ⟨1532002995568568563437697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32682730572129462686670869 1532002995568568563437697)
          ·
            refine ⟨1149002246676426422578273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1532002995568568563437697 1149002246676426422578273)
            ·
              refine ⟨861751685007319816933705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149002246676426422578273 861751685007319816933705)
              ·
                refine ⟨646313763755489862700279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861751685007319816933705 646313763755489862700279)
                ·
                  refine ⟨969470645633234794050419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646313763755489862700279 969470645633234794050419)
                  ·
                    refine ⟨1454205968449852191075629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 969470645633234794050419 1454205968449852191075629)
                    ·
                      refine ⟨545327238168694571653361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1454205968449852191075629 545327238168694571653361)
                      ·
                        rfl

theorem cell23_1062021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 1, 1, 3].length) (baseStart_1062021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062021 prefixEnd_1062021 := by exact prefixLift 1062021
  have htrace : WordTrace (prefixWord ++ tailWord_1062021) baseStart_1062021 baseEnd_1062021 := by
    simpa [prefixWord, tailWord_1062021, baseEnd_1062021] using wordTrace_append hprefix tailTrace_1062021
  have hstable : (prefixWord ++ tailWord_1062021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062021).length < 2 ^ (prefixWord ++ tailWord_1062021).sum := by decide
  have hdescent : baseEnd_1062021 < baseStart_1062021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062030 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_1062030 : Nat := 118140960795 + 1062030 * 2 ^ 59
def prefixEnd_1062030 : Nat := 4983230072969 + 3 ^ 40 * 1062030 * 2
def baseEnd_1062030 : Nat := 545331859494585036440819

theorem tailTrace_1062030 : CollatzResearch.WordTrace tailWord_1062030 prefixEnd_1062030 545331859494585036440819 := by
  unfold tailWord_1062030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4841927042806770641085943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25823610894969443419125029 4841927042806770641085943)
  ·
    refine ⟨7262890564210155961628915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4841927042806770641085943 7262890564210155961628915)
    ·
      refine ⟨10894335846315233942443373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7262890564210155961628915 10894335846315233942443373)
      ·
        refine ⟨4085375942368212728416265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10894335846315233942443373 4085375942368212728416265)
        ·
          refine ⟨3064031956776159546312199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4085375942368212728416265 3064031956776159546312199)
          ·
            refine ⟨4596047935164239319468299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3064031956776159546312199 4596047935164239319468299)
            ·
              refine ⟨6894071902746358979202449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4596047935164239319468299 6894071902746358979202449)
              ·
                refine ⟨5170553927059769234401837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6894071902746358979202449 5170553927059769234401837)
                ·
                  refine ⟨1938957722647413462900689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5170553927059769234401837 1938957722647413462900689)
                  ·
                    refine ⟨1454218291985560097175517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1938957722647413462900689 1454218291985560097175517)
                    ·
                      refine ⟨545331859494585036440819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1454218291985560097175517 545331859494585036440819)
                      ·
                        rfl

theorem cell23_1062030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_1062030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062030 prefixEnd_1062030 := by exact prefixLift 1062030
  have htrace : WordTrace (prefixWord ++ tailWord_1062030) baseStart_1062030 baseEnd_1062030 := by
    simpa [prefixWord, tailWord_1062030, baseEnd_1062030] using wordTrace_append hprefix tailTrace_1062030
  have hstable : (prefixWord ++ tailWord_1062030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062030).length < 2 ^ (prefixWord ++ tailWord_1062030).sum := by decide
  have hdescent : baseEnd_1062030 < baseStart_1062030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062040 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1062040 : Nat := 118140960795 + 1062040 * 2 ^ 59
def prefixEnd_1062040 : Nat := 4983230072969 + 3 ^ 40 * 1062040 * 2
def baseEnd_1062040 : Nat := 545336994301129997315773

theorem tailTrace_1062040 : CollatzResearch.WordTrace tailWord_1062040 prefixEnd_1062040 545336994301129997315773 := by
  unfold tailWord_1062040
  simp only [CollatzResearch.WordTrace]
  refine ⟨19367890536208968418275787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25823854048278624557701049 19367890536208968418275787)
  ·
    refine ⟨29051835804313452627413681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19367890536208968418275787 29051835804313452627413681)
    ·
      refine ⟨21788876853235089470560261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29051835804313452627413681 21788876853235089470560261)
      ·
        refine ⟨4085414409981579275730049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21788876853235089470560261 4085414409981579275730049)
        ·
          refine ⟨3064060807486184456797537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4085414409981579275730049 3064060807486184456797537)
          ·
            refine ⟨2298045605614638342598153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3064060807486184456797537 2298045605614638342598153)
            ·
              refine ⟨1723534204210978756948615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2298045605614638342598153 1723534204210978756948615)
              ·
                refine ⟨2585301306316468135422923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723534204210978756948615 2585301306316468135422923)
                ·
                  refine ⟨3877951959474702203134385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2585301306316468135422923 3877951959474702203134385)
                  ·
                    refine ⟨2908463969606026652350789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3877951959474702203134385 2908463969606026652350789)
                    ·
                      refine ⟨545336994301129997315773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2908463969606026652350789 545336994301129997315773)
                      ·
                        rfl

theorem cell23_1062040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1062040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062040 prefixEnd_1062040 := by exact prefixLift 1062040
  have htrace : WordTrace (prefixWord ++ tailWord_1062040) baseStart_1062040 baseEnd_1062040 := by
    simpa [prefixWord, tailWord_1062040, baseEnd_1062040] using wordTrace_append hprefix tailTrace_1062040
  have hstable : (prefixWord ++ tailWord_1062040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062040).length < 2 ^ (prefixWord ++ tailWord_1062040).sum := by decide
  have hdescent : baseEnd_1062040 < baseStart_1062040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062061 : List Nat := [1, 5, 2, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_1062061 : Nat := 118140960795 + 1062061 * 2 ^ 59
def prefixEnd_1062061 : Nat := 4983230072969 + 3 ^ 40 * 1062061 * 2
def baseEnd_1062061 : Nat := 545347777394874415153177

theorem tailTrace_1062061 : CollatzResearch.WordTrace tailWord_1062061 prefixEnd_1062061 545347777394874415153177 := by
  unfold tailWord_1062061
  simp only [CollatzResearch.WordTrace]
  refine ⟨38736547005341857423066037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25824364670227904948710691 38736547005341857423066037)
  ·
    refine ⟨3631551281750799133412441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38736547005341857423066037 3631551281750799133412441)
    ·
      refine ⟨2723663461313099350059331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3631551281750799133412441 2723663461313099350059331)
      ·
        refine ⟨4085495191969649025088997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2723663461313099350059331 4085495191969649025088997)
        ·
          refine ⟨766030348494309192204187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4085495191969649025088997 766030348494309192204187)
          ·
            refine ⟨1149045522741463788306281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766030348494309192204187 1149045522741463788306281)
            ·
              refine ⟨861784142056097841229711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149045522741463788306281 861784142056097841229711)
              ·
                refine ⟨1292676213084146761844567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 861784142056097841229711 1292676213084146761844567)
                ·
                  refine ⟨1939014319626220142766851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292676213084146761844567 1939014319626220142766851)
                  ·
                    refine ⟨2908521479439330214150277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1939014319626220142766851 2908521479439330214150277)
                    ·
                      refine ⟨545347777394874415153177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2908521479439330214150277 545347777394874415153177)
                      ·
                        rfl

theorem cell23_1062061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_1062061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062061 prefixEnd_1062061 := by exact prefixLift 1062061
  have htrace : WordTrace (prefixWord ++ tailWord_1062061) baseStart_1062061 baseEnd_1062061 := by
    simpa [prefixWord, tailWord_1062061, baseEnd_1062061] using wordTrace_append hprefix tailTrace_1062061
  have hstable : (prefixWord ++ tailWord_1062061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062061).length < 2 ^ (prefixWord ++ tailWord_1062061).sum := by decide
  have hdescent : baseEnd_1062061 < baseStart_1062061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062077 : List Nat := [1, 4, 1, 2, 1, 1, 5, 2, 2, 1, 3]
def baseStart_1062077 : Nat := 118140960795 + 1062077 * 2 ^ 59
def prefixEnd_1062077 : Nat := 4983230072969 + 3 ^ 40 * 1062077 * 2
def baseEnd_1062077 : Nat := 545355993085346352553103

theorem tailTrace_1062077 : CollatzResearch.WordTrace tailWord_1062077 prefixEnd_1062077 545355993085346352553103 := by
  unfold tailWord_1062077
  simp only [CollatzResearch.WordTrace]
  refine ⟨38737130573283892155648485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25824753715522594770432323 38737130573283892155648485)
  ·
    refine ⟨7263211982490729779184091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38737130573283892155648485 7263211982490729779184091)
    ·
      refine ⟨10894817973736094668776137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7263211982490729779184091 10894817973736094668776137)
      ·
        refine ⟨8171113480302071001582103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10894817973736094668776137 8171113480302071001582103)
        ·
          refine ⟨12256670220453106502373155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8171113480302071001582103 12256670220453106502373155)
          ·
            refine ⟨18385005330679659753559733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12256670220453106502373155 18385005330679659753559733)
            ·
              refine ⟨1723594249751218101896225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18385005330679659753559733 1723594249751218101896225)
              ·
                refine ⟨1292695687313413576422169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1723594249751218101896225 1292695687313413576422169)
                ·
                  refine ⟨969521765485060182316627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1292695687313413576422169 969521765485060182316627)
                  ·
                    refine ⟨1454282648227590273474941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 969521765485060182316627 1454282648227590273474941)
                    ·
                      refine ⟨545355993085346352553103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1454282648227590273474941 545355993085346352553103)
                      ·
                        rfl

theorem cell23_1062077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_1062077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062077 prefixEnd_1062077 := by exact prefixLift 1062077
  have htrace : WordTrace (prefixWord ++ tailWord_1062077) baseStart_1062077 baseEnd_1062077 := by
    simpa [prefixWord, tailWord_1062077, baseEnd_1062077] using wordTrace_append hprefix tailTrace_1062077
  have hstable : (prefixWord ++ tailWord_1062077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062077).length < 2 ^ (prefixWord ++ tailWord_1062077).sum := by decide
  have hdescent : baseEnd_1062077 < baseStart_1062077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062094 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3]
def baseStart_1062094 : Nat := 118140960795 + 1062094 * 2 ^ 59
def prefixEnd_1062094 : Nat := 4983230072969 + 3 ^ 40 * 1062094 * 2
def baseEnd_1062094 : Nat := 545364722256472786040525

theorem tailTrace_1062094 : CollatzResearch.WordTrace tailWord_1062094 prefixEnd_1062094 545364722256472786040525 := by
  unfold tailWord_1062094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4842218826777788007377167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25825167076148202706011557 4842218826777788007377167)
  ·
    refine ⟨7263328240166682011065751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4842218826777788007377167 7263328240166682011065751)
    ·
      refine ⟨10894992360250023016598627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7263328240166682011065751 10894992360250023016598627)
      ·
        refine ⟨16342488540375034524897941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10894992360250023016598627 16342488540375034524897941)
        ·
          refine ⟨766054150330079743354591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16342488540375034524897941 766054150330079743354591)
          ·
            refine ⟨1149081225495119615031887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766054150330079743354591 1149081225495119615031887)
            ·
              refine ⟨1723621838242679422547831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149081225495119615031887 1723621838242679422547831)
              ·
                refine ⟨2585432757364019133821747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723621838242679422547831 2585432757364019133821747)
                ·
                  refine ⟨3878149136046028700732621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2585432757364019133821747 3878149136046028700732621)
                  ·
                    refine ⟨1454305926017260762774733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3878149136046028700732621 1454305926017260762774733)
                    ·
                      refine ⟨545364722256472786040525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1454305926017260762774733 545364722256472786040525)
                      ·
                        rfl

theorem cell23_1062094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_1062094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062094 prefixEnd_1062094 := by exact prefixLift 1062094
  have htrace : WordTrace (prefixWord ++ tailWord_1062094) baseStart_1062094 baseEnd_1062094 := by
    simpa [prefixWord, tailWord_1062094, baseEnd_1062094] using wordTrace_append hprefix tailTrace_1062094
  have hstable : (prefixWord ++ tailWord_1062094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062094).length < 2 ^ (prefixWord ++ tailWord_1062094).sum := by decide
  have hdescent : baseEnd_1062094 < baseStart_1062094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062096 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 10]
def baseStart_1062096 : Nat := 118140960795 + 1062096 * 2 ^ 59
def prefixEnd_1062096 : Nat := 4983230072969 + 3 ^ 40 * 1062096 * 2
def baseEnd_1062096 : Nat := 545365749217781778215515

theorem tailTrace_1062096 : CollatzResearch.WordTrace tailWord_1062096 prefixEnd_1062096 545365749217781778215515 := by
  unfold tailWord_1062096
  simp only [CollatzResearch.WordTrace]
  refine ⟨19368911780107529200295071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25825215706810038933726761 19368911780107529200295071)
  ·
    refine ⟨29053367670161293800442607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19368911780107529200295071 29053367670161293800442607)
    ·
      refine ⟨43580051505241940700663911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29053367670161293800442607 43580051505241940700663911)
      ·
        refine ⟨65370077257862911050995867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43580051505241940700663911 65370077257862911050995867)
        ·
          refine ⟨98055115886794366576493801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65370077257862911050995867 98055115886794366576493801)
          ·
            refine ⟨73541336915095774932370351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98055115886794366576493801 73541336915095774932370351)
            ·
              refine ⟨110312005372643662398555527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73541336915095774932370351 110312005372643662398555527)
              ·
                refine ⟨165468008058965493597833291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110312005372643662398555527 165468008058965493597833291)
                ·
                  refine ⟨248202012088448240396749937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165468008058965493597833291 248202012088448240396749937)
                  ·
                    refine ⟨186151509066336180297562453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 248202012088448240396749937 186151509066336180297562453)
                    ·
                      refine ⟨545365749217781778215515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 186151509066336180297562453 545365749217781778215515)
                      ·
                        rfl

theorem cell23_1062096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_1062096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062096 prefixEnd_1062096 := by exact prefixLift 1062096
  have htrace : WordTrace (prefixWord ++ tailWord_1062096) baseStart_1062096 baseEnd_1062096 := by
    simpa [prefixWord, tailWord_1062096, baseEnd_1062096] using wordTrace_append hprefix tailTrace_1062096
  have hstable : (prefixWord ++ tailWord_1062096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062096).length < 2 ^ (prefixWord ++ tailWord_1062096).sum := by decide
  have hdescent : baseEnd_1062096 < baseStart_1062096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062103 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 3]
def baseStart_1062103 : Nat := 118140960795 + 1062103 * 2 ^ 59
def prefixEnd_1062103 : Nat := 4983230072969 + 3 ^ 40 * 1062103 * 2
def baseEnd_1062103 : Nat := 545369343582363250827983

theorem tailTrace_1062103 : CollatzResearch.WordTrace tailWord_1062103 prefixEnd_1062103 545369343582363250827983 := by
  unfold tailWord_1062103
  simp only [CollatzResearch.WordTrace]
  refine ⟨38738078871189698596094963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25825385914126465730729975 38738078871189698596094963)
  ·
    refine ⟨58107118306784547894142445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38738078871189698596094963 58107118306784547894142445)
    ·
      refine ⟨21790169365044205460303417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58107118306784547894142445 21790169365044205460303417)
      ·
        refine ⟨16342627023783154095227563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21790169365044205460303417 16342627023783154095227563)
        ·
          refine ⟨24513940535674731142841345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16342627023783154095227563 24513940535674731142841345)
          ·
            refine ⟨18385455401756048357131009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24513940535674731142841345 18385455401756048357131009)
            ·
              refine ⟨13789091551317036267848257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18385455401756048357131009 13789091551317036267848257)
              ·
                refine ⟨10341818663487777200886193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13789091551317036267848257 10341818663487777200886193)
                ·
                  refine ⟨7756363997615832900664645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10341818663487777200886193 7756363997615832900664645)
                  ·
                    refine ⟨1454318249552968668874621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7756363997615832900664645 1454318249552968668874621)
                    ·
                      refine ⟨545369343582363250827983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1454318249552968668874621 545369343582363250827983)
                      ·
                        rfl

theorem cell23_1062103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_1062103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062103 prefixEnd_1062103 := by exact prefixLift 1062103
  have htrace : WordTrace (prefixWord ++ tailWord_1062103) baseStart_1062103 baseEnd_1062103 := by
    simpa [prefixWord, tailWord_1062103, baseEnd_1062103] using wordTrace_append hprefix tailTrace_1062103
  have hstable : (prefixWord ++ tailWord_1062103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062103).length < 2 ^ (prefixWord ++ tailWord_1062103).sum := by decide
  have hdescent : baseEnd_1062103 < baseStart_1062103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062104 : List Nat := [2, 1, 2, 2, 5, 1, 2, 2, 1, 3, 2]
def baseStart_1062104 : Nat := 118140960795 + 1062104 * 2 ^ 59
def prefixEnd_1062104 : Nat := 4983230072969 + 3 ^ 40 * 1062104 * 2
def baseEnd_1062104 : Nat := 545369857063017746915479

theorem tailTrace_1062104 : CollatzResearch.WordTrace tailWord_1062104 prefixEnd_1062104 545369857063017746915479 := by
  unfold tailWord_1062104
  simp only [CollatzResearch.WordTrace]
  refine ⟨19369057672093037883440683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25825410229457383844587577 19369057672093037883440683)
  ·
    refine ⟨29053586508139556825161025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19369057672093037883440683 29053586508139556825161025)
    ·
      refine ⟨21790189881104667618870769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29053586508139556825161025 21790189881104667618870769)
      ·
        refine ⟨16342642410828500714153077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21790189881104667618870769 16342642410828500714153077)
        ·
          refine ⟨1532122726015171941951851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16342642410828500714153077 1532122726015171941951851)
          ·
            refine ⟨2298184089022757912927777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1532122726015171941951851 2298184089022757912927777)
            ·
              refine ⟨1723638066767068434695833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2298184089022757912927777 1723638066767068434695833)
              ·
                refine ⟨1292728550075301326021875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1723638066767068434695833 1292728550075301326021875)
                ·
                  refine ⟨1939092825112951989032813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292728550075301326021875 1939092825112951989032813)
                  ·
                    refine ⟨727159809417356995887305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1939092825112951989032813 727159809417356995887305)
                    ·
                      refine ⟨545369857063017746915479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727159809417356995887305 545369857063017746915479)
                      ·
                        rfl

theorem cell23_1062104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_1062104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062104 prefixEnd_1062104 := by exact prefixLift 1062104
  have htrace : WordTrace (prefixWord ++ tailWord_1062104) baseStart_1062104 baseEnd_1062104 := by
    simpa [prefixWord, tailWord_1062104, baseEnd_1062104] using wordTrace_append hprefix tailTrace_1062104
  have hstable : (prefixWord ++ tailWord_1062104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062104).length < 2 ^ (prefixWord ++ tailWord_1062104).sum := by decide
  have hdescent : baseEnd_1062104 < baseStart_1062104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062134 : List Nat := [5, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_1062134 : Nat := 118140960795 + 1062134 * 2 ^ 59
def prefixEnd_1062134 : Nat := 4983230072969 + 3 ^ 40 * 1062134 * 2
def baseEnd_1062134 : Nat := 545385261482652629540341

theorem tailTrace_1062134 : CollatzResearch.WordTrace tailWord_1062134 prefixEnd_1062134 545385261482652629540341 := by
  unfold tailWord_1062134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421200595879836930654591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25826139689384927260315637 2421200595879836930654591)
  ·
    refine ⟨3631800893819755395981887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2421200595879836930654591 3631800893819755395981887)
    ·
      refine ⟨5447701340729633093972831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3631800893819755395981887 5447701340729633093972831)
      ·
        refine ⟨8171552011094449640959247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5447701340729633093972831 8171552011094449640959247)
        ·
          refine ⟨12257328016641674461438871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8171552011094449640959247 12257328016641674461438871)
          ·
            refine ⟨18385992024962511692158307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12257328016641674461438871 18385992024962511692158307)
            ·
              refine ⟨27578988037443767538237461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18385992024962511692158307 27578988037443767538237461)
              ·
                refine ⟨1292765064255176603354881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27578988037443767538237461 1292765064255176603354881)
                ·
                  refine ⟨969573798191382452516161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1292765064255176603354881 969573798191382452516161)
                  ·
                    refine ⟨727180348643536839387121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 969573798191382452516161 727180348643536839387121)
                    ·
                      refine ⟨545385261482652629540341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727180348643536839387121 545385261482652629540341)
                      ·
                        rfl

theorem cell23_1062134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_1062134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062134 prefixEnd_1062134 := by exact prefixLift 1062134
  have htrace : WordTrace (prefixWord ++ tailWord_1062134) baseStart_1062134 baseEnd_1062134 := by
    simpa [prefixWord, tailWord_1062134, baseEnd_1062134] using wordTrace_append hprefix tailTrace_1062134
  have hstable : (prefixWord ++ tailWord_1062134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062134).length < 2 ^ (prefixWord ++ tailWord_1062134).sum := by decide
  have hdescent : baseEnd_1062134 < baseStart_1062134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062153 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 4, 5]
def baseStart_1062153 : Nat := 118140960795 + 1062153 * 2 ^ 59
def prefixEnd_1062153 : Nat := 4983230072969 + 3 ^ 40 * 1062153 * 2
def baseEnd_1062153 : Nat := 181798339205029351734251

theorem tailTrace_1062153 : CollatzResearch.WordTrace tailWord_1062153 prefixEnd_1062153 181798339205029351734251 := by
  unfold tailWord_1062153
  simp only [CollatzResearch.WordTrace]
  refine ⟨38739902521008557135415113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25826601680672371423610075 38739902521008557135415113)
  ·
    refine ⟨29054926890756417851561335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38739902521008557135415113 29054926890756417851561335)
    ·
      refine ⟨43582390336134626777342003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29054926890756417851561335 43582390336134626777342003)
      ·
        refine ⟨65373585504201940166013005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43582390336134626777342003 65373585504201940166013005)
        ·
          refine ⟨24515094564075727562254877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65373585504201940166013005 24515094564075727562254877)
          ·
            refine ⟨9193160461528397835845579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24515094564075727562254877 9193160461528397835845579)
            ·
              refine ⟨13789740692292596753768369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9193160461528397835845579 13789740692292596753768369)
              ·
                refine ⟨10342305519219447565326277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13789740692292596753768369 10342305519219447565326277)
                ·
                  refine ⟨1939182284853646418498677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10342305519219447565326277 1939182284853646418498677)
                  ·
                    refine ⟨181798339205029351734251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1939182284853646418498677 181798339205029351734251)
                    ·
                      rfl

theorem cell23_1062153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 5].length) (baseStart_1062153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062153 prefixEnd_1062153 := by exact prefixLift 1062153
  have htrace : WordTrace (prefixWord ++ tailWord_1062153) baseStart_1062153 baseEnd_1062153 := by
    simpa [prefixWord, tailWord_1062153, baseEnd_1062153] using wordTrace_append hprefix tailTrace_1062153
  have hstable : (prefixWord ++ tailWord_1062153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062153).length < 2 ^ (prefixWord ++ tailWord_1062153).sum := by decide
  have hdescent : baseEnd_1062153 < baseStart_1062153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062170 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 2, 5]
def baseStart_1062170 : Nat := 118140960795 + 1062170 * 2 ^ 59
def prefixEnd_1062170 : Nat := 4983230072969 + 3 ^ 40 * 1062170 * 2
def baseEnd_1062170 : Nat := 181801248928738162896725

theorem tailTrace_1062170 : CollatzResearch.WordTrace tailWord_1062170 prefixEnd_1062170 181801248928738162896725 := by
  unfold tailWord_1062170
  simp only [CollatzResearch.WordTrace]
  refine ⟨9685130640486742259695991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25827015041297979359189309 9685130640486742259695991)
  ·
    refine ⟨14527695960730113389543987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9685130640486742259695991 14527695960730113389543987)
    ·
      refine ⟨21791543941095170084315981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14527695960730113389543987 21791543941095170084315981)
      ·
        refine ⟨8171828977910688781618493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21791543941095170084315981 8171828977910688781618493)
        ·
          refine ⟨3064435866716508293106935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8171828977910688781618493 3064435866716508293106935)
          ·
            refine ⟨4596653800074762439660403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3064435866716508293106935 4596653800074762439660403)
            ·
              refine ⟨6894980700112143659490605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4596653800074762439660403 6894980700112143659490605)
              ·
                refine ⟨2585617762542053872308977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6894980700112143659490605 2585617762542053872308977)
                ·
                  refine ⟨1939213321906540404231733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2585617762542053872308977 1939213321906540404231733)
                  ·
                    refine ⟨181801248928738162896725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1939213321906540404231733 181801248928738162896725)
                    ·
                      rfl

theorem cell23_1062170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_1062170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062170 prefixEnd_1062170 := by exact prefixLift 1062170
  have htrace : WordTrace (prefixWord ++ tailWord_1062170) baseStart_1062170 baseEnd_1062170 := by
    simpa [prefixWord, tailWord_1062170, baseEnd_1062170] using wordTrace_append hprefix tailTrace_1062170
  have hstable : (prefixWord ++ tailWord_1062170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062170).length < 2 ^ (prefixWord ++ tailWord_1062170).sum := by decide
  have hdescent : baseEnd_1062170 < baseStart_1062170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062200 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 3, 4]
def baseStart_1062200 : Nat := 118140960795 + 1062200 * 2 ^ 59
def prefixEnd_1062200 : Nat := 4983230072969 + 3 ^ 40 * 1062200 * 2
def baseEnd_1062200 : Nat := 181806383735283123771679

theorem tailTrace_1062200 : CollatzResearch.WordTrace tailWord_1062200 prefixEnd_1062200 181806383735283123771679 := by
  unfold tailWord_1062200
  simp only [CollatzResearch.WordTrace]
  refine ⟨19370808375919142081188027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25827744501225522774917369 19370808375919142081188027)
  ·
    refine ⟨29056212563878713121782041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19370808375919142081188027 29056212563878713121782041)
    ·
      refine ⟨21792159422909034841336531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29056212563878713121782041 21792159422909034841336531)
      ·
        refine ⟨32688239134363552262004797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21792159422909034841336531 32688239134363552262004797)
        ·
          refine ⟨12258089675386332098251799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32688239134363552262004797 12258089675386332098251799)
          ·
            refine ⟨18387134513079498147377699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12258089675386332098251799 18387134513079498147377699)
            ·
              refine ⟨27580701769619247221066549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18387134513079498147377699 27580701769619247221066549)
              ·
                refine ⟨2585690790901804426974989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27580701769619247221066549 2585690790901804426974989)
                ·
                  refine ⟨969634046588176660115621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2585690790901804426974989 969634046588176660115621)
                  ·
                    refine ⟨181806383735283123771679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 969634046588176660115621 181806383735283123771679)
                    ·
                      rfl

theorem cell23_1062200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_1062200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062200 prefixEnd_1062200 := by exact prefixLift 1062200
  have htrace : WordTrace (prefixWord ++ tailWord_1062200) baseStart_1062200 baseEnd_1062200 := by
    simpa [prefixWord, tailWord_1062200, baseEnd_1062200] using wordTrace_append hprefix tailTrace_1062200
  have hstable : (prefixWord ++ tailWord_1062200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062200).length < 2 ^ (prefixWord ++ tailWord_1062200).sum := by decide
  have hdescent : baseEnd_1062200 < baseStart_1062200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062207 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 2, 4, 2]
def baseStart_1062207 : Nat := 118140960795 + 1062207 * 2 ^ 59
def prefixEnd_1062207 : Nat := 4983230072969 + 3 ^ 40 * 1062207 * 2
def baseEnd_1062207 : Nat := 545422745570430843927505

theorem tailTrace_1062207 : CollatzResearch.WordTrace tailWord_1062207 prefixEnd_1062207 545422745570430843927505 := by
  unfold tailWord_1062207
  simp only [CollatzResearch.WordTrace]
  refine ⟨38741872062812924357880875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25827914708541949571920583 38741872062812924357880875)
  ·
    refine ⟨58112808094219386536821313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38741872062812924357880875 58112808094219386536821313)
    ·
      refine ⟨43584606070664539902615985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58112808094219386536821313 43584606070664539902615985)
      ·
        refine ⟨32688454552998404926961989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43584606070664539902615985 32688454552998404926961989)
        ·
          refine ⟨6129085228687200923805373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32688454552998404926961989 6129085228687200923805373)
          ·
            refine ⟨2298406960757700346427015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6129085228687200923805373 2298406960757700346427015)
            ·
              refine ⟨3447610441136550519640523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2298406960757700346427015 3447610441136550519640523)
              ·
                refine ⟨5171415661704825779460785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3447610441136550519640523 5171415661704825779460785)
                ·
                  refine ⟨3878561746278619334595589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5171415661704825779460785 3878561746278619334595589)
                  ·
                    refine ⟨727230327427241125236673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3878561746278619334595589 727230327427241125236673)
                    ·
                      refine ⟨545422745570430843927505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727230327427241125236673 545422745570430843927505)
                      ·
                        rfl

theorem cell23_1062207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 4, 2].length) (baseStart_1062207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062207 prefixEnd_1062207 := by exact prefixLift 1062207
  have htrace : WordTrace (prefixWord ++ tailWord_1062207) baseStart_1062207 baseEnd_1062207 := by
    simpa [prefixWord, tailWord_1062207, baseEnd_1062207] using wordTrace_append hprefix tailTrace_1062207
  have hstable : (prefixWord ++ tailWord_1062207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062207).length < 2 ^ (prefixWord ++ tailWord_1062207).sum := by decide
  have hdescent : baseEnd_1062207 < baseStart_1062207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062221 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1062221 : Nat := 118140960795 + 1062221 * 2 ^ 59
def prefixEnd_1062221 : Nat := 4983230072969 + 3 ^ 40 * 1062221 * 2
def baseEnd_1062221 : Nat := 181809978099864596384147

theorem tailTrace_1062221 : CollatzResearch.WordTrace tailWord_1062221 prefixEnd_1062221 181809978099864596384147 := by
  unfold tailWord_1062221
  simp only [CollatzResearch.WordTrace]
  refine ⟨38742382684762204748890517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25828255123174803165927011 38742382684762204748890517)
  ·
    refine ⟨1816049188348228347604243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38742382684762204748890517 1816049188348228347604243)
    ·
      refine ⟨2724073782522342521406365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1816049188348228347604243 2724073782522342521406365)
      ·
        refine ⟨1021527668445878445527387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2724073782522342521406365 1021527668445878445527387)
        ·
          refine ⟨1532291502668817668291081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021527668445878445527387 1532291502668817668291081)
          ·
            refine ⟨1149218627001613251218311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1532291502668817668291081 1149218627001613251218311)
            ·
              refine ⟨1723827940502419876827467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1149218627001613251218311 1723827940502419876827467)
              ·
                refine ⟨2585741910753629815241201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723827940502419876827467 2585741910753629815241201)
                ·
                  refine ⟨1939306433065222361430901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2585741910753629815241201 1939306433065222361430901)
                  ·
                    refine ⟨181809978099864596384147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1939306433065222361430901 181809978099864596384147)
                    ·
                      rfl

theorem cell23_1062221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1062221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062221 prefixEnd_1062221 := by exact prefixLift 1062221
  have htrace : WordTrace (prefixWord ++ tailWord_1062221) baseStart_1062221 baseEnd_1062221 := by
    simpa [prefixWord, tailWord_1062221, baseEnd_1062221] using wordTrace_append hprefix tailTrace_1062221
  have hstable : (prefixWord ++ tailWord_1062221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062221).length < 2 ^ (prefixWord ++ tailWord_1062221).sum := by decide
  have hdescent : baseEnd_1062221 < baseStart_1062221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062257 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 3, 1, 3]
def baseStart_1062257 : Nat := 118140960795 + 1062257 * 2 ^ 59
def prefixEnd_1062257 : Nat := 4983230072969 + 3 ^ 40 * 1062257 * 2
def baseEnd_1062257 : Nat := 545448419603155648302275

theorem tailTrace_1062257 : CollatzResearch.WordTrace tailWord_1062257 prefixEnd_1062257 545448419603155648302275 := by
  unfold tailWord_1062257
  simp only [CollatzResearch.WordTrace]
  refine ⟨38743695712631782897201025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25829130475087855264800683 38743695712631782897201025)
  ·
    refine ⟨29057771784473837172900769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38743695712631782897201025 29057771784473837172900769)
    ·
      refine ⟨21793328838355377879675577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29057771784473837172900769 21793328838355377879675577)
      ·
        refine ⟨16344996628766533409756683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21793328838355377879675577 16344996628766533409756683)
        ·
          refine ⟨24517494943149800114635025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16344996628766533409756683 24517494943149800114635025)
          ·
            refine ⟨18388121207362350085976269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24517494943149800114635025 18388121207362350085976269)
            ·
              refine ⟨6895545452760881282241101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18388121207362350085976269 6895545452760881282241101)
              ·
                refine ⟨2585829544785330480840413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6895545452760881282241101 2585829544785330480840413)
                ·
                  refine ⟨969686079294498930315155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2585829544785330480840413 969686079294498930315155)
                  ·
                    refine ⟨1454529118941748395472733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 969686079294498930315155 1454529118941748395472733)
                    ·
                      refine ⟨545448419603155648302275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1454529118941748395472733 545448419603155648302275)
                      ·
                        rfl

theorem cell23_1062257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_1062257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062257 prefixEnd_1062257 := by exact prefixLift 1062257
  have htrace : WordTrace (prefixWord ++ tailWord_1062257) baseStart_1062257 baseEnd_1062257 := by
    simpa [prefixWord, tailWord_1062257, baseEnd_1062257] using wordTrace_append hprefix tailTrace_1062257
  have hstable : (prefixWord ++ tailWord_1062257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062257).length < 2 ^ (prefixWord ++ tailWord_1062257).sum := by decide
  have hdescent : baseEnd_1062257 < baseStart_1062257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062297 : List Nat := [1, 2, 1, 2, 1, 5, 2, 3, 1, 1, 4]
def baseStart_1062297 : Nat := 118140960795 + 1062297 * 2 ^ 59
def prefixEnd_1062297 : Nat := 4983230072969 + 3 ^ 40 * 1062297 * 2
def baseEnd_1062297 : Nat := 545468958829335491802091

theorem tailTrace_1062297 : CollatzResearch.WordTrace tailWord_1062297 prefixEnd_1062297 545468958829335491802091 := by
  unfold tailWord_1062297
  simp only [CollatzResearch.WordTrace]
  refine ⟨38745154632486869728657145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25830103088324579819104763 38745154632486869728657145)
  ·
    refine ⟨29058865974365152296492859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38745154632486869728657145 29058865974365152296492859)
    ·
      refine ⟨43588298961547728444739289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29058865974365152296492859 43588298961547728444739289)
      ·
        refine ⟨32691224221160796333554467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43588298961547728444739289 32691224221160796333554467)
        ·
          refine ⟨49036836331741194500331701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32691224221160796333554467 49036836331741194500331701)
          ·
            refine ⟨4597203406100736984406097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49036836331741194500331701 4597203406100736984406097)
            ·
              refine ⟨3447902554575552738304573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4597203406100736984406097 3447902554575552738304573)
              ·
                refine ⟨1292963457965832276864215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3447902554575552738304573 1292963457965832276864215)
                ·
                  refine ⟨1939445186948748415296323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292963457965832276864215 1939445186948748415296323)
                  ·
                    refine ⟨2909167780423122622944485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1939445186948748415296323 2909167780423122622944485)
                    ·
                      refine ⟨545468958829335491802091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2909167780423122622944485 545468958829335491802091)
                      ·
                        rfl

theorem cell23_1062297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_1062297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062297 prefixEnd_1062297 := by exact prefixLift 1062297
  have htrace : WordTrace (prefixWord ++ tailWord_1062297) baseStart_1062297 baseEnd_1062297 := by
    simpa [prefixWord, tailWord_1062297, baseEnd_1062297] using wordTrace_append hprefix tailTrace_1062297
  have hstable : (prefixWord ++ tailWord_1062297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062297).length < 2 ^ (prefixWord ++ tailWord_1062297).sum := by decide
  have hdescent : baseEnd_1062297 < baseStart_1062297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062307 : List Nat := [1, 1, 1, 4, 1, 3, 2, 4, 2, 4]
def baseStart_1062307 : Nat := 118140960795 + 1062307 * 2 ^ 59
def prefixEnd_1062307 : Nat := 4983230072969 + 3 ^ 40 * 1062307 * 2
def baseEnd_1062307 : Nat := 181824697878626817559015

theorem tailTrace_1062307 : CollatzResearch.WordTrace tailWord_1062307 prefixEnd_1062307 181824697878626817559015 := by
  unfold tailWord_1062307
  simp only [CollatzResearch.WordTrace]
  refine ⟨38745519362450641436521175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25830346241633760957680783 38745519362450641436521175)
  ·
    refine ⟨58118279043675962154781763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38745519362450641436521175 58118279043675962154781763)
    ·
      refine ⟨87177418565513943232172645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58118279043675962154781763 87177418565513943232172645)
      ·
        refine ⟨16345765981033864356032371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87177418565513943232172645 16345765981033864356032371)
        ·
          refine ⟨24518648971550796534048557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16345765981033864356032371 24518648971550796534048557)
          ·
            refine ⟨9194493364331548700268209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24518648971550796534048557 9194493364331548700268209)
            ·
              refine ⟨6895870023248661525201157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9194493364331548700268209 6895870023248661525201157)
              ·
                refine ⟨1292975629359124035975217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6895870023248661525201157 1292975629359124035975217)
                ·
                  refine ⟨969731722019343026981413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1292975629359124035975217 969731722019343026981413)
                  ·
                    refine ⟨181824697878626817559015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 969731722019343026981413 181824697878626817559015)
                    ·
                      rfl

theorem cell23_1062307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2, 4].length) (baseStart_1062307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062307 prefixEnd_1062307 := by exact prefixLift 1062307
  have htrace : WordTrace (prefixWord ++ tailWord_1062307) baseStart_1062307 baseEnd_1062307 := by
    simpa [prefixWord, tailWord_1062307, baseEnd_1062307] using wordTrace_append hprefix tailTrace_1062307
  have hstable : (prefixWord ++ tailWord_1062307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062307).length < 2 ^ (prefixWord ++ tailWord_1062307).sum := by decide
  have hdescent : baseEnd_1062307 < baseStart_1062307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062347 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 6, 1, 3]
def baseStart_1062347 : Nat := 118140960795 + 1062347 * 2 ^ 59
def prefixEnd_1062347 : Nat := 4983230072969 + 3 ^ 40 * 1062347 * 2
def baseEnd_1062347 : Nat := 545494632862060296176861

theorem tailTrace_1062347 : CollatzResearch.WordTrace tailWord_1062347 prefixEnd_1062347 545494632862060296176861 := by
  unfold tailWord_1062347
  simp only [CollatzResearch.WordTrace]
  refine ⟨38746978282305728267977295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25831318854870485511984863 38746978282305728267977295)
  ·
    refine ⟨58120467423458592401965943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38746978282305728267977295 58120467423458592401965943)
    ·
      refine ⟨87180701135187888602948915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58120467423458592401965943 87180701135187888602948915)
      ·
        refine ⟨130771051702781832904423373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87180701135187888602948915 130771051702781832904423373)
        ·
          refine ⟨49039144388543187339158765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130771051702781832904423373 49039144388543187339158765)
          ·
            refine ⟨18389679145703695252184537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49039144388543187339158765 18389679145703695252184537)
            ·
              refine ⟨13792259359277771439138403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18389679145703695252184537 13792259359277771439138403)
              ·
                refine ⟨20688389038916657158707605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13792259359277771439138403 20688389038916657158707605)
                ·
                  refine ⟨969768236199218304314419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20688389038916657158707605 969768236199218304314419)
                  ·
                    refine ⟨1454652354298827456471629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 969768236199218304314419 1454652354298827456471629)
                    ·
                      refine ⟨545494632862060296176861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1454652354298827456471629 545494632862060296176861)
                      ·
                        rfl

theorem cell23_1062347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 1, 3].length) (baseStart_1062347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062347 prefixEnd_1062347 := by exact prefixLift 1062347
  have htrace : WordTrace (prefixWord ++ tailWord_1062347) baseStart_1062347 baseEnd_1062347 := by
    simpa [prefixWord, tailWord_1062347, baseEnd_1062347] using wordTrace_append hprefix tailTrace_1062347
  have hstable : (prefixWord ++ tailWord_1062347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062347).length < 2 ^ (prefixWord ++ tailWord_1062347).sum := by decide
  have hdescent : baseEnd_1062347 < baseStart_1062347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062360 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_1062360 : Nat := 118140960795 + 1062360 * 2 ^ 59
def prefixEnd_1062360 : Nat := 4983230072969 + 3 ^ 40 * 1062360 * 2
def baseEnd_1062360 : Nat := 545501308110568745314301

theorem tailTrace_1062360 : CollatzResearch.WordTrace tailWord_1062360 prefixEnd_1062360 545501308110568745314301 := by
  unfold tailWord_1062360
  simp only [CollatzResearch.WordTrace]
  refine ⟨19373726215629315744100267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25831634954172420992133689 19373726215629315744100267)
  ·
    refine ⟨29060589323443973616150401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19373726215629315744100267 29060589323443973616150401)
    ·
      refine ⟨21795441992582980212112801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29060589323443973616150401 21795441992582980212112801)
      ·
        refine ⟨16346581494437235159084601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21795441992582980212112801 16346581494437235159084601)
        ·
          refine ⟨12259936120827926369313451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16346581494437235159084601 12259936120827926369313451)
          ·
            refine ⟨18389904181241889553970177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12259936120827926369313451 18389904181241889553970177)
            ·
              refine ⟨13792428135931417165477633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18389904181241889553970177 13792428135931417165477633)
              ·
                refine ⟨10344321101948562874108225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13792428135931417165477633 10344321101948562874108225)
                ·
                  refine ⟨7758240826461422155581169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10344321101948562874108225 7758240826461422155581169)
                  ·
                    refine ⟨5818680619846066616685877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7758240826461422155581169 5818680619846066616685877)
                    ·
                      refine ⟨545501308110568745314301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5818680619846066616685877 545501308110568745314301)
                      ·
                        rfl

theorem cell23_1062360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_1062360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062360 prefixEnd_1062360 := by exact prefixLift 1062360
  have htrace : WordTrace (prefixWord ++ tailWord_1062360) baseStart_1062360 baseEnd_1062360 := by
    simpa [prefixWord, tailWord_1062360, baseEnd_1062360] using wordTrace_append hprefix tailTrace_1062360
  have hstable : (prefixWord ++ tailWord_1062360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062360).length < 2 ^ (prefixWord ++ tailWord_1062360).sum := by decide
  have hdescent : baseEnd_1062360 < baseStart_1062360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062365 : List Nat := [1, 4, 3, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_1062365 : Nat := 118140960795 + 1062365 * 2 ^ 59
def prefixEnd_1062365 : Nat := 4983230072969 + 3 ^ 40 * 1062365 * 2
def baseEnd_1062365 : Nat := 545503875513841225751779

theorem tailTrace_1062365 : CollatzResearch.WordTrace tailWord_1062365 prefixEnd_1062365 545503875513841225751779 := by
  unfold tailWord_1062365
  simp only [CollatzResearch.WordTrace]
  refine ⟨38747634796240517342132549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25831756530827011561421699 38747634796240517342132549)
  ·
    refine ⟨7265181524295097001649853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38747634796240517342132549 7265181524295097001649853)
    ·
      refine ⟨2724443071610661375618695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7265181524295097001649853 2724443071610661375618695)
      ·
        refine ⟨4086664607415992063428043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2724443071610661375618695 4086664607415992063428043)
        ·
          refine ⟨6129996911123988095142065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4086664607415992063428043 6129996911123988095142065)
          ·
            refine ⟨4597497683342991071356549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6129996911123988095142065 4597497683342991071356549)
            ·
              refine ⟨862030815626810825879353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4597497683342991071356549 862030815626810825879353)
              ·
                refine ⟨646523111720108119409515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 862030815626810825879353 646523111720108119409515)
                ·
                  refine ⟨969784667580162179114273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646523111720108119409515 969784667580162179114273)
                  ·
                    refine ⟨727338500685121634335705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 969784667580162179114273 727338500685121634335705)
                    ·
                      refine ⟨545503875513841225751779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727338500685121634335705 545503875513841225751779)
                      ·
                        rfl

theorem cell23_1062365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_1062365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062365 prefixEnd_1062365 := by exact prefixLift 1062365
  have htrace : WordTrace (prefixWord ++ tailWord_1062365) baseStart_1062365 baseEnd_1062365 := by
    simpa [prefixWord, tailWord_1062365, baseEnd_1062365] using wordTrace_append hprefix tailTrace_1062365
  have hstable : (prefixWord ++ tailWord_1062365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062365).length < 2 ^ (prefixWord ++ tailWord_1062365).sum := by decide
  have hdescent : baseEnd_1062365 < baseStart_1062365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062381 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1062381 : Nat := 118140960795 + 1062381 * 2 ^ 59
def prefixEnd_1062381 : Nat := 4983230072969 + 3 ^ 40 * 1062381 * 2
def baseEnd_1062381 : Nat := 545512091204313163151705

theorem tailTrace_1062381 : CollatzResearch.WordTrace tailWord_1062381 prefixEnd_1062381 545512091204313163151705 := by
  unfold tailWord_1062381
  simp only [CollatzResearch.WordTrace]
  refine ⟨38748218364182552074714997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25832145576121701383143331 38748218364182552074714997)
  ·
    refine ⟨3632645471642114257004531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38748218364182552074714997 3632645471642114257004531)
    ·
      refine ⟨5448968207463171385506797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3632645471642114257004531 5448968207463171385506797)
      ·
        refine ⟨2043363077798689269565049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5448968207463171385506797 2043363077798689269565049)
        ·
          refine ⟨1532522308349016952173787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2043363077798689269565049 1532522308349016952173787)
          ·
            refine ⟨2298783462523525428260681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1532522308349016952173787 2298783462523525428260681)
            ·
              refine ⟨1724087596892644071195511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2298783462523525428260681 1724087596892644071195511)
              ·
                refine ⟨2586131395338966106793267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1724087596892644071195511 2586131395338966106793267)
                ·
                  refine ⟨3879197093008449160189901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2586131395338966106793267 3879197093008449160189901)
                  ·
                    refine ⟨1454698909878168435071213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3879197093008449160189901 1454698909878168435071213)
                    ·
                      refine ⟨545512091204313163151705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1454698909878168435071213 545512091204313163151705)
                      ·
                        rfl

theorem cell23_1062381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1062381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062381 prefixEnd_1062381 := by exact prefixLift 1062381
  have htrace : WordTrace (prefixWord ++ tailWord_1062381) baseStart_1062381 baseEnd_1062381 := by
    simpa [prefixWord, tailWord_1062381, baseEnd_1062381] using wordTrace_append hprefix tailTrace_1062381
  have hstable : (prefixWord ++ tailWord_1062381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062381).length < 2 ^ (prefixWord ++ tailWord_1062381).sum := by decide
  have hdescent : baseEnd_1062381 < baseStart_1062381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062421 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 4, 2, 2]
def baseStart_1062421 : Nat := 118140960795 + 1062421 * 2 ^ 59
def prefixEnd_1062421 : Nat := 4983230072969 + 3 ^ 40 * 1062421 * 2
def baseEnd_1062421 : Nat := 545532630430493006651521

theorem tailTrace_1062421 : CollatzResearch.WordTrace tailWord_1062421 prefixEnd_1062421 545532630430493006651521 := by
  unfold tailWord_1062421
  simp only [CollatzResearch.WordTrace]
  refine ⟨38749677284037638906171117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25833118189358425937447411 38749677284037638906171117)
  ·
    refine ⟨14531128981514114589814169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38749677284037638906171117 14531128981514114589814169)
    ·
      refine ⟨10898346736135585942360627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14531128981514114589814169 10898346736135585942360627)
      ·
        refine ⟨16347520104203378913540941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10898346736135585942360627 16347520104203378913540941)
        ·
          refine ⟨6130320039076267092577853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16347520104203378913540941 6130320039076267092577853)
          ·
            refine ⟨2298870014653600159716695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6130320039076267092577853 2298870014653600159716695)
            ·
              refine ⟨3448305021980400239575043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2298870014653600159716695 3448305021980400239575043)
              ·
                refine ⟨5172457532970600359362565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3448305021980400239575043 5172457532970600359362565)
                ·
                  refine ⟨969835787431987567380481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5172457532970600359362565 969835787431987567380481)
                  ·
                    refine ⟨727376840573990675535361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 969835787431987567380481 727376840573990675535361)
                    ·
                      refine ⟨545532630430493006651521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727376840573990675535361 545532630430493006651521)
                      ·
                        rfl

theorem cell23_1062421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_1062421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062421 prefixEnd_1062421 := by exact prefixLift 1062421
  have htrace : WordTrace (prefixWord ++ tailWord_1062421) baseStart_1062421 baseEnd_1062421 := by
    simpa [prefixWord, tailWord_1062421, baseEnd_1062421] using wordTrace_append hprefix tailTrace_1062421
  have hstable : (prefixWord ++ tailWord_1062421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062421).length < 2 ^ (prefixWord ++ tailWord_1062421).sum := by decide
  have hdescent : baseEnd_1062421 < baseStart_1062421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062457 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 1, 7]
def baseStart_1062457 : Nat := 118140960795 + 1062457 * 2 ^ 59
def prefixEnd_1062457 : Nat := 4983230072969 + 3 ^ 40 * 1062457 * 2
def baseEnd_1062457 : Nat := 181850371911351621933785

theorem tailTrace_1062457 : CollatzResearch.WordTrace tailWord_1062457 prefixEnd_1062457 181850371911351621933785 := by
  unfold tailWord_1062457
  simp only [CollatzResearch.WordTrace]
  refine ⟨38750990311907217054481625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25833993541271478036321083 38750990311907217054481625)
  ·
    refine ⟨29063242733930412790861219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38750990311907217054481625 29063242733930412790861219)
    ·
      refine ⟨43594864100895619186291829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29063242733930412790861219 43594864100895619186291829)
      ·
        refine ⟨4087018509458964298714859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43594864100895619186291829 4087018509458964298714859)
        ·
          refine ⟨6130527764188446448072289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4087018509458964298714859 6130527764188446448072289)
          ·
            refine ⟨4597895823141334836054217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6130527764188446448072289 4597895823141334836054217)
            ·
              refine ⟨3448421867356001127040663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4597895823141334836054217 3448421867356001127040663)
              ·
                refine ⟨5172632801034001690560995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3448421867356001127040663 5172632801034001690560995)
                ·
                  refine ⟨7758949201551002535841493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5172632801034001690560995 7758949201551002535841493)
                  ·
                    refine ⟨181850371911351621933785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7758949201551002535841493 181850371911351621933785)
                    ·
                      rfl

theorem cell23_1062457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 7].length) (baseStart_1062457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062457 prefixEnd_1062457 := by exact prefixLift 1062457
  have htrace : WordTrace (prefixWord ++ tailWord_1062457) baseStart_1062457 baseEnd_1062457 := by
    simpa [prefixWord, tailWord_1062457, baseEnd_1062457] using wordTrace_append hprefix tailTrace_1062457
  have hstable : (prefixWord ++ tailWord_1062457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062457).length < 2 ^ (prefixWord ++ tailWord_1062457).sum := by decide
  have hdescent : baseEnd_1062457 < baseStart_1062457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062521 : List Nat := [1, 2, 1, 3, 3, 1, 2, 5, 1, 4]
def baseStart_1062521 : Nat := 118140960795 + 1062521 * 2 ^ 59
def prefixEnd_1062521 : Nat := 4983230072969 + 3 ^ 40 * 1062521 * 2
def baseEnd_1062521 : Nat := 181861326165314205133687

theorem tailTrace_1062521 : CollatzResearch.WordTrace tailWord_1062521 prefixEnd_1062521 181861326165314205133687 := by
  unfold tailWord_1062521
  simp only [CollatzResearch.WordTrace]
  refine ⟨38753324583675355984811417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25835549722450237323207611 38753324583675355984811417)
  ·
    refine ⟨29064993437756516988608563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38753324583675355984811417 29064993437756516988608563)
    ·
      refine ⟨43597490156634775482912845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29064993437756516988608563 43597490156634775482912845)
      ·
        refine ⟨16349058808738040806092317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43597490156634775482912845 16349058808738040806092317)
        ·
          refine ⟨6130897053276765302284619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16349058808738040806092317 6130897053276765302284619)
          ·
            refine ⟨9196345579915147953426929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6130897053276765302284619 9196345579915147953426929)
            ·
              refine ⟨6897259184936360965070197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9196345579915147953426929 6897259184936360965070197)
              ·
                refine ⟨646618048587783840475331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6897259184936360965070197 646618048587783840475331)
                ·
                  refine ⟨969927072881675760712997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646618048587783840475331 969927072881675760712997)
                  ·
                    refine ⟨181861326165314205133687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 969927072881675760712997 181861326165314205133687)
                    ·
                      rfl

theorem cell23_1062521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 1, 4].length) (baseStart_1062521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062521 prefixEnd_1062521 := by exact prefixLift 1062521
  have htrace : WordTrace (prefixWord ++ tailWord_1062521) baseStart_1062521 baseEnd_1062521 := by
    simpa [prefixWord, tailWord_1062521, baseEnd_1062521] using wordTrace_append hprefix tailTrace_1062521
  have hstable : (prefixWord ++ tailWord_1062521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062521).length < 2 ^ (prefixWord ++ tailWord_1062521).sum := by decide
  have hdescent : baseEnd_1062521 < baseStart_1062521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062527 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 3]
def baseStart_1062527 : Nat := 118140960795 + 1062527 * 2 ^ 59
def prefixEnd_1062527 : Nat := 4983230072969 + 3 ^ 40 * 1062527 * 2
def baseEnd_1062527 : Nat := 545587059379869591926033

theorem tailTrace_1062527 : CollatzResearch.WordTrace tailWord_1062527 prefixEnd_1062527 545587059379869591926033 := by
  unfold tailWord_1062527
  simp only [CollatzResearch.WordTrace]
  refine ⟨38753543421653619009529835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25835695614435746006353223 38753543421653619009529835)
  ·
    refine ⟨58130315132480428514294753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38753543421653619009529835 58130315132480428514294753)
    ·
      refine ⟨43597736349360321385721065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58130315132480428514294753 43597736349360321385721065)
      ·
        refine ⟨32698302262020241039290799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43597736349360321385721065 32698302262020241039290799)
        ·
          refine ⟨49047453393030361558936199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32698302262020241039290799 49047453393030361558936199)
          ·
            refine ⟨73571180089545542338404299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49047453393030361558936199 73571180089545542338404299)
            ·
              refine ⟨110356770134318313507606449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73571180089545542338404299 110356770134318313507606449)
              ·
                refine ⟨82767577600738735130704837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110356770134318313507606449 82767577600738735130704837)
                ·
                  refine ⟨15518920800138512837007157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82767577600738735130704837 15518920800138512837007157)
                  ·
                    refine ⟨1454898825012985578469421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15518920800138512837007157 1454898825012985578469421)
                    ·
                      refine ⟨545587059379869591926033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1454898825012985578469421 545587059379869591926033)
                      ·
                        rfl

theorem cell23_1062527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_1062527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062527 prefixEnd_1062527 := by exact prefixLift 1062527
  have htrace : WordTrace (prefixWord ++ tailWord_1062527) baseStart_1062527 baseEnd_1062527 := by
    simpa [prefixWord, tailWord_1062527, baseEnd_1062527] using wordTrace_append hprefix tailTrace_1062527
  have hstable : (prefixWord ++ tailWord_1062527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062527).length < 2 ^ (prefixWord ++ tailWord_1062527).sum := by decide
  have hdescent : baseEnd_1062527 < baseStart_1062527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062538 : List Nat := [3, 1, 2, 3, 2, 2, 1, 4, 1, 4]
def baseStart_1062538 : Nat := 118140960795 + 1062538 * 2 ^ 59
def prefixEnd_1062538 : Nat := 4983230072969 + 3 ^ 40 * 1062538 * 2
def baseEnd_1062538 : Nat := 181864235889023016296161

theorem tailTrace_1062538 : CollatzResearch.WordTrace tailWord_1062538 prefixEnd_1062538 181864235889023016296161 := by
  unfold tailWord_1062538
  simp only [CollatzResearch.WordTrace]
  refine ⟨9688486156153441972045067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25835963083075845258786845 9688486156153441972045067)
  ·
    refine ⟨14532729234230162958067601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9688486156153441972045067 14532729234230162958067601)
    ·
      refine ⟨10899546925672622218550701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14532729234230162958067601 10899546925672622218550701)
      ·
        refine ⟨4087330097127233331956513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10899546925672622218550701 4087330097127233331956513)
        ·
          refine ⟨3065497572845424998967385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4087330097127233331956513 3065497572845424998967385)
          ·
            refine ⟨2299123179634068749225539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3065497572845424998967385 2299123179634068749225539)
            ·
              refine ⟨3448684769451103123838309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2299123179634068749225539 3448684769451103123838309)
              ·
                refine ⟨646628394272081835719683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3448684769451103123838309 646628394272081835719683)
                ·
                  refine ⟨969942591408122753579525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646628394272081835719683 969942591408122753579525)
                  ·
                    refine ⟨181864235889023016296161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 969942591408122753579525 181864235889023016296161)
                    ·
                      rfl

theorem cell23_1062538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_1062538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062538 prefixEnd_1062538 := by exact prefixLift 1062538
  have htrace : WordTrace (prefixWord ++ tailWord_1062538) baseStart_1062538 baseEnd_1062538 := by
    simpa [prefixWord, tailWord_1062538, baseEnd_1062538] using wordTrace_append hprefix tailTrace_1062538
  have hstable : (prefixWord ++ tailWord_1062538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062538).length < 2 ^ (prefixWord ++ tailWord_1062538).sum := by decide
  have hdescent : baseEnd_1062538 < baseStart_1062538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062544 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 7, 1, 3]
def baseStart_1062544 : Nat := 118140960795 + 1062544 * 2 ^ 59
def prefixEnd_1062544 : Nat := 4983230072969 + 3 ^ 40 * 1062544 * 2
def baseEnd_1062544 : Nat := 545595788550996025413455

theorem tailTrace_1062544 : CollatzResearch.WordTrace tailWord_1062544 prefixEnd_1062544 545595788550996025413455 := by
  unfold tailWord_1062544
  simp only [CollatzResearch.WordTrace]
  refine ⟨19377081731296015456449343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25836108975061353941932457 19377081731296015456449343)
  ·
    refine ⟨29065622596944023184674015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19377081731296015456449343 29065622596944023184674015)
    ·
      refine ⟨43598433895416034777011023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29065622596944023184674015 43598433895416034777011023)
      ·
        refine ⟨65397650843124052165516535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43598433895416034777011023 65397650843124052165516535)
        ·
          refine ⟨98096476264686078248274803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65397650843124052165516535 98096476264686078248274803)
          ·
            refine ⟨147144714397029117372412205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98096476264686078248274803 147144714397029117372412205)
            ·
              refine ⟨55179267898885919014654577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147144714397029117372412205 55179267898885919014654577)
              ·
                refine ⟨41384450924164439260990933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55179267898885919014654577 41384450924164439260990933)
                ·
                  refine ⟨969948068535104045179475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 41384450924164439260990933 969948068535104045179475)
                  ·
                    refine ⟨1454922102802656067769213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 969948068535104045179475 1454922102802656067769213)
                    ·
                      refine ⟨545595788550996025413455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1454922102802656067769213 545595788550996025413455)
                      ·
                        rfl

theorem cell23_1062544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 7, 1, 3].length) (baseStart_1062544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062544 prefixEnd_1062544 := by exact prefixLift 1062544
  have htrace : WordTrace (prefixWord ++ tailWord_1062544) baseStart_1062544 baseEnd_1062544 := by
    simpa [prefixWord, tailWord_1062544, baseEnd_1062544] using wordTrace_append hprefix tailTrace_1062544
  have hstable : (prefixWord ++ tailWord_1062544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062544).length < 2 ^ (prefixWord ++ tailWord_1062544).sum := by decide
  have hdescent : baseEnd_1062544 < baseStart_1062544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062557 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1062557 : Nat := 118140960795 + 1062557 * 2 ^ 59
def prefixEnd_1062557 : Nat := 4983230072969 + 3 ^ 40 * 1062557 * 2
def baseEnd_1062557 : Nat := 545602463799504474550895

theorem tailTrace_1062557 : CollatzResearch.WordTrace tailWord_1062557 prefixEnd_1062557 545602463799504474550895 := by
  unfold tailWord_1062557
  simp only [CollatzResearch.WordTrace]
  refine ⟨38754637611544934133121925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25836425074363289422081283 38754637611544934133121925)
  ·
    refine ⟨7266494552164675149960361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38754637611544934133121925 7266494552164675149960361)
    ·
      refine ⟨5449870914123506362470271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7266494552164675149960361 5449870914123506362470271)
      ·
        refine ⟨8174806371185259543705407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5449870914123506362470271 8174806371185259543705407)
        ·
          refine ⟨12262209556777889315558111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8174806371185259543705407 12262209556777889315558111)
          ·
            refine ⟨18393314335166833973337167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12262209556777889315558111 18393314335166833973337167)
            ·
              refine ⟨27589971502750250960005751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18393314335166833973337167 27589971502750250960005751)
              ·
                refine ⟨41384957254125376440008627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27589971502750250960005751 41384957254125376440008627)
                ·
                  refine ⟨62077435881188064660012941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41384957254125376440008627 62077435881188064660012941)
                  ·
                    refine ⟨23279038455445524247504853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62077435881188064660012941 23279038455445524247504853)
                    ·
                      refine ⟨545602463799504474550895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23279038455445524247504853 545602463799504474550895)
                      ·
                        rfl

theorem cell23_1062557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1062557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062557 prefixEnd_1062557 := by exact prefixLift 1062557
  have htrace : WordTrace (prefixWord ++ tailWord_1062557) baseStart_1062557 baseEnd_1062557 := by
    simpa [prefixWord, tailWord_1062557, baseEnd_1062557] using wordTrace_append hprefix tailTrace_1062557
  have hstable : (prefixWord ++ tailWord_1062557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062557).length < 2 ^ (prefixWord ++ tailWord_1062557).sum := by decide
  have hdescent : baseEnd_1062557 < baseStart_1062557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062561 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 5, 1, 3]
def baseStart_1062561 : Nat := 118140960795 + 1062561 * 2 ^ 59
def prefixEnd_1062561 : Nat := 4983230072969 + 3 ^ 40 * 1062561 * 2
def baseEnd_1062561 : Nat := 545604517722122458900877

theorem tailTrace_1062561 : CollatzResearch.WordTrace tailWord_1062561 prefixEnd_1062561 545604517722122458900877 := by
  unfold tailWord_1062561
  simp only [CollatzResearch.WordTrace]
  refine ⟨38754783503530442816267537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25836522335686961877511691 38754783503530442816267537)
  ·
    refine ⟨29066087627647832112200653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38754783503530442816267537 29066087627647832112200653)
    ·
      refine ⟨10899782860367937042075245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29066087627647832112200653 10899782860367937042075245)
      ·
        refine ⟨4087418572637976390778217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10899782860367937042075245 4087418572637976390778217)
        ·
          refine ⟨3065563929478482293083663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4087418572637976390778217 3065563929478482293083663)
          ·
            refine ⟨4598345894217723439625495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3065563929478482293083663 4598345894217723439625495)
            ·
              refine ⟨6897518841326585159438243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4598345894217723439625495 6897518841326585159438243)
              ·
                refine ⟨10346278261989877739157365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6897518841326585159438243 10346278261989877739157365)
                ·
                  refine ⟨969963587061551038046003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10346278261989877739157365 969963587061551038046003)
                  ·
                    refine ⟨1454945380592326557069005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 969963587061551038046003 1454945380592326557069005)
                    ·
                      refine ⟨545604517722122458900877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1454945380592326557069005 545604517722122458900877)
                      ·
                        rfl

theorem cell23_1062561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_1062561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062561 prefixEnd_1062561 := by exact prefixLift 1062561
  have htrace : WordTrace (prefixWord ++ tailWord_1062561) baseStart_1062561 baseEnd_1062561 := by
    simpa [prefixWord, tailWord_1062561, baseEnd_1062561] using wordTrace_append hprefix tailTrace_1062561
  have hstable : (prefixWord ++ tailWord_1062561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062561).length < 2 ^ (prefixWord ++ tailWord_1062561).sum := by decide
  have hdescent : baseEnd_1062561 < baseStart_1062561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062564 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_1062564 : Nat := 118140960795 + 1062564 * 2 ^ 59
def prefixEnd_1062564 : Nat := 4983230072969 + 3 ^ 40 * 1062564 * 2
def baseEnd_1062564 : Nat := 181868686054695315721121

theorem tailTrace_1062564 : CollatzResearch.WordTrace tailWord_1062564 prefixEnd_1062564 181868686054695315721121 := by
  unfold tailWord_1062564
  simp only [CollatzResearch.WordTrace]
  refine ⟨19377446461259787164313373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25836595281679716219084497 19377446461259787164313373)
  ·
    refine ⟨7266542422972420186617515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19377446461259787164313373 7266542422972420186617515)
    ·
      refine ⟨10899813634458630279926273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7266542422972420186617515 10899813634458630279926273)
      ·
        refine ⟨8174860225843972709944705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10899813634458630279926273 8174860225843972709944705)
        ·
          refine ⟨6131145169382979532458529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8174860225843972709944705 6131145169382979532458529)
          ·
            refine ⟨4598358877037234649343897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6131145169382979532458529 4598358877037234649343897)
            ·
              refine ⟨3448769157777925987007923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4598358877037234649343897 3448769157777925987007923)
              ·
                refine ⟨5173153736666888980511885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3448769157777925987007923 5173153736666888980511885)
                ·
                  refine ⟨1939932651250083367691957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5173153736666888980511885 1939932651250083367691957)
                  ·
                    refine ⟨181868686054695315721121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1939932651250083367691957 181868686054695315721121)
                    ·
                      rfl

theorem cell23_1062564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_1062564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062564 prefixEnd_1062564 := by exact prefixLift 1062564
  have htrace : WordTrace (prefixWord ++ tailWord_1062564) baseStart_1062564 baseEnd_1062564 := by
    simpa [prefixWord, tailWord_1062564, baseEnd_1062564] using wordTrace_append hprefix tailTrace_1062564
  have hstable : (prefixWord ++ tailWord_1062564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062564).length < 2 ^ (prefixWord ++ tailWord_1062564).sum := by decide
  have hdescent : baseEnd_1062564 < baseStart_1062564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062578 : List Nat := [3, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3]
def baseStart_1062578 : Nat := 118140960795 + 1062578 * 2 ^ 59
def prefixEnd_1062578 : Nat := 4983230072969 + 3 ^ 40 * 1062578 * 2
def baseEnd_1062578 : Nat := 545613246893248892388299

theorem tailTrace_1062578 : CollatzResearch.WordTrace tailWord_1062578 prefixEnd_1062578 545613246893248892388299 := by
  unfold tailWord_1062578
  simp only [CollatzResearch.WordTrace]
  refine ⟨9688850886117213679909097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25836935696312569813090925 9688850886117213679909097)
  ·
    refine ⟨7266638164587910259931823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9688850886117213679909097 7266638164587910259931823)
    ·
      refine ⟨10899957246881865389897735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7266638164587910259931823 10899957246881865389897735)
      ·
        refine ⟨16349935870322798084846603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10899957246881865389897735 16349935870322798084846603)
        ·
          refine ⟨24524903805484197127269905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16349935870322798084846603 24524903805484197127269905)
          ·
            refine ⟨18393677854113147845452429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24524903805484197127269905 18393677854113147845452429)
            ·
              refine ⟨6897629195292430442044661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18393677854113147845452429 6897629195292430442044661)
              ·
                refine ⟨646652737058665353941687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6897629195292430442044661 646652737058665353941687)
                ·
                  refine ⟨969979105587998030912531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646652737058665353941687 969979105587998030912531)
                  ·
                    refine ⟨1454968658381997046368797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 969979105587998030912531 1454968658381997046368797)
                    ·
                      refine ⟨545613246893248892388299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1454968658381997046368797 545613246893248892388299)
                      ·
                        rfl

theorem cell23_1062578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_1062578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062578 prefixEnd_1062578 := by exact prefixLift 1062578
  have htrace : WordTrace (prefixWord ++ tailWord_1062578) baseStart_1062578 baseEnd_1062578 := by
    simpa [prefixWord, tailWord_1062578, baseEnd_1062578] using wordTrace_append hprefix tailTrace_1062578
  have hstable : (prefixWord ++ tailWord_1062578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062578).length < 2 ^ (prefixWord ++ tailWord_1062578).sum := by decide
  have hdescent : baseEnd_1062578 < baseStart_1062578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062584 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 1, 8, 2]
def baseStart_1062584 : Nat := 118140960795 + 1062584 * 2 ^ 59
def prefixEnd_1062584 : Nat := 4983230072969 + 3 ^ 40 * 1062584 * 2
def baseEnd_1062584 : Nat := 545616327777175868913271

theorem tailTrace_1062584 : CollatzResearch.WordTrace tailWord_1062584 prefixEnd_1062584 545616327777175868913271 := by
  unfold tailWord_1062584
  simp only [CollatzResearch.WordTrace]
  refine ⟨19377811191223558872177403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25837081588298078496236537 19377811191223558872177403)
  ·
    refine ⟨29066716786835338308266105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19377811191223558872177403 29066716786835338308266105)
    ·
      refine ⟨21800037590126503731199579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29066716786835338308266105 21800037590126503731199579)
      ·
        refine ⟨32700056385189755596799369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21800037590126503731199579 32700056385189755596799369)
        ·
          refine ⟨24525042288892316697599527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32700056385189755596799369 24525042288892316697599527)
          ·
            refine ⟨36787563433338475046399291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24525042288892316697599527 36787563433338475046399291)
            ·
              refine ⟨55181345150007712569598937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36787563433338475046399291 55181345150007712569598937)
              ·
                refine ⟨41386008862505784427199203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55181345150007712569598937 41386008862505784427199203)
                ·
                  refine ⟨62079013293758676640798805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41386008862505784427199203 62079013293758676640798805)
                  ·
                    refine ⟨727488437036234491884361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62079013293758676640798805 727488437036234491884361)
                    ·
                      refine ⟨545616327777175868913271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727488437036234491884361 545616327777175868913271)
                      ·
                        rfl

theorem cell23_1062584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 8, 2].length) (baseStart_1062584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062584 prefixEnd_1062584 := by exact prefixLift 1062584
  have htrace : WordTrace (prefixWord ++ tailWord_1062584) baseStart_1062584 baseEnd_1062584 := by
    simpa [prefixWord, tailWord_1062584, baseEnd_1062584] using wordTrace_append hprefix tailTrace_1062584
  have hstable : (prefixWord ++ tailWord_1062584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062584).length < 2 ^ (prefixWord ++ tailWord_1062584).sum := by decide
  have hdescent : baseEnd_1062584 < baseStart_1062584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062587 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 5]
def baseStart_1062587 : Nat := 118140960795 + 1062587 * 2 ^ 59
def prefixEnd_1062587 : Nat := 4983230072969 + 3 ^ 40 * 1062587 * 2
def baseEnd_1062587 : Nat := 545617868219139357175757

theorem tailTrace_1062587 : CollatzResearch.WordTrace tailWord_1062587 prefixEnd_1062587 545617868219139357175757 := by
  unfold tailWord_1062587
  simp only [CollatzResearch.WordTrace]
  refine ⟨38755731801436249256714015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25837154534290832837809343 38755731801436249256714015)
  ·
    refine ⟨58133597702154373885071023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38755731801436249256714015 58133597702154373885071023)
    ·
      refine ⟨87200396553231560827606535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58133597702154373885071023 87200396553231560827606535)
      ·
        refine ⟨130800594829847341241409803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87200396553231560827606535 130800594829847341241409803)
        ·
          refine ⟨196200892244771011862114705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130800594829847341241409803 196200892244771011862114705)
          ·
            refine ⟨147150669183578258896586029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196200892244771011862114705 147150669183578258896586029)
            ·
              refine ⟨55181500943841847086219761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147150669183578258896586029 55181500943841847086219761)
              ·
                refine ⟨41386125707881385314664821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55181500943841847086219761 41386125707881385314664821)
                ·
                  refine ⟨3879949285113879873249827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41386125707881385314664821 3879949285113879873249827)
                  ·
                    refine ⟨5819923927670819809874741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3879949285113879873249827 5819923927670819809874741)
                    ·
                      refine ⟨545617868219139357175757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5819923927670819809874741 545617868219139357175757)
                      ·
                        rfl

theorem cell23_1062587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 5].length) (baseStart_1062587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062587 prefixEnd_1062587 := by exact prefixLift 1062587
  have htrace : WordTrace (prefixWord ++ tailWord_1062587) baseStart_1062587 baseEnd_1062587 := by
    simpa [prefixWord, tailWord_1062587, baseEnd_1062587] using wordTrace_append hprefix tailTrace_1062587
  have hstable : (prefixWord ++ tailWord_1062587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062587).length < 2 ^ (prefixWord ++ tailWord_1062587).sum := by decide
  have hdescent : baseEnd_1062587 < baseStart_1062587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062597 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_1062597 : Nat := 118140960795 + 1062597 * 2 ^ 59
def prefixEnd_1062597 : Nat := 4983230072969 + 3 ^ 40 * 1062597 * 2
def baseEnd_1062597 : Nat := 545623003025684318050711

theorem tailTrace_1062597 : CollatzResearch.WordTrace tailWord_1062597 prefixEnd_1062597 545623003025684318050711 := by
  unfold tailWord_1062597
  simp only [CollatzResearch.WordTrace]
  refine ⟨38756096531400020964578045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25837397687600013976385363 38756096531400020964578045)
  ·
    refine ⟨14533536199275007861716767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38756096531400020964578045 14533536199275007861716767)
    ·
      refine ⟨21800304298912511792575151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14533536199275007861716767 21800304298912511792575151)
      ·
        refine ⟨32700456448368767688862727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21800304298912511792575151 32700456448368767688862727)
        ·
          refine ⟨49050684672553151533294091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32700456448368767688862727 49050684672553151533294091)
          ·
            refine ⟨73576027008829727299941137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49050684672553151533294091 73576027008829727299941137)
            ·
              refine ⟨55182020256622295474955853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73576027008829727299941137 55182020256622295474955853)
              ·
                refine ⟨20693257596233360803108445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55182020256622295474955853 20693257596233360803108445)
                ·
                  refine ⟨7759971598587510301165667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20693257596233360803108445 7759971598587510301165667)
                  ·
                    refine ⟨11639957397881265451748501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7759971598587510301165667 11639957397881265451748501)
                    ·
                      refine ⟨545623003025684318050711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11639957397881265451748501 545623003025684318050711)
                      ·
                        rfl

theorem cell23_1062597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_1062597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062597 prefixEnd_1062597 := by exact prefixLift 1062597
  have htrace : WordTrace (prefixWord ++ tailWord_1062597) baseStart_1062597 baseEnd_1062597 := by
    simpa [prefixWord, tailWord_1062597, baseEnd_1062597] using wordTrace_append hprefix tailTrace_1062597
  have hstable : (prefixWord ++ tailWord_1062597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062597).length < 2 ^ (prefixWord ++ tailWord_1062597).sum := by decide
  have hdescent : baseEnd_1062597 < baseStart_1062597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062618 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2]
def baseStart_1062618 : Nat := 118140960795 + 1062618 * 2 ^ 59
def prefixEnd_1062618 : Nat := 4983230072969 + 3 ^ 40 * 1062618 * 2
def baseEnd_1062618 : Nat := 545633786119428735888115

theorem tailTrace_1062618 : CollatzResearch.WordTrace tailWord_1062618 prefixEnd_1062618 545633786119428735888115 := by
  unfold tailWord_1062618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9689215616080985387773127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25837908309549294367395005 9689215616080985387773127)
  ·
    refine ⟨14533823424121478081659691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9689215616080985387773127 14533823424121478081659691)
    ·
      refine ⟨21800735136182217122489537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14533823424121478081659691 21800735136182217122489537)
      ·
        refine ⟨16350551352136662841867153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21800735136182217122489537 16350551352136662841867153)
        ·
          refine ⟨12262913514102497131400365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16350551352136662841867153 12262913514102497131400365)
          ·
            refine ⟨4598592567788436424275137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12262913514102497131400365 4598592567788436424275137)
            ·
              refine ⟨3448944425841327318206353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4598592567788436424275137 3448944425841327318206353)
              ·
                refine ⟨2586708319380995488654765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3448944425841327318206353 2586708319380995488654765)
                ·
                  refine ⟨970015619767873308245537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2586708319380995488654765 970015619767873308245537)
                  ·
                    refine ⟨727511714825904981184153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 970015619767873308245537 727511714825904981184153)
                    ·
                      refine ⟨545633786119428735888115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727511714825904981184153 545633786119428735888115)
                      ·
                        rfl

theorem cell23_1062618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_1062618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062618 prefixEnd_1062618 := by exact prefixLift 1062618
  have htrace : WordTrace (prefixWord ++ tailWord_1062618) baseStart_1062618 baseEnd_1062618 := by
    simpa [prefixWord, tailWord_1062618, baseEnd_1062618] using wordTrace_append hprefix tailTrace_1062618
  have hstable : (prefixWord ++ tailWord_1062618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062618).length < 2 ^ (prefixWord ++ tailWord_1062618).sum := by decide
  have hdescent : baseEnd_1062618 < baseStart_1062618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062624 : List Nat := [2, 1, 1, 3, 1, 2, 6, 7]
def baseStart_1062624 : Nat := 118140960795 + 1062624 * 2 ^ 59
def prefixEnd_1062624 : Nat := 4983230072969 + 3 ^ 40 * 1062624 * 2
def baseEnd_1062624 : Nat := 20208772851976137496781

theorem tailTrace_1062624 : CollatzResearch.WordTrace tailWord_1062624 prefixEnd_1062624 20208772851976137496781 := by
  unfold tailWord_1062624
  simp only [CollatzResearch.WordTrace]
  refine ⟨19378540651151102287905463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25838054201534803050540617 19378540651151102287905463)
  ·
    refine ⟨29067810976726653431858195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19378540651151102287905463 29067810976726653431858195)
    ·
      refine ⟨43601716465089980147787293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29067810976726653431858195 43601716465089980147787293)
      ·
        refine ⟨16350643674408742555420235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43601716465089980147787293 16350643674408742555420235)
        ·
          refine ⟨24525965511613113833130353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16350643674408742555420235 24525965511613113833130353)
          ·
            refine ⟨18394474133709835374847765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24525965511613113833130353 18394474133709835374847765)
            ·
              refine ⟨862240975017648533195989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18394474133709835374847765 862240975017648533195989)
              ·
                refine ⟨20208772851976137496781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 862240975017648533195989 20208772851976137496781)
                ·
                  rfl

theorem cell23_1062624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 7].length) (baseStart_1062624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062624 prefixEnd_1062624 := by exact prefixLift 1062624
  have htrace : WordTrace (prefixWord ++ tailWord_1062624) baseStart_1062624 baseEnd_1062624 := by
    simpa [prefixWord, tailWord_1062624, baseEnd_1062624] using wordTrace_append hprefix tailTrace_1062624
  have hstable : (prefixWord ++ tailWord_1062624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062624).length < 2 ^ (prefixWord ++ tailWord_1062624).sum := by decide
  have hdescent : baseEnd_1062624 < baseStart_1062624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062635 : List Nat := [1, 1, 1, 1, 2, 4, 5, 3, 1, 2, 2]
def baseStart_1062635 : Nat := 118140960795 + 1062635 * 2 ^ 59
def prefixEnd_1062635 : Nat := 4983230072969 + 3 ^ 40 * 1062635 * 2
def baseEnd_1062635 : Nat := 545642515290555169375537

theorem tailTrace_1062635 : CollatzResearch.WordTrace tailWord_1062635 prefixEnd_1062635 545642515290555169375537 := by
  unfold tailWord_1062635
  simp only [CollatzResearch.WordTrace]
  refine ⟨38757482505262353454461359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25838321670174902302974239 38757482505262353454461359)
  ·
    refine ⟨58136223757893530181692039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38757482505262353454461359 58136223757893530181692039)
    ·
      refine ⟨87204335636840295272538059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58136223757893530181692039 87204335636840295272538059)
      ·
        refine ⟨130806503455260442908807089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87204335636840295272538059 130806503455260442908807089)
        ·
          refine ⟨98104877591445332181605317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130806503455260442908807089 98104877591445332181605317)
          ·
            refine ⟨18394664548395999784050997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98104877591445332181605317 18394664548395999784050997)
            ·
              refine ⟨1724499801412124979754781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18394664548395999784050997 1724499801412124979754781)
              ·
                refine ⟨646687425529546867408043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1724499801412124979754781 646687425529546867408043)
                ·
                  refine ⟨970031138294320301112065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646687425529546867408043 970031138294320301112065)
                  ·
                    refine ⟨727523353720740225834049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 970031138294320301112065 727523353720740225834049)
                    ·
                      refine ⟨545642515290555169375537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727523353720740225834049 545642515290555169375537)
                      ·
                        rfl

theorem cell23_1062635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 1, 2, 2].length) (baseStart_1062635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062635 prefixEnd_1062635 := by exact prefixLift 1062635
  have htrace : WordTrace (prefixWord ++ tailWord_1062635) baseStart_1062635 baseEnd_1062635 := by
    simpa [prefixWord, tailWord_1062635, baseEnd_1062635] using wordTrace_append hprefix tailTrace_1062635
  have hstable : (prefixWord ++ tailWord_1062635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062635).length < 2 ^ (prefixWord ++ tailWord_1062635).sum := by decide
  have hdescent : baseEnd_1062635 < baseStart_1062635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062652 : List Nat := [2, 2, 2, 1, 3, 1, 5, 2, 1, 2, 2]
def baseStart_1062652 : Nat := 118140960795 + 1062652 * 2 ^ 59
def prefixEnd_1062652 : Nat := 4983230072969 + 3 ^ 40 * 1062652 * 2
def baseEnd_1062652 : Nat := 545651244461681602862959

theorem tailTrace_1062652 : CollatzResearch.WordTrace tailWord_1062652 prefixEnd_1062652 545651244461681602862959 := by
  unfold tailWord_1062652
  simp only [CollatzResearch.WordTrace]
  refine ⟨19379051273100382678915105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25838735030800510238553473 19379051273100382678915105)
  ·
    refine ⟨14534288454825287009186329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19379051273100382678915105 14534288454825287009186329)
    ·
      refine ⟨10900716341118965256889747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14534288454825287009186329 10900716341118965256889747)
      ·
        refine ⟨16351074511678447885334621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10900716341118965256889747 16351074511678447885334621)
        ·
          refine ⟨6131652941879417957000483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16351074511678447885334621 6131652941879417957000483)
          ·
            refine ⟨9197479412819126935500725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6131652941879417957000483 9197479412819126935500725)
            ·
              refine ⟨862263694951793150203193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9197479412819126935500725 862263694951793150203193)
              ·
                refine ⟨646697771213844862652395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 862263694951793150203193 646697771213844862652395)
                ·
                  refine ⟨970046656820767293978593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646697771213844862652395 970046656820767293978593)
                  ·
                    refine ⟨727534992615575470483945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 970046656820767293978593 727534992615575470483945)
                    ·
                      refine ⟨545651244461681602862959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727534992615575470483945 545651244461681602862959)
                      ·
                        rfl

theorem cell23_1062652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_1062652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062652 prefixEnd_1062652 := by exact prefixLift 1062652
  have htrace : WordTrace (prefixWord ++ tailWord_1062652) baseStart_1062652 baseEnd_1062652 := by
    simpa [prefixWord, tailWord_1062652, baseEnd_1062652] using wordTrace_append hprefix tailTrace_1062652
  have hstable : (prefixWord ++ tailWord_1062652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062652).length < 2 ^ (prefixWord ++ tailWord_1062652).sum := by decide
  have hdescent : baseEnd_1062652 < baseStart_1062652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062691 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 3, 4, 2]
def baseStart_1062691 : Nat := 118140960795 + 1062691 * 2 ^ 59
def prefixEnd_1062691 : Nat := 4983230072969 + 3 ^ 40 * 1062691 * 2
def baseEnd_1062691 : Nat := 545671270207206950275279

theorem tailTrace_1062691 : CollatzResearch.WordTrace tailWord_1062691 prefixEnd_1062691 545671270207206950275279 := by
  unfold tailWord_1062691
  simp only [CollatzResearch.WordTrace]
  refine ⟨38759524993059475018499927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25839683328706316678999951 38759524993059475018499927)
  ·
    refine ⟨58139287489589212527749891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38759524993059475018499927 58139287489589212527749891)
    ·
      refine ⟨87208931234383818791624837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58139287489589212527749891 87208931234383818791624837)
      ·
        refine ⟨16351674606446966023429657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87208931234383818791624837 16351674606446966023429657)
        ·
          refine ⟨12263755954835224517572243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16351674606446966023429657 12263755954835224517572243)
          ·
            refine ⟨18395633932252836776358365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12263755954835224517572243 18395633932252836776358365)
            ·
              refine ⟨6898362724594813791134387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18395633932252836776358365 6898362724594813791134387)
              ·
                refine ⟨10347544086892220686701581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6898362724594813791134387 10347544086892220686701581)
                ·
                  refine ⟨3880329032584582757513093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10347544086892220686701581 3880329032584582757513093)
                  ·
                    refine ⟨727561693609609267033705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3880329032584582757513093 727561693609609267033705)
                    ·
                      refine ⟨545671270207206950275279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727561693609609267033705 545671270207206950275279)
                      ·
                        rfl

theorem cell23_1062691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_1062691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062691 prefixEnd_1062691 := by exact prefixLift 1062691
  have htrace : WordTrace (prefixWord ++ tailWord_1062691) baseStart_1062691 baseEnd_1062691 := by
    simpa [prefixWord, tailWord_1062691, baseEnd_1062691] using wordTrace_append hprefix tailTrace_1062691
  have hstable : (prefixWord ++ tailWord_1062691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062691).length < 2 ^ (prefixWord ++ tailWord_1062691).sum := by decide
  have hdescent : baseEnd_1062691 < baseStart_1062691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062702 : List Nat := [4, 1, 3, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1062702 : Nat := 118140960795 + 1062702 * 2 ^ 59
def prefixEnd_1062702 : Nat := 4983230072969 + 3 ^ 40 * 1062702 * 2
def baseEnd_1062702 : Nat := 545676918494406407237729

theorem tailTrace_1062702 : CollatzResearch.WordTrace tailWord_1062702 prefixEnd_1062702 545676918494406407237729 := by
  unfold tailWord_1062702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4844990774502452987143795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25839950797346415931433573 4844990774502452987143795)
  ·
    refine ⟨7267486161753679480715693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4844990774502452987143795 7267486161753679480715693)
    ·
      refine ⟨2725307310657629805268385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7267486161753679480715693 2725307310657629805268385)
      ·
        refine ⟨2043980482993222353951289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2725307310657629805268385 2043980482993222353951289)
        ·
          refine ⟨1532985362244916765463467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2043980482993222353951289 1532985362244916765463467)
          ·
            refine ⟨2299478043367375148195201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1532985362244916765463467 2299478043367375148195201)
            ·
              refine ⟨1724608532525531361146401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2299478043367375148195201 1724608532525531361146401)
              ·
                refine ⟨1293456399394148520859801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1724608532525531361146401 1293456399394148520859801)
                ·
                  refine ⟨970092299545611390644851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1293456399394148520859801 970092299545611390644851)
                  ·
                    refine ⟨1455138449318417085967277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 970092299545611390644851 1455138449318417085967277)
                    ·
                      refine ⟨545676918494406407237729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1455138449318417085967277 545676918494406407237729)
                      ·
                        rfl

theorem cell23_1062702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1062702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062702 prefixEnd_1062702 := by exact prefixLift 1062702
  have htrace : WordTrace (prefixWord ++ tailWord_1062702) baseStart_1062702 baseEnd_1062702 := by
    simpa [prefixWord, tailWord_1062702, baseEnd_1062702] using wordTrace_append hprefix tailTrace_1062702
  have hstable : (prefixWord ++ tailWord_1062702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062702).length < 2 ^ (prefixWord ++ tailWord_1062702).sum := by decide
  have hdescent : baseEnd_1062702 < baseStart_1062702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062801 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 3]
def baseStart_1062801 : Nat := 118140960795 + 1062801 * 2 ^ 59
def prefixEnd_1062801 : Nat := 4983230072969 + 3 ^ 40 * 1062801 * 2
def baseEnd_1062801 : Nat := 545727753079201519899773

theorem tailTrace_1062801 : CollatzResearch.WordTrace tailWord_1062801 prefixEnd_1062801 545727753079201519899773 := by
  unfold tailWord_1062801
  simp only [CollatzResearch.WordTrace]
  refine ⟨38763537022660963805004257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25842358015107309203336171 38763537022660963805004257)
  ·
    refine ⟨29072652766995722853753193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38763537022660963805004257 29072652766995722853753193)
    ·
      refine ⟨21804489575246792140314895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29072652766995722853753193 21804489575246792140314895)
      ·
        refine ⟨32706734362870188210472343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21804489575246792140314895 32706734362870188210472343)
        ·
          refine ⟨49060101544305282315708515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32706734362870188210472343 49060101544305282315708515)
          ·
            refine ⟨73590152316457923473562773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49060101544305282315708515 73590152316457923473562773)
            ·
              refine ⟨3449538389833965162823255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73590152316457923473562773 3449538389833965162823255)
              ·
                refine ⟨5174307584750947744234883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3449538389833965162823255 5174307584750947744234883)
                ·
                  refine ⟨7761461377126421616352325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5174307584750947744234883 7761461377126421616352325)
                  ·
                    refine ⟨1455274008211204053066061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7761461377126421616352325 1455274008211204053066061)
                    ·
                      refine ⟨545727753079201519899773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1455274008211204053066061 545727753079201519899773)
                      ·
                        rfl

theorem cell23_1062801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_1062801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062801 prefixEnd_1062801 := by exact prefixLift 1062801
  have htrace : WordTrace (prefixWord ++ tailWord_1062801) baseStart_1062801 baseEnd_1062801 := by
    simpa [prefixWord, tailWord_1062801, baseEnd_1062801] using wordTrace_append hprefix tailTrace_1062801
  have hstable : (prefixWord ++ tailWord_1062801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062801).length < 2 ^ (prefixWord ++ tailWord_1062801).sum := by decide
  have hdescent : baseEnd_1062801 < baseStart_1062801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062848 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 5, 1, 3]
def baseStart_1062848 : Nat := 118140960795 + 1062848 * 2 ^ 59
def prefixEnd_1062848 : Nat := 4983230072969 + 3 ^ 40 * 1062848 * 2
def baseEnd_1062848 : Nat := 545751886669962836012057

theorem tailTrace_1062848 : CollatzResearch.WordTrace tailWord_1062848 prefixEnd_1062848 545751886669962836012057 := by
  unfold tailWord_1062848
  simp only [CollatzResearch.WordTrace]
  refine ⟨19382625626745345415982599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25843500835660460554643465 19382625626745345415982599)
  ·
    refine ⟨29073938440118018123973899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19382625626745345415982599 29073938440118018123973899)
    ·
      refine ⟨43610907660177027185960849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29073938440118018123973899 43610907660177027185960849)
      ·
        refine ⟨32708180745132770389470637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43610907660177027185960849 32708180745132770389470637)
        ·
          refine ⟨12265567779424788896051489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32708180745132770389470637 12265567779424788896051489)
          ·
            refine ⟨9199175834568591672038617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12265567779424788896051489 9199175834568591672038617)
            ·
              refine ⟨6899381875926443754028963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9199175834568591672038617 6899381875926443754028963)
              ·
                refine ⟨10349072813889665631043445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6899381875926443754028963 10349072813889665631043445)
                ·
                  refine ⟨970225576302156152910323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10349072813889665631043445 970225576302156152910323)
                  ·
                    refine ⟨1455338364453234229365485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 970225576302156152910323 1455338364453234229365485)
                    ·
                      refine ⟨545751886669962836012057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1455338364453234229365485 545751886669962836012057)
                      ·
                        rfl

theorem cell23_1062848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_1062848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062848 prefixEnd_1062848 := by exact prefixLift 1062848
  have htrace : WordTrace (prefixWord ++ tailWord_1062848) baseStart_1062848 baseEnd_1062848 := by
    simpa [prefixWord, tailWord_1062848, baseEnd_1062848] using wordTrace_append hprefix tailTrace_1062848
  have hstable : (prefixWord ++ tailWord_1062848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062848).length < 2 ^ (prefixWord ++ tailWord_1062848).sum := by decide
  have hdescent : baseEnd_1062848 < baseStart_1062848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062858 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 1, 5, 2]
def baseStart_1062858 : Nat := 118140960795 + 1062858 * 2 ^ 59
def prefixEnd_1062858 : Nat := 4983230072969 + 3 ^ 40 * 1062858 * 2
def baseEnd_1062858 : Nat := 545757021476507796887011

theorem tailTrace_1062858 : CollatzResearch.WordTrace tailWord_1062858 prefixEnd_1062858 545757021476507796887011 := by
  unfold tailWord_1062858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9691403995863615634957307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25843743988969641693219485 9691403995863615634957307)
  ·
    refine ⟨14537105993795423452435961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9691403995863615634957307 14537105993795423452435961)
    ·
      refine ⟨10902829495346567589326971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14537105993795423452435961 10902829495346567589326971)
      ·
        refine ⟨16354244243019851383990457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10902829495346567589326971 16354244243019851383990457)
        ·
          refine ⟨12265683182264888537992843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16354244243019851383990457 12265683182264888537992843)
          ·
            refine ⟨18398524773397332806989265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12265683182264888537992843 18398524773397332806989265)
            ·
              refine ⟨13798893580047999605241949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18398524773397332806989265 13798893580047999605241949)
              ·
                refine ⟨5174585092517999851965731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13798893580047999605241949 5174585092517999851965731)
                ·
                  refine ⟨7761877638776999777948597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5174585092517999851965731 7761877638776999777948597)
                  ·
                    refine ⟨727676028635343729182681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7761877638776999777948597 727676028635343729182681)
                    ·
                      refine ⟨545757021476507796887011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727676028635343729182681 545757021476507796887011)
                      ·
                        rfl

theorem cell23_1062858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_1062858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062858 prefixEnd_1062858 := by exact prefixLift 1062858
  have htrace : WordTrace (prefixWord ++ tailWord_1062858) baseStart_1062858 baseEnd_1062858 := by
    simpa [prefixWord, tailWord_1062858, baseEnd_1062858] using wordTrace_append hprefix tailTrace_1062858
  have hstable : (prefixWord ++ tailWord_1062858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062858).length < 2 ^ (prefixWord ++ tailWord_1062858).sum := by decide
  have hdescent : baseEnd_1062858 < baseStart_1062858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062876 : List Nat := [2, 2, 6, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1062876 : Nat := 118140960795 + 1062876 * 2 ^ 59
def prefixEnd_1062876 : Nat := 4983230072969 + 3 ^ 40 * 1062876 * 2
def baseEnd_1062876 : Nat := 181922088042762908820643

theorem tailTrace_1062876 : CollatzResearch.WordTrace tailWord_1062876 prefixEnd_1062876 181922088042762908820643 := by
  unfold tailWord_1062876
  simp only [CollatzResearch.WordTrace]
  refine ⟨19383136248694625806992241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25844181664926167742656321 19383136248694625806992241)
  ·
    refine ⟨14537352186520969355244181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19383136248694625806992241 14537352186520969355244181)
    ·
      refine ⟨681438383743170438527071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14537352186520969355244181 681438383743170438527071)
      ·
        refine ⟨1022157575614755657790607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681438383743170438527071 1022157575614755657790607)
        ·
          refine ⟨1533236363422133486685911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022157575614755657790607 1533236363422133486685911)
          ·
            refine ⟨2299854545133200230028867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533236363422133486685911 2299854545133200230028867)
            ·
              refine ⟨3449781817699800345043301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2299854545133200230028867 3449781817699800345043301)
              ·
                refine ⟨646834090818712564695619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3449781817699800345043301 646834090818712564695619)
                ·
                  refine ⟨970251136228068847043429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646834090818712564695619 970251136228068847043429)
                  ·
                    refine ⟨181922088042762908820643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 970251136228068847043429 181922088042762908820643)
                    ·
                      rfl

theorem cell23_1062876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1062876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062876 prefixEnd_1062876 := by exact prefixLift 1062876
  have htrace : WordTrace (prefixWord ++ tailWord_1062876) baseStart_1062876 baseEnd_1062876 := by
    simpa [prefixWord, tailWord_1062876, baseEnd_1062876] using wordTrace_append hprefix tailTrace_1062876
  have hstable : (prefixWord ++ tailWord_1062876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062876).length < 2 ^ (prefixWord ++ tailWord_1062876).sum := by decide
  have hdescent : baseEnd_1062876 < baseStart_1062876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062888 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_1062888 : Nat := 118140960795 + 1062888 * 2 ^ 59
def prefixEnd_1062888 : Nat := 4983230072969 + 3 ^ 40 * 1062888 * 2
def baseEnd_1062888 : Nat := 545772425896142679511873

theorem tailTrace_1062888 : CollatzResearch.WordTrace tailWord_1062888 prefixEnd_1062888 545772425896142679511873 := by
  unfold tailWord_1062888
  simp only [CollatzResearch.WordTrace]
  refine ⟨19383355086672888831710659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25844473448897185108947545 19383355086672888831710659)
  ·
    refine ⟨29075032630009333247565989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19383355086672888831710659 29075032630009333247565989)
    ·
      refine ⟨5451568618126749983918623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29075032630009333247565989 5451568618126749983918623)
      ·
        refine ⟨8177352927190124975877935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5451568618126749983918623 8177352927190124975877935)
        ·
          refine ⟨12266029390785187463816903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8177352927190124975877935 12266029390785187463816903)
          ·
            refine ⟨18399044086177781195725355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12266029390785187463816903 18399044086177781195725355)
            ·
              refine ⟨27598566129266671793588033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18399044086177781195725355 27598566129266671793588033)
              ·
                refine ⟨20698924596950003845191025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27598566129266671793588033 20698924596950003845191025)
                ·
                  refine ⟨15524193447712502883893269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20698924596950003845191025 15524193447712502883893269)
                  ·
                    refine ⟨727696567861523572682497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15524193447712502883893269 727696567861523572682497)
                    ·
                      refine ⟨545772425896142679511873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727696567861523572682497 545772425896142679511873)
                      ·
                        rfl

theorem cell23_1062888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_1062888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062888 prefixEnd_1062888 := by exact prefixLift 1062888
  have htrace : WordTrace (prefixWord ++ tailWord_1062888) baseStart_1062888 baseEnd_1062888 := by
    simpa [prefixWord, tailWord_1062888, baseEnd_1062888] using wordTrace_append hprefix tailTrace_1062888
  have hstable : (prefixWord ++ tailWord_1062888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062888).length < 2 ^ (prefixWord ++ tailWord_1062888).sum := by decide
  have hdescent : baseEnd_1062888 < baseStart_1062888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062891 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 5]
def baseStart_1062891 : Nat := 118140960795 + 1062891 * 2 ^ 59
def prefixEnd_1062891 : Nat := 4983230072969 + 3 ^ 40 * 1062891 * 2
def baseEnd_1062891 : Nat := 545773966338106167774359

theorem tailTrace_1062891 : CollatzResearch.WordTrace tailWord_1062891 prefixEnd_1062891 545773966338106167774359 := by
  unfold tailWord_1062891
  simp only [CollatzResearch.WordTrace]
  refine ⟨38766819592334909175780527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25844546394889939450520351 38766819592334909175780527)
  ·
    refine ⟨58150229388502363763670791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38766819592334909175780527 58150229388502363763670791)
    ·
      refine ⟨87225344082753545645506187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58150229388502363763670791 87225344082753545645506187)
      ·
        refine ⟨130838016124130318468259281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87225344082753545645506187 130838016124130318468259281)
        ·
          refine ⟨98128512093097738851194461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130838016124130318468259281 98128512093097738851194461)
          ·
            refine ⟨36798192034911652069197923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98128512093097738851194461 36798192034911652069197923)
            ·
              refine ⟨55197288052367478103796885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36798192034911652069197923 55197288052367478103796885)
              ·
                refine ⟨2587372877454725536115479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55197288052367478103796885 2587372877454725536115479)
                ·
                  refine ⟨3881059316182088304173219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2587372877454725536115479 3881059316182088304173219)
                  ·
                    refine ⟨5821588974273132456259829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3881059316182088304173219 5821588974273132456259829)
                    ·
                      refine ⟨545773966338106167774359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5821588974273132456259829 545773966338106167774359)
                      ·
                        rfl

theorem cell23_1062891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 5].length) (baseStart_1062891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062891 prefixEnd_1062891 := by exact prefixLift 1062891
  have htrace : WordTrace (prefixWord ++ tailWord_1062891) baseStart_1062891 baseEnd_1062891 := by
    simpa [prefixWord, tailWord_1062891, baseEnd_1062891] using wordTrace_append hprefix tailTrace_1062891
  have hstable : (prefixWord ++ tailWord_1062891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062891).length < 2 ^ (prefixWord ++ tailWord_1062891).sum := by decide
  have hdescent : baseEnd_1062891 < baseStart_1062891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062905 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 5, 2, 2]
def baseStart_1062905 : Nat := 118140960795 + 1062905 * 2 ^ 59
def prefixEnd_1062905 : Nat := 4983230072969 + 3 ^ 40 * 1062905 * 2
def baseEnd_1062905 : Nat := 545781155067269112999295

theorem tailTrace_1062905 : CollatzResearch.WordTrace tailWord_1062905 prefixEnd_1062905 545781155067269112999295 := by
  unfold tailWord_1062905
  simp only [CollatzResearch.WordTrace]
  refine ⟨38767330214284189566790169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25844886809522793044526779 38767330214284189566790169)
  ·
    refine ⟨29075497660713142175092627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38767330214284189566790169 29075497660713142175092627)
    ·
      refine ⟨43613246491069713262638941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29075497660713142175092627 43613246491069713262638941)
      ·
        refine ⟨16354967434151142473489603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43613246491069713262638941 16354967434151142473489603)
        ·
          refine ⟨24532451151226713710234405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16354967434151142473489603 24532451151226713710234405)
          ·
            refine ⟨4599834590855008820668951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24532451151226713710234405 4599834590855008820668951)
            ·
              refine ⟨6899751886282513231003427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4599834590855008820668951 6899751886282513231003427)
              ·
                refine ⟨10349627829423769846505141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6899751886282513231003427 10349627829423769846505141)
                ·
                  refine ⟨970277609008478423109857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10349627829423769846505141 970277609008478423109857)
                  ·
                    refine ⟨727708206756358817332393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 970277609008478423109857 727708206756358817332393)
                    ·
                      refine ⟨545781155067269112999295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727708206756358817332393 545781155067269112999295)
                      ·
                        rfl

theorem cell23_1062905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_1062905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062905 prefixEnd_1062905 := by exact prefixLift 1062905
  have htrace : WordTrace (prefixWord ++ tailWord_1062905) baseStart_1062905 baseEnd_1062905 := by
    simpa [prefixWord, tailWord_1062905, baseEnd_1062905] using wordTrace_append hprefix tailTrace_1062905
  have hstable : (prefixWord ++ tailWord_1062905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062905).length < 2 ^ (prefixWord ++ tailWord_1062905).sum := by decide
  have hdescent : baseEnd_1062905 < baseStart_1062905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062908 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_1062908 : Nat := 118140960795 + 1062908 * 2 ^ 59
def prefixEnd_1062908 : Nat := 4983230072969 + 3 ^ 40 * 1062908 * 2
def baseEnd_1062908 : Nat := 545782695509232601261781

theorem tailTrace_1062908 : CollatzResearch.WordTrace tailWord_1062908 prefixEnd_1062908 545782695509232601261781 := by
  unfold tailWord_1062908
  simp only [CollatzResearch.WordTrace]
  refine ⟨19383719816636660539574689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25844959755515547386099585 19383719816636660539574689)
  ·
    refine ⟨14537789862477495404681017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19383719816636660539574689 14537789862477495404681017)
    ·
      refine ⟨10903342396858121553510763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14537789862477495404681017 10903342396858121553510763)
      ·
        refine ⟨16355013595287182330266145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10903342396858121553510763 16355013595287182330266145)
        ·
          refine ⟨12266260196465386747699609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16355013595287182330266145 12266260196465386747699609)
          ·
            refine ⟨9199695147349040060774707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12266260196465386747699609 9199695147349040060774707)
            ·
              refine ⟨13799542721023560091162061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9199695147349040060774707 13799542721023560091162061)
              ·
                refine ⟨5174828520383835034185773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13799542721023560091162061 5174828520383835034185773)
                ·
                  refine ⟨1940560695143938137819665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5174828520383835034185773 1940560695143938137819665)
                  ·
                    refine ⟨1455420521357953603364749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1940560695143938137819665 1455420521357953603364749)
                    ·
                      refine ⟨545782695509232601261781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1455420521357953603364749 545782695509232601261781)
                      ·
                        rfl

theorem cell23_1062908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_1062908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062908 prefixEnd_1062908 := by exact prefixLift 1062908
  have htrace : WordTrace (prefixWord ++ tailWord_1062908) baseStart_1062908 baseEnd_1062908 := by
    simpa [prefixWord, tailWord_1062908, baseEnd_1062908] using wordTrace_append hprefix tailTrace_1062908
  have hstable : (prefixWord ++ tailWord_1062908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062908).length < 2 ^ (prefixWord ++ tailWord_1062908).sum := by decide
  have hdescent : baseEnd_1062908 < baseStart_1062908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062916 : List Nat := [2, 3, 2, 4, 1, 1, 2, 3, 1, 1, 3]
def baseStart_1062916 : Nat := 118140960795 + 1062916 * 2 ^ 59
def prefixEnd_1062916 : Nat := 4983230072969 + 3 ^ 40 * 1062916 * 2
def baseEnd_1062916 : Nat := 545786803354468569961745

theorem tailTrace_1062916 : CollatzResearch.WordTrace tailWord_1062916 prefixEnd_1062916 545786803354468569961745 := by
  unfold tailWord_1062916
  simp only [CollatzResearch.WordTrace]
  refine ⟨19383865708622169222720301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25845154278162892296960401 19383865708622169222720301)
  ·
    refine ⟨7268949640733313458520113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19383865708622169222720301 7268949640733313458520113)
    ·
      refine ⟨5451712230549985093890085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7268949640733313458520113 5451712230549985093890085)
      ·
        refine ⟨1022196043228122205104391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5451712230549985093890085 1022196043228122205104391)
        ·
          refine ⟨1533294064842183307656587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022196043228122205104391 1533294064842183307656587)
          ·
            refine ⟨2299941097263274961484881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533294064842183307656587 2299941097263274961484881)
            ·
              refine ⟨1724955822947456221113661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2299941097263274961484881 1724955822947456221113661)
              ·
                refine ⟨646858433605296082917623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1724955822947456221113661 646858433605296082917623)
                ·
                  refine ⟨970287650407944124376435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 646858433605296082917623 970287650407944124376435)
                  ·
                    refine ⟨1455431475611916186564653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 970287650407944124376435 1455431475611916186564653)
                    ·
                      refine ⟨545786803354468569961745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1455431475611916186564653 545786803354468569961745)
                      ·
                        rfl

theorem cell23_1062916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_1062916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062916 prefixEnd_1062916 := by exact prefixLift 1062916
  have htrace : WordTrace (prefixWord ++ tailWord_1062916) baseStart_1062916 baseEnd_1062916 := by
    simpa [prefixWord, tailWord_1062916, baseEnd_1062916] using wordTrace_append hprefix tailTrace_1062916
  have hstable : (prefixWord ++ tailWord_1062916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062916).length < 2 ^ (prefixWord ++ tailWord_1062916).sum := by decide
  have hdescent : baseEnd_1062916 < baseStart_1062916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062965 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_1062965 : Nat := 118140960795 + 1062965 * 2 ^ 59
def prefixEnd_1062965 : Nat := 4983230072969 + 3 ^ 40 * 1062965 * 2
def baseEnd_1062965 : Nat := 545811963906538878249019

theorem tailTrace_1062965 : CollatzResearch.WordTrace tailWord_1062965 prefixEnd_1062965 545811963906538878249019 := by
  unfold tailWord_1062965
  simp only [CollatzResearch.WordTrace]
  refine ⟨38769518594066819813974349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25846345729377879875982899 38769518594066819813974349)
  ·
    refine ⟨14538569472775057430240381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38769518594066819813974349 14538569472775057430240381)
    ·
      refine ⟨5451963552290646536340143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14538569472775057430240381 5451963552290646536340143)
      ·
        refine ⟨8177945328435969804510215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5451963552290646536340143 8177945328435969804510215)
        ·
          refine ⟨12266917992653954706765323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8177945328435969804510215 12266917992653954706765323)
          ·
            refine ⟨18400376988980932060147985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12266917992653954706765323 18400376988980932060147985)
            ·
              refine ⟨13800282741735699045110989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18400376988980932060147985 13800282741735699045110989)
              ·
                refine ⟨5175106028150887141916621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13800282741735699045110989 5175106028150887141916621)
                ·
                  refine ⟨1940664760556582678218733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5175106028150887141916621 1940664760556582678218733)
                  ·
                    refine ⟨727749285208718504332025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1940664760556582678218733 727749285208718504332025)
                    ·
                      refine ⟨545811963906538878249019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727749285208718504332025 545811963906538878249019)
                      ·
                        rfl

theorem cell23_1062965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_1062965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062965 prefixEnd_1062965 := by exact prefixLift 1062965
  have htrace : WordTrace (prefixWord ++ tailWord_1062965) baseStart_1062965 baseEnd_1062965 := by
    simpa [prefixWord, tailWord_1062965, baseEnd_1062965] using wordTrace_append hprefix tailTrace_1062965
  have hstable : (prefixWord ++ tailWord_1062965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062965).length < 2 ^ (prefixWord ++ tailWord_1062965).sum := by decide
  have hdescent : baseEnd_1062965 < baseStart_1062965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1062995 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 8, 2, 2]
def baseStart_1062995 : Nat := 118140960795 + 1062995 * 2 ^ 59
def prefixEnd_1062995 : Nat := 4983230072969 + 3 ^ 40 * 1062995 * 2
def baseEnd_1062995 : Nat := 545827368326173760873881

theorem tailTrace_1062995 : CollatzResearch.WordTrace tailWord_1062995 prefixEnd_1062995 545827368326173760873881 := by
  unfold tailWord_1062995
  simp only [CollatzResearch.WordTrace]
  refine ⟨38770612783958134937566439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25847075189305423291710959 38770612783958134937566439)
  ·
    refine ⟨58155919175937202406349659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38770612783958134937566439 58155919175937202406349659)
    ·
      refine ⟨87233878763905803609524489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58155919175937202406349659 87233878763905803609524489)
      ·
        refine ⟨65425409072929352707143367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87233878763905803609524489 65425409072929352707143367)
        ·
          refine ⟨98138113609394029060715051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65425409072929352707143367 98138113609394029060715051)
          ·
            refine ⟨147207170414091043591072577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98138113609394029060715051 147207170414091043591072577)
            ·
              refine ⟨110405377810568282693304433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147207170414091043591072577 110405377810568282693304433)
              ·
                refine ⟨82804033357926212019978325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110405377810568282693304433 82804033357926212019978325)
                ·
                  refine ⟨970359765913197797109121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 82804033357926212019978325 970359765913197797109121)
                  ·
                    refine ⟨727769824434898347831841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 970359765913197797109121 727769824434898347831841)
                    ·
                      refine ⟨545827368326173760873881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727769824434898347831841 545827368326173760873881)
                      ·
                        rfl

theorem cell23_1062995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 2, 2].length) (baseStart_1062995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1062995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1062995 prefixEnd_1062995 := by exact prefixLift 1062995
  have htrace : WordTrace (prefixWord ++ tailWord_1062995) baseStart_1062995 baseEnd_1062995 := by
    simpa [prefixWord, tailWord_1062995, baseEnd_1062995] using wordTrace_append hprefix tailTrace_1062995
  have hstable : (prefixWord ++ tailWord_1062995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1062995).length < 2 ^ (prefixWord ++ tailWord_1062995).sum := by decide
  have hdescent : baseEnd_1062995 < baseStart_1062995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1062995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063082 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1063082 : Nat := 118140960795 + 1063082 * 2 ^ 59
def prefixEnd_1063082 : Nat := 4983230072969 + 3 ^ 40 * 1063082 * 2
def baseEnd_1063082 : Nat := 181957347047704973495327

theorem tailTrace_1063082 : CollatzResearch.WordTrace tailWord_1063082 prefixEnd_1063082 181957347047704973495327 := by
  unfold tailWord_1063082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9693446483660737198995875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25849190623095299197322333 9693446483660737198995875)
  ·
    refine ⟨14540169725491105798493813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9693446483660737198995875 14540169725491105798493813)
    ·
      refine ⟨1363140911764791168608795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14540169725491105798493813 1363140911764791168608795)
      ·
        refine ⟨2044711367647186752913193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1363140911764791168608795 2044711367647186752913193)
        ·
          refine ⟨1533533525735390064684895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2044711367647186752913193 1533533525735390064684895)
          ·
            refine ⟨2300300288603085097027343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533533525735390064684895 2300300288603085097027343)
            ·
              refine ⟨3450450432904627645541015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2300300288603085097027343 3450450432904627645541015)
              ·
                refine ⟨5175675649356941468311523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3450450432904627645541015 5175675649356941468311523)
                ·
                  refine ⟨7763513474035412202467285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5175675649356941468311523 7763513474035412202467285)
                  ·
                    refine ⟨181957347047704973495327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7763513474035412202467285 181957347047704973495327)
                    ·
                      rfl

theorem cell23_1063082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1063082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063082 prefixEnd_1063082 := by exact prefixLift 1063082
  have htrace : WordTrace (prefixWord ++ tailWord_1063082) baseStart_1063082 baseEnd_1063082 := by
    simpa [prefixWord, tailWord_1063082, baseEnd_1063082] using wordTrace_append hprefix tailTrace_1063082
  have hstable : (prefixWord ++ tailWord_1063082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063082).length < 2 ^ (prefixWord ++ tailWord_1063082).sum := by decide
  have hdescent : baseEnd_1063082 < baseStart_1063082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063086 : List Nat := [4, 1, 4, 2, 1, 1, 2, 3, 5]
def baseStart_1063086 : Nat := 118140960795 + 1063086 * 2 ^ 59
def prefixEnd_1063086 : Nat := 4983230072969 + 3 ^ 40 * 1063086 * 2
def baseEnd_1063086 : Nat := 60652677229525878315107

theorem tailTrace_1063086 : CollatzResearch.WordTrace tailWord_1063086 prefixEnd_1063086 60652677229525878315107 := by
  unfold tailWord_1063086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4846741478328557184891139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25849287884418971652752741 4846741478328557184891139)
  ·
    refine ⟨7270112217492835777336709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4846741478328557184891139 7270112217492835777336709)
    ·
      refine ⟨1363146040779906708250633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7270112217492835777336709 1363146040779906708250633)
      ·
        refine ⟨1022359530584930031187975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1363146040779906708250633 1022359530584930031187975)
        ·
          refine ⟨1533539295877395046781963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022359530584930031187975 1533539295877395046781963)
          ·
            refine ⟨2300308943816092570172945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533539295877395046781963 2300308943816092570172945)
            ·
              refine ⟨1725231707862069427629709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2300308943816092570172945 1725231707862069427629709)
              ·
                refine ⟨646961890448276035361141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1725231707862069427629709 646961890448276035361141)
                ·
                  refine ⟨60652677229525878315107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 646961890448276035361141 60652677229525878315107)
                  ·
                    rfl

theorem cell23_1063086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_1063086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063086 prefixEnd_1063086 := by exact prefixLift 1063086
  have htrace : WordTrace (prefixWord ++ tailWord_1063086) baseStart_1063086 baseEnd_1063086 := by
    simpa [prefixWord, tailWord_1063086, baseEnd_1063086] using wordTrace_append hprefix tailTrace_1063086
  have hstable : (prefixWord ++ tailWord_1063086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063086).length < 2 ^ (prefixWord ++ tailWord_1063086).sum := by decide
  have hdescent : baseEnd_1063086 < baseStart_1063086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063098 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_1063098 : Nat := 118140960795 + 1063098 * 2 ^ 59
def prefixEnd_1063098 : Nat := 4983230072969 + 3 ^ 40 * 1063098 * 2
def baseEnd_1063098 : Nat := 545880256833586857885907

theorem tailTrace_1063098 : CollatzResearch.WordTrace tailWord_1063098 prefixEnd_1063098 545880256833586857885907 := by
  unfold tailWord_1063098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9693592375646245882141487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25849579668389989019043965 9693592375646245882141487)
  ·
    refine ⟨14540388563469368823212231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9693592375646245882141487 14540388563469368823212231)
    ·
      refine ⟨21810582845204053234818347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14540388563469368823212231 21810582845204053234818347)
      ·
        refine ⟨32715874267806079852227521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21810582845204053234818347 32715874267806079852227521)
        ·
          refine ⟨24536905700854559889170641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32715874267806079852227521 24536905700854559889170641)
          ·
            refine ⟨18402679275640919916877981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24536905700854559889170641 18402679275640919916877981)
            ·
              refine ⟨6901004728365344968829243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18402679275640919916877981 6901004728365344968829243)
              ·
                refine ⟨10351507092548017453243865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6901004728365344968829243 10351507092548017453243865)
                ·
                  refine ⟨7763630319411013089932899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10351507092548017453243865 7763630319411013089932899)
                  ·
                    refine ⟨11645445479116519634899349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7763630319411013089932899 11645445479116519634899349)
                    ·
                      refine ⟨545880256833586857885907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11645445479116519634899349 545880256833586857885907)
                      ·
                        rfl

theorem cell23_1063098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_1063098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063098 prefixEnd_1063098 := by exact prefixLift 1063098
  have htrace : WordTrace (prefixWord ++ tailWord_1063098) baseStart_1063098 baseEnd_1063098 := by
    simpa [prefixWord, tailWord_1063098, baseEnd_1063098] using wordTrace_append hprefix tailTrace_1063098
  have hstable : (prefixWord ++ tailWord_1063098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063098).length < 2 ^ (prefixWord ++ tailWord_1063098).sum := by decide
  have hdescent : baseEnd_1063098 < baseStart_1063098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063155 : List Nat := [1, 1, 1, 2, 2, 4, 1, 5, 1, 5]
def baseStart_1063155 : Nat := 118140960795 + 1063155 * 2 ^ 59
def prefixEnd_1063155 : Nat := 4983230072969 + 3 ^ 40 * 1063155 * 2
def baseEnd_1063155 : Nat := 181969841743631044957715

theorem tailTrace_1063155 : CollatzResearch.WordTrace tailWord_1063155 prefixEnd_1063155 181969841743631044957715 := by
  unfold tailWord_1063155
  simp only [CollatzResearch.WordTrace]
  refine ⟨38776448463378482263390919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25850965642252321508927279 38776448463378482263390919)
  ·
    refine ⟨58164672695067723395086379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38776448463378482263390919 58164672695067723395086379)
    ·
      refine ⟨87247009042601585092629569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58164672695067723395086379 87247009042601585092629569)
      ·
        refine ⟨65435256781951188819472177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87247009042601585092629569 65435256781951188819472177)
        ·
          refine ⟨49076442586463391614604133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65435256781951188819472177 49076442586463391614604133)
          ·
            refine ⟨9201832984961885927738275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49076442586463391614604133 9201832984961885927738275)
            ·
              refine ⟨13802749477442828891607413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9201832984961885927738275 13802749477442828891607413)
              ·
                refine ⟨1294007763510265208588195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13802749477442828891607413 1294007763510265208588195)
                ·
                  refine ⟨1941011645265397812882293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294007763510265208588195 1941011645265397812882293)
                  ·
                    refine ⟨181969841743631044957715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1941011645265397812882293 181969841743631044957715)
                    ·
                      rfl

theorem cell23_1063155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 5].length) (baseStart_1063155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063155 prefixEnd_1063155 := by exact prefixLift 1063155
  have htrace : WordTrace (prefixWord ++ tailWord_1063155) baseStart_1063155 baseEnd_1063155 := by
    simpa [prefixWord, tailWord_1063155, baseEnd_1063155] using wordTrace_append hprefix tailTrace_1063155
  have hstable : (prefixWord ++ tailWord_1063155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063155).length < 2 ^ (prefixWord ++ tailWord_1063155).sum := by decide
  have hdescent : baseEnd_1063155 < baseStart_1063155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063162 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2]
def baseStart_1063162 : Nat := 118140960795 + 1063162 * 2 ^ 59
def prefixEnd_1063162 : Nat := 4983230072969 + 3 ^ 40 * 1063162 * 2
def baseEnd_1063162 : Nat := 545913119595474607485613

theorem tailTrace_1063162 : CollatzResearch.WordTrace tailWord_1063162 prefixEnd_1063162 545913119595474607485613 := by
  unfold tailWord_1063162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9694175943588280614723935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25851135849568748305930493 9694175943588280614723935)
  ·
    refine ⟨14541263915382420922085903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9694175943588280614723935 14541263915382420922085903)
    ·
      refine ⟨21811895873073631383128855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14541263915382420922085903 21811895873073631383128855)
      ·
        refine ⟨32717843809610447074693283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21811895873073631383128855 32717843809610447074693283)
        ·
          refine ⟨49076765714415670612039925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32717843809610447074693283 49076765714415670612039925)
          ·
            refine ⟨4600946785726469119878743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49076765714415670612039925 4600946785726469119878743)
            ·
              refine ⟨6901420178589703679818115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4600946785726469119878743 6901420178589703679818115)
              ·
                refine ⟨10352130267884555519727173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6901420178589703679818115 10352130267884555519727173)
                ·
                  refine ⟨1941024425228354159948845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10352130267884555519727173 1941024425228354159948845)
                  ·
                    refine ⟨727884159460632809980817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1941024425228354159948845 727884159460632809980817)
                    ·
                      refine ⟨545913119595474607485613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 727884159460632809980817 545913119595474607485613)
                      ·
                        rfl

theorem cell23_1063162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2].length) (baseStart_1063162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063162 prefixEnd_1063162 := by exact prefixLift 1063162
  have htrace : WordTrace (prefixWord ++ tailWord_1063162) baseStart_1063162 baseEnd_1063162 := by
    simpa [prefixWord, tailWord_1063162, baseEnd_1063162] using wordTrace_append hprefix tailTrace_1063162
  have hstable : (prefixWord ++ tailWord_1063162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063162).length < 2 ^ (prefixWord ++ tailWord_1063162).sum := by decide
  have hdescent : baseEnd_1063162 < baseStart_1063162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063202 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_1063202 : Nat := 118140960795 + 1063202 * 2 ^ 59
def prefixEnd_1063202 : Nat := 4983230072969 + 3 ^ 40 * 1063202 * 2
def baseEnd_1063202 : Nat := 181977886273884816995143

theorem tailTrace_1063202 : CollatzResearch.WordTrace tailWord_1063202 prefixEnd_1063202 181977886273884816995143 := by
  unfold tailWord_1063202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9694540673552052322587965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25852108462805472860234573 9694540673552052322587965)
  ·
    refine ⟨3635452752582019620970487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9694540673552052322587965 3635452752582019620970487)
    ·
      refine ⟨5453179128873029431455731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3635452752582019620970487 5453179128873029431455731)
      ·
        refine ⟨8179768693309544147183597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5453179128873029431455731 8179768693309544147183597)
        ·
          refine ⟨3067413259991079055193849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8179768693309544147183597 3067413259991079055193849)
          ·
            refine ⟨2300559944993309291395387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3067413259991079055193849 2300559944993309291395387)
            ·
              refine ⟨3450839917489963937093081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2300559944993309291395387 3450839917489963937093081)
              ·
                refine ⟨2588129938117472952819811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3450839917489963937093081 2588129938117472952819811)
                ·
                  refine ⟨3882194907176209429229717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2588129938117472952819811 3882194907176209429229717)
                  ·
                    refine ⟨181977886273884816995143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3882194907176209429229717 181977886273884816995143)
                    ·
                      rfl

theorem cell23_1063202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_1063202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063202 prefixEnd_1063202 := by exact prefixLift 1063202
  have htrace : WordTrace (prefixWord ++ tailWord_1063202) baseStart_1063202 baseEnd_1063202 := by
    simpa [prefixWord, tailWord_1063202, baseEnd_1063202] using wordTrace_append hprefix tailTrace_1063202
  have hstable : (prefixWord ++ tailWord_1063202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063202).length < 2 ^ (prefixWord ++ tailWord_1063202).sum := by decide
  have hdescent : baseEnd_1063202 < baseStart_1063202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063212 : List Nat := [2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 3]
def baseStart_1063212 : Nat := 118140960795 + 1063212 * 2 ^ 59
def prefixEnd_1063212 : Nat := 4983230072969 + 3 ^ 40 * 1063212 * 2
def baseEnd_1063212 : Nat := 545938793628199411860383

theorem tailTrace_1063212 : CollatzResearch.WordTrace tailWord_1063212 prefixEnd_1063212 545938793628199411860383 := by
  unfold tailWord_1063212
  simp only [CollatzResearch.WordTrace]
  refine ⟨19389263712085990499107945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25852351616114653998810593 19389263712085990499107945)
  ·
    refine ⟨14541947784064492874330959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19389263712085990499107945 14541947784064492874330959)
    ·
      refine ⟨21812921676096739311496439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14541947784064492874330959 21812921676096739311496439)
      ·
        refine ⟨32719382514145108967244659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21812921676096739311496439 32719382514145108967244659)
        ·
          refine ⟨49079073771217663450866989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32719382514145108967244659 49079073771217663450866989)
          ·
            refine ⟨18404652664206623794075121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49079073771217663450866989 18404652664206623794075121)
            ·
              refine ⟨13803489498154967845556341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18404652664206623794075121 13803489498154967845556341)
              ·
                refine ⟨1294077140452028235520907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13803489498154967845556341 1294077140452028235520907)
                ·
                  refine ⟨1941115710678042353281361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294077140452028235520907 1941115710678042353281361)
                  ·
                    refine ⟨1455836783008531764961021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1941115710678042353281361 1455836783008531764961021)
                    ·
                      refine ⟨545938793628199411860383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1455836783008531764961021 545938793628199411860383)
                      ·
                        rfl

theorem cell23_1063212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_1063212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063212 prefixEnd_1063212 := by exact prefixLift 1063212
  have htrace : WordTrace (prefixWord ++ tailWord_1063212) baseStart_1063212 baseEnd_1063212 := by
    simpa [prefixWord, tailWord_1063212, baseEnd_1063212] using wordTrace_append hprefix tailTrace_1063212
  have hstable : (prefixWord ++ tailWord_1063212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063212).length < 2 ^ (prefixWord ++ tailWord_1063212).sum := by decide
  have hdescent : baseEnd_1063212 < baseStart_1063212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063220 : List Nat := [2, 5, 1, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_1063220 : Nat := 118140960795 + 1063220 * 2 ^ 59
def prefixEnd_1063220 : Nat := 4983230072969 + 3 ^ 40 * 1063220 * 2
def baseEnd_1063220 : Nat := 545942901473435380560347

theorem tailTrace_1063220 : CollatzResearch.WordTrace tailWord_1063220 prefixEnd_1063220 545942901473435380560347 := by
  unfold tailWord_1063220
  simp only [CollatzResearch.WordTrace]
  refine ⟨19389409604071499182253557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25852546138761998909671409 19389409604071499182253557)
  ·
    refine ⟨1817757150381703048336271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19389409604071499182253557 1817757150381703048336271)
    ·
      refine ⟨2726635725572554572504407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1817757150381703048336271 2726635725572554572504407)
      ·
        refine ⟨4089953588358831858756611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2726635725572554572504407 4089953588358831858756611)
        ·
          refine ⟨6134930382538247788134917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4089953588358831858756611 6134930382538247788134917)
          ·
            refine ⟨1150299446725921460275297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6134930382538247788134917 1150299446725921460275297)
            ·
              refine ⟨862724585044441095206473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1150299446725921460275297 862724585044441095206473)
              ·
                refine ⟨647043438783330821404855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 862724585044441095206473 647043438783330821404855)
                ·
                  refine ⟨970565158174996232107283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 647043438783330821404855 970565158174996232107283)
                  ·
                    refine ⟨1455847737262494348160925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 970565158174996232107283 1455847737262494348160925)
                    ·
                      refine ⟨545942901473435380560347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1455847737262494348160925 545942901473435380560347)
                      ·
                        rfl

theorem cell23_1063220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_1063220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063220 prefixEnd_1063220 := by exact prefixLift 1063220
  have htrace : WordTrace (prefixWord ++ tailWord_1063220) baseStart_1063220 baseEnd_1063220 := by
    simpa [prefixWord, tailWord_1063220, baseEnd_1063220] using wordTrace_append hprefix tailTrace_1063220
  have hstable : (prefixWord ++ tailWord_1063220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063220).length < 2 ^ (prefixWord ++ tailWord_1063220).sum := by decide
  have hdescent : baseEnd_1063220 < baseStart_1063220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063242 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 8, 1, 3]
def baseStart_1063242 : Nat := 118140960795 + 1063242 * 2 ^ 59
def prefixEnd_1063242 : Nat := 4983230072969 + 3 ^ 40 * 1063242 * 2
def baseEnd_1063242 : Nat := 545954198047834294485245

theorem tailTrace_1063242 : CollatzResearch.WordTrace tailWord_1063242 prefixEnd_1063242 545954198047834294485245 := by
  unfold tailWord_1063242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9694905403515824030451995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25853081076042197414538653 9694905403515824030451995)
  ·
    refine ⟨14542358105273736045677993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9694905403515824030451995 14542358105273736045677993)
    ·
      refine ⟨10906768578955302034258495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14542358105273736045677993 10906768578955302034258495)
      ·
        refine ⟨16360152868432953051387743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10906768578955302034258495 16360152868432953051387743)
        ·
          refine ⟨24540229302649429577081615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16360152868432953051387743 24540229302649429577081615)
          ·
            refine ⟨36810343953974144365622423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24540229302649429577081615 36810343953974144365622423)
            ·
              refine ⟨55215515930961216548433635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36810343953974144365622423 55215515930961216548433635)
              ·
                refine ⟨82823273896441824822650453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55215515930961216548433635 82823273896441824822650453)
                ·
                  refine ⟨970585240973927634640435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 82823273896441824822650453 970585240973927634640435)
                  ·
                    refine ⟨1455877861460891451960653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 970585240973927634640435 1455877861460891451960653)
                    ·
                      refine ⟨545954198047834294485245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1455877861460891451960653 545954198047834294485245)
                      ·
                        rfl

theorem cell23_1063242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_1063242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063242 prefixEnd_1063242 := by exact prefixLift 1063242
  have htrace : WordTrace (prefixWord ++ tailWord_1063242) baseStart_1063242 baseEnd_1063242 := by
    simpa [prefixWord, tailWord_1063242, baseEnd_1063242] using wordTrace_append hprefix tailTrace_1063242
  have hstable : (prefixWord ++ tailWord_1063242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063242).length < 2 ^ (prefixWord ++ tailWord_1063242).sum := by decide
  have hdescent : baseEnd_1063242 < baseStart_1063242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063255 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_1063255 : Nat := 118140960795 + 1063255 * 2 ^ 59
def prefixEnd_1063255 : Nat := 4983230072969 + 3 ^ 40 * 1063255 * 2
def baseEnd_1063255 : Nat := 545960873296342743622685

theorem tailTrace_1063255 : CollatzResearch.WordTrace tailWord_1063255 prefixEnd_1063255 545960873296342743622685 := by
  unfold tailWord_1063255
  simp only [CollatzResearch.WordTrace]
  refine ⟨38780095763016199342031219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25853397175344132894687479 38780095763016199342031219)
  ·
    refine ⟨58170143644524299013046829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38780095763016199342031219 58170143644524299013046829)
    ·
      refine ⟨21813803866696612129892561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58170143644524299013046829 21813803866696612129892561)
      ·
        refine ⟨16360352900022459097419421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21813803866696612129892561 16360352900022459097419421)
        ·
          refine ⟨6135132337508422161532283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16360352900022459097419421 6135132337508422161532283)
          ·
            refine ⟨9202698506262633242298425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6135132337508422161532283 9202698506262633242298425)
            ·
              refine ⟨6902023879696974931723819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9202698506262633242298425 6902023879696974931723819)
              ·
                refine ⟨10353035819545462397585729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6902023879696974931723819 10353035819545462397585729)
                ·
                  refine ⟨7764776864659096798189297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10353035819545462397585729 7764776864659096798189297)
                  ·
                    refine ⟨5823582648494322598641973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7764776864659096798189297 5823582648494322598641973)
                    ·
                      refine ⟨545960873296342743622685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5823582648494322598641973 545960873296342743622685)
                      ·
                        rfl

theorem cell23_1063255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_1063255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063255 prefixEnd_1063255 := by exact prefixLift 1063255
  have htrace : WordTrace (prefixWord ++ tailWord_1063255) baseStart_1063255 baseEnd_1063255 := by
    simpa [prefixWord, tailWord_1063255, baseEnd_1063255] using wordTrace_append hprefix tailTrace_1063255
  have hstable : (prefixWord ++ tailWord_1063255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063255).length < 2 ^ (prefixWord ++ tailWord_1063255).sum := by decide
  have hdescent : baseEnd_1063255 < baseStart_1063255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063260 : List Nat := [2, 2, 4, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_1063260 : Nat := 118140960795 + 1063260 * 2 ^ 59
def prefixEnd_1063260 : Nat := 4983230072969 + 3 ^ 40 * 1063260 * 2
def baseEnd_1063260 : Nat := 545963440699615224060163

theorem tailTrace_1063260 : CollatzResearch.WordTrace tailWord_1063260 prefixEnd_1063260 545963440699615224060163 := by
  unfold tailWord_1063260
  simp only [CollatzResearch.WordTrace]
  refine ⟨19390139063999042597981617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25853518751998723463975489 19390139063999042597981617)
  ·
    refine ⟨14542604297999281948486213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19390139063999042597981617 14542604297999281948486213)
    ·
      refine ⟨2726738305874865365341165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14542604297999281948486213 2726738305874865365341165)
      ·
        refine ⟨1022526864703074512002937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2726738305874865365341165 1022526864703074512002937)
        ·
          refine ⟨766895148527305884002203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1022526864703074512002937 766895148527305884002203)
          ·
            refine ⟨1150342722790958826003305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766895148527305884002203 1150342722790958826003305)
            ·
              refine ⟨862757042093219119502479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1150342722790958826003305 862757042093219119502479)
              ·
                refine ⟨1294135563139828679253719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862757042093219119502479 1294135563139828679253719)
                ·
                  refine ⟨1941203344709743018880579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294135563139828679253719 1941203344709743018880579)
                  ·
                    refine ⟨2911805017064614528320869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1941203344709743018880579 2911805017064614528320869)
                    ·
                      refine ⟨545963440699615224060163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2911805017064614528320869 545963440699615224060163)
                      ·
                        rfl

theorem cell23_1063260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_1063260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063260 prefixEnd_1063260 := by exact prefixLift 1063260
  have htrace : WordTrace (prefixWord ++ tailWord_1063260) baseStart_1063260 baseEnd_1063260 := by
    simpa [prefixWord, tailWord_1063260, baseEnd_1063260] using wordTrace_append hprefix tailTrace_1063260
  have hstable : (prefixWord ++ tailWord_1063260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063260).length < 2 ^ (prefixWord ++ tailWord_1063260).sum := by decide
  have hdescent : baseEnd_1063260 < baseStart_1063260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063332 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_1063332 : Nat := 118140960795 + 1063332 * 2 ^ 59
def prefixEnd_1063332 : Nat := 4983230072969 + 3 ^ 40 * 1063332 * 2
def baseEnd_1063332 : Nat := 546000411306738942359831

theorem tailTrace_1063332 : CollatzResearch.WordTrace tailWord_1063332 prefixEnd_1063332 546000411306738942359831 := by
  unfold tailWord_1063332
  simp only [CollatzResearch.WordTrace]
  refine ⟨19391452091868620746292125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25855269455824827661722833 19391452091868620746292125)
  ·
    refine ⟨7271794534450732779859547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19391452091868620746292125 7271794534450732779859547)
    ·
      refine ⟨10907691801676099169789321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7271794534450732779859547 10907691801676099169789321)
      ·
        refine ⟨8180768851257074377341991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10907691801676099169789321 8180768851257074377341991)
        ·
          refine ⟨12271153276885611566012987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8180768851257074377341991 12271153276885611566012987)
          ·
            refine ⟨18406729915328417349019481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12271153276885611566012987 18406729915328417349019481)
            ·
              refine ⟨13805047436496313011764611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18406729915328417349019481 13805047436496313011764611)
              ·
                refine ⟨20707571154744469517646917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13805047436496313011764611 20707571154744469517646917)
                ·
                  refine ⟨3882669591514588034558797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20707571154744469517646917 3882669591514588034558797)
                  ·
                    refine ⟨1456001096817970512959549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3882669591514588034558797 1456001096817970512959549)
                    ·
                      refine ⟨546000411306738942359831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1456001096817970512959549 546000411306738942359831)
                      ·
                        rfl

theorem cell23_1063332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_1063332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063332 prefixEnd_1063332 := by exact prefixLift 1063332
  have htrace : WordTrace (prefixWord ++ tailWord_1063332) baseStart_1063332 baseEnd_1063332 := by
    simpa [prefixWord, tailWord_1063332, baseEnd_1063332] using wordTrace_append hprefix tailTrace_1063332
  have hstable : (prefixWord ++ tailWord_1063332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063332).length < 2 ^ (prefixWord ++ tailWord_1063332).sum := by decide
  have hdescent : baseEnd_1063332 < baseStart_1063332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063389 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_1063389 : Nat := 118140960795 + 1063389 * 2 ^ 59
def prefixEnd_1063389 : Nat := 4983230072969 + 3 ^ 40 * 1063389 * 2
def baseEnd_1063389 : Nat := 546029679704045219347069

theorem tailTrace_1063389 : CollatzResearch.WordTrace tailWord_1063389 prefixEnd_1063389 546029679704045219347069 := by
  unfold tailWord_1063389
  simp only [CollatzResearch.WordTrace]
  refine ⟨38784983144530740227409221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25856655429687160151606147 38784983144530740227409221)
  ·
    refine ⟨7272184339599513792639229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38784983144530740227409221 7272184339599513792639229)
    ·
      refine ⟨2727069127349817672239711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7272184339599513792639229 2727069127349817672239711)
      ·
        refine ⟨4090603691024726508359567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2727069127349817672239711 4090603691024726508359567)
        ·
          refine ⟨6135905536537089762539351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4090603691024726508359567 6135905536537089762539351)
          ·
            refine ⟨9203858304805634643809027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6135905536537089762539351 9203858304805634643809027)
            ·
              refine ⟨13805787457208451965713541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9203858304805634643809027 13805787457208451965713541)
              ·
                refine ⟨2588585148226584743571289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13805787457208451965713541 2588585148226584743571289)
                ·
                  refine ⟨1941438861169938557678467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2588585148226584743571289 1941438861169938557678467)
                  ·
                    refine ⟨2912158291754907836517701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1941438861169938557678467 2912158291754907836517701)
                    ·
                      refine ⟨546029679704045219347069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2912158291754907836517701 546029679704045219347069)
                      ·
                        rfl

theorem cell23_1063389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_1063389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063389 prefixEnd_1063389 := by exact prefixLift 1063389
  have htrace : WordTrace (prefixWord ++ tailWord_1063389) baseStart_1063389 baseEnd_1063389 := by
    simpa [prefixWord, tailWord_1063389, baseEnd_1063389] using wordTrace_append hprefix tailTrace_1063389
  have hstable : (prefixWord ++ tailWord_1063389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063389).length < 2 ^ (prefixWord ++ tailWord_1063389).sum := by decide
  have hdescent : baseEnd_1063389 < baseStart_1063389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063399 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 3, 4]
def baseStart_1063399 : Nat := 118140960795 + 1063399 * 2 ^ 59
def prefixEnd_1063399 : Nat := 4983230072969 + 3 ^ 40 * 1063399 * 2
def baseEnd_1063399 : Nat := 182011604836863393407341

theorem tailTrace_1063399 : CollatzResearch.WordTrace tailWord_1063399 prefixEnd_1063399 182011604836863393407341 := by
  unfold tailWord_1063399
  simp only [CollatzResearch.WordTrace]
  refine ⟨38785347874494511935273251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25856898582996341290182167 38785347874494511935273251)
  ·
    refine ⟨58178021811741767902909877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38785347874494511935273251 58178021811741767902909877)
    ·
      refine ⟨5454189544850790740897801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58178021811741767902909877 5454189544850790740897801)
      ·
        refine ⟨4090642158638093055673351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5454189544850790740897801 4090642158638093055673351)
        ·
          refine ⟨6135963237957139583510027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4090642158638093055673351 6135963237957139583510027)
          ·
            refine ⟨9203944856935709375265041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6135963237957139583510027 9203944856935709375265041)
            ·
              refine ⟨6902958642701782031448781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9203944856935709375265041 6902958642701782031448781)
              ·
                refine ⟨2588609491013168261793293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6902958642701782031448781 2588609491013168261793293)
                ·
                  refine ⟨970728559129938098172485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2588609491013168261793293 970728559129938098172485)
                  ·
                    refine ⟨182011604836863393407341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 970728559129938098172485 182011604836863393407341)
                    ·
                      rfl

theorem cell23_1063399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_1063399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063399 prefixEnd_1063399 := by exact prefixLift 1063399
  have htrace : WordTrace (prefixWord ++ tailWord_1063399) baseStart_1063399 baseEnd_1063399 := by
    simpa [prefixWord, tailWord_1063399, baseEnd_1063399] using wordTrace_append hprefix tailTrace_1063399
  have hstable : (prefixWord ++ tailWord_1063399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063399).length < 2 ^ (prefixWord ++ tailWord_1063399).sum := by decide
  have hdescent : baseEnd_1063399 < baseStart_1063399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063406 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_1063406 : Nat := 118140960795 + 1063406 * 2 ^ 59
def prefixEnd_1063406 : Nat := 4983230072969 + 3 ^ 40 * 1063406 * 2
def baseEnd_1063406 : Nat := 546038408875171652834491

theorem tailTrace_1063406 : CollatzResearch.WordTrace tailWord_1063406 prefixEnd_1063406 546038408875171652834491 := by
  unfold tailWord_1063406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4848200398183644016347259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25857068790312768087185381 4848200398183644016347259)
  ·
    refine ⟨7272300597275466024520889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4848200398183644016347259 7272300597275466024520889)
    ·
      refine ⟨5454225447956599518390667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7272300597275466024520889 5454225447956599518390667)
      ·
        refine ⟨8181338171934899277586001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5454225447956599518390667 8181338171934899277586001)
        ·
          refine ⟨6136003628951174458189501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8181338171934899277586001 6136003628951174458189501)
          ·
            refine ⟨2301001360856690421821063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6136003628951174458189501 2301001360856690421821063)
            ·
              refine ⟨3451502041285035632731595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2301001360856690421821063 3451502041285035632731595)
              ·
                refine ⟨5177253061927553449097393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3451502041285035632731595 5177253061927553449097393)
                ·
                  refine ⟨3882939796445665086823045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5177253061927553449097393 3882939796445665086823045)
                  ·
                    refine ⟨728051211833562203779321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3882939796445665086823045 728051211833562203779321)
                    ·
                      refine ⟨546038408875171652834491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728051211833562203779321 546038408875171652834491)
                      ·
                        rfl

theorem cell23_1063406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_1063406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063406 prefixEnd_1063406 := by exact prefixLift 1063406
  have htrace : WordTrace (prefixWord ++ tailWord_1063406) baseStart_1063406 baseEnd_1063406 := by
    simpa [prefixWord, tailWord_1063406, baseEnd_1063406] using wordTrace_append hprefix tailTrace_1063406
  have hstable : (prefixWord ++ tailWord_1063406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063406).length < 2 ^ (prefixWord ++ tailWord_1063406).sum := by decide
  have hdescent : baseEnd_1063406 < baseStart_1063406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063466 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_1063466 : Nat := 118140960795 + 1063466 * 2 ^ 59
def prefixEnd_1063466 : Nat := 4983230072969 + 3 ^ 40 * 1063466 * 2
def baseEnd_1063466 : Nat := 546069217714441418084215

theorem tailTrace_1063466 : CollatzResearch.WordTrace tailWord_1063466 prefixEnd_1063466 546069217714441418084215 := by
  unfold tailWord_1063466
  simp only [CollatzResearch.WordTrace]
  refine ⟨9696947891312945594490563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25858527710167854918641501 9696947891312945594490563)
  ·
    refine ⟨14545421836969418391735845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9696947891312945594490563 14545421836969418391735845)
    ·
      refine ⟨2727266594431765948450471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14545421836969418391735845 2727266594431765948450471)
      ·
        refine ⟨4090899891647648922675707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2727266594431765948450471 4090899891647648922675707)
        ·
          refine ⟨6136349837471473384013561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4090899891647648922675707 6136349837471473384013561)
          ·
            refine ⟨4602262378103605038010171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6136349837471473384013561 4602262378103605038010171)
            ·
              refine ⟨6903393567155407557015257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4602262378103605038010171 6903393567155407557015257)
              ·
                refine ⟨5177545175366555667761443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6903393567155407557015257 5177545175366555667761443)
                ·
                  refine ⟨7766317763049833501642165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5177545175366555667761443 7766317763049833501642165)
                  ·
                    refine ⟨728092290285921890778953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7766317763049833501642165 728092290285921890778953)
                    ·
                      refine ⟨546069217714441418084215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728092290285921890778953 546069217714441418084215)
                      ·
                        rfl

theorem cell23_1063466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_1063466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063466 prefixEnd_1063466 := by exact prefixLift 1063466
  have htrace : WordTrace (prefixWord ++ tailWord_1063466) baseStart_1063466 baseEnd_1063466 := by
    simpa [prefixWord, tailWord_1063466, baseEnd_1063466] using wordTrace_append hprefix tailTrace_1063466
  have hstable : (prefixWord ++ tailWord_1063466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063466).length < 2 ^ (prefixWord ++ tailWord_1063466).sum := by decide
  have hdescent : baseEnd_1063466 < baseStart_1063466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063479 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 2, 6, 2]
def baseStart_1063479 : Nat := 118140960795 + 1063479 * 2 ^ 59
def prefixEnd_1063479 : Nat := 4983230072969 + 3 ^ 40 * 1063479 * 2
def baseEnd_1063479 : Nat := 546075892962949867221655

theorem tailTrace_1063479 : CollatzResearch.WordTrace tailWord_1063479 prefixEnd_1063479 546075892962949867221655 := by
  unfold tailWord_1063479
  simp only [CollatzResearch.WordTrace]
  refine ⟨38788265714204685598185491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25858843809469790398790327 38788265714204685598185491)
  ·
    refine ⟨58182398571307028397278237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38788265714204685598185491 58182398571307028397278237)
    ·
      refine ⟨21818399464240135648979339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58182398571307028397278237 21818399464240135648979339)
      ·
        refine ⟨32727599196360203473469009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21818399464240135648979339 32727599196360203473469009)
        ·
          refine ⟨24545699397270152605101757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32727599196360203473469009 24545699397270152605101757)
          ·
            refine ⟨9204637273976307226913159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24545699397270152605101757 9204637273976307226913159)
            ·
              refine ⟨13806955910964460840369739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9204637273976307226913159 13806955910964460840369739)
              ·
                refine ⟨20710433866446691260554609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13806955910964460840369739 20710433866446691260554609)
                ·
                  refine ⟨15532825399835018445415957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20710433866446691260554609 15532825399835018445415957)
                  ·
                    refine ⟨728101190617266489628873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15532825399835018445415957 728101190617266489628873)
                    ·
                      refine ⟨546075892962949867221655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728101190617266489628873 546075892962949867221655)
                      ·
                        rfl

theorem cell23_1063479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 6, 2].length) (baseStart_1063479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063479 prefixEnd_1063479 := by exact prefixLift 1063479
  have htrace : WordTrace (prefixWord ++ tailWord_1063479) baseStart_1063479 baseEnd_1063479 := by
    simpa [prefixWord, tailWord_1063479, baseEnd_1063479] using wordTrace_append hprefix tailTrace_1063479
  have hstable : (prefixWord ++ tailWord_1063479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063479).length < 2 ^ (prefixWord ++ tailWord_1063479).sum := by decide
  have hdescent : baseEnd_1063479 < baseStart_1063479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063496 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 5, 2, 2]
def baseStart_1063496 : Nat := 118140960795 + 1063496 * 2 ^ 59
def prefixEnd_1063496 : Nat := 4983230072969 + 3 ^ 40 * 1063496 * 2
def baseEnd_1063496 : Nat := 546084622134076300709077

theorem tailTrace_1063496 : CollatzResearch.WordTrace tailWord_1063496 prefixEnd_1063496 546084622134076300709077 := by
  unfold tailWord_1063496
  simp only [CollatzResearch.WordTrace]
  refine ⟨19394442877571548750777171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25859257170095398334369561 19394442877571548750777171)
  ·
    refine ⟨29091664316357323126165757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19394442877571548750777171 29091664316357323126165757)
    ·
      refine ⟨10909374118633996172312159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29091664316357323126165757 10909374118633996172312159)
      ·
        refine ⟨16364061177950994258468239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10909374118633996172312159 16364061177950994258468239)
        ·
          refine ⟨24546091766926491387702359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16364061177950994258468239 24546091766926491387702359)
          ·
            refine ⟨36819137650389737081553539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24546091766926491387702359 36819137650389737081553539)
            ·
              refine ⟨55228706475584605622330309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36819137650389737081553539 55228706475584605622330309)
              ·
                refine ⟨10355382464172113554186933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55228706475584605622330309 10355382464172113554186933)
                ·
                  refine ⟨970817106016135645705025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10355382464172113554186933 970817106016135645705025)
                  ·
                    refine ⟨728112829512101734278769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 970817106016135645705025 728112829512101734278769)
                    ·
                      refine ⟨546084622134076300709077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728112829512101734278769 546084622134076300709077)
                      ·
                        rfl

theorem cell23_1063496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_1063496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063496 prefixEnd_1063496 := by exact prefixLift 1063496
  have htrace : WordTrace (prefixWord ++ tailWord_1063496) baseStart_1063496 baseEnd_1063496 := by
    simpa [prefixWord, tailWord_1063496, baseEnd_1063496] using wordTrace_append hprefix tailTrace_1063496
  have hstable : (prefixWord ++ tailWord_1063496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063496).length < 2 ^ (prefixWord ++ tailWord_1063496).sum := by decide
  have hdescent : baseEnd_1063496 < baseStart_1063496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063502 : List Nat := [4, 1, 1, 1, 1, 2, 13]
def baseStart_1063502 : Nat := 118140960795 + 1063502 * 2 ^ 59
def prefixEnd_1063502 : Nat := 4983230072969 + 3 ^ 40 * 1063502 * 2
def baseEnd_1063502 : Nat := 6741823494049423175729

theorem tailTrace_1063502 : CollatzResearch.WordTrace tailWord_1063502 prefixEnd_1063502 6741823494049423175729 := by
  unfold tailWord_1063502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4848638074140170065784095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25859403062080907017515173 4848638074140170065784095)
  ·
    refine ⟨7272957111210255098676143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4848638074140170065784095 7272957111210255098676143)
    ·
      refine ⟨10909435666815382648014215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7272957111210255098676143 10909435666815382648014215)
      ·
        refine ⟨16364153500223073972021323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10909435666815382648014215 16364153500223073972021323)
        ·
          refine ⟨24546230250334610958031985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16364153500223073972021323 24546230250334610958031985)
          ·
            refine ⟨18409672687750958218523989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24546230250334610958031985 18409672687750958218523989)
            ·
              refine ⟨6741823494049423175729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 18409672687750958218523989 6741823494049423175729)
              ·
                rfl

theorem cell23_1063502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 13].length) (baseStart_1063502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063502 prefixEnd_1063502 := by exact prefixLift 1063502
  have htrace : WordTrace (prefixWord ++ tailWord_1063502) baseStart_1063502 baseEnd_1063502 := by
    simpa [prefixWord, tailWord_1063502, baseEnd_1063502] using wordTrace_append hprefix tailTrace_1063502
  have hstable : (prefixWord ++ tailWord_1063502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063502).length < 2 ^ (prefixWord ++ tailWord_1063502).sum := by decide
  have hdescent : baseEnd_1063502 < baseStart_1063502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063506 : List Nat := [3, 2, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_1063506 : Nat := 118140960795 + 1063506 * 2 ^ 59
def prefixEnd_1063506 : Nat := 4983230072969 + 3 ^ 40 * 1063506 * 2
def baseEnd_1063506 : Nat := 182029918980207087194677

theorem tailTrace_1063506 : CollatzResearch.WordTrace tailWord_1063506 prefixEnd_1063506 182029918980207087194677 := by
  unfold tailWord_1063506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9697312621276717302354593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25859500323404579472945581 9697312621276717302354593)
  ·
    refine ⟨7272984465957537976765945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9697312621276717302354593 7272984465957537976765945)
    ·
      refine ⟨5454738349468153482574459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7272984465957537976765945 5454738349468153482574459)
      ·
        refine ⟨8182107524202230223861689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5454738349468153482574459 8182107524202230223861689)
        ·
          refine ⟨6136580643151672667896267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8182107524202230223861689 6136580643151672667896267)
          ·
            refine ⟨9204870964727509001844401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6136580643151672667896267 9204870964727509001844401)
            ·
              refine ⟨6903653223545631751383301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9204870964727509001844401 6903653223545631751383301)
              ·
                refine ⟨1294434979414805953384369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6903653223545631751383301 1294434979414805953384369)
                ·
                  refine ⟨970826234561104465038277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1294434979414805953384369 970826234561104465038277)
                  ·
                    refine ⟨182029918980207087194677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 970826234561104465038277 182029918980207087194677)
                    ·
                      rfl

theorem cell23_1063506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_1063506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063506 prefixEnd_1063506 := by exact prefixLift 1063506
  have htrace : WordTrace (prefixWord ++ tailWord_1063506) baseStart_1063506 baseEnd_1063506 := by
    simpa [prefixWord, tailWord_1063506, baseEnd_1063506] using wordTrace_append hprefix tailTrace_1063506
  have hstable : (prefixWord ++ tailWord_1063506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063506).length < 2 ^ (prefixWord ++ tailWord_1063506).sum := by decide
  have hdescent : baseEnd_1063506 < baseStart_1063506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063529 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 1, 3, 3]
def baseStart_1063529 : Nat := 118140960795 + 1063529 * 2 ^ 59
def prefixEnd_1063529 : Nat := 4983230072969 + 3 ^ 40 * 1063529 * 2
def baseEnd_1063529 : Nat := 546101566995674671596425

theorem tailTrace_1063529 : CollatzResearch.WordTrace tailWord_1063529 prefixEnd_1063529 546101566995674671596425 := by
  unfold tailWord_1063529
  simp only [CollatzResearch.WordTrace]
  refine ⟨38790089364023544137505641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25860059576015696091670427 38790089364023544137505641)
  ·
    refine ⟨29092567023017658103129231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38790089364023544137505641 29092567023017658103129231)
    ·
      refine ⟨43638850534526487154693847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29092567023017658103129231 43638850534526487154693847)
      ·
        refine ⟨65458275801789730732040771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43638850534526487154693847 65458275801789730732040771)
        ·
          refine ⟨98187413702684596098061157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65458275801789730732040771 98187413702684596098061157)
          ·
            refine ⟨18410140069253361768386467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98187413702684596098061157 18410140069253361768386467)
            ·
              refine ⟨27615210103880042652579701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18410140069253361768386467 27615210103880042652579701)
              ·
                refine ⟨2588925947238753998679347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27615210103880042652579701 2588925947238753998679347)
                ·
                  refine ⟨3883388920858130998019021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2588925947238753998679347 3883388920858130998019021)
                  ·
                    refine ⟨1456270845321799124257133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3883388920858130998019021 1456270845321799124257133)
                    ·
                      refine ⟨546101566995674671596425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1456270845321799124257133 546101566995674671596425)
                      ·
                        rfl

theorem cell23_1063529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 3, 3].length) (baseStart_1063529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063529 prefixEnd_1063529 := by exact prefixLift 1063529
  have htrace : WordTrace (prefixWord ++ tailWord_1063529) baseStart_1063529 baseEnd_1063529 := by
    simpa [prefixWord, tailWord_1063529, baseEnd_1063529] using wordTrace_append hprefix tailTrace_1063529
  have hstable : (prefixWord ++ tailWord_1063529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063529).length < 2 ^ (prefixWord ++ tailWord_1063529).sum := by decide
  have hdescent : baseEnd_1063529 < baseStart_1063529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063533 : List Nat := [1, 5, 1, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_1063533 : Nat := 118140960795 + 1063533 * 2 ^ 59
def prefixEnd_1063533 : Nat := 4983230072969 + 3 ^ 40 * 1063533 * 2
def baseEnd_1063533 : Nat := 546103620918292655946407

theorem tailTrace_1063533 : CollatzResearch.WordTrace tailWord_1063533 prefixEnd_1063533 546103620918292655946407 := by
  unfold tailWord_1063533
  simp only [CollatzResearch.WordTrace]
  refine ⟨38790235256009052820651253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25860156837339368547100835 38790235256009052820651253)
  ·
    refine ⟨3636584555250848701936055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38790235256009052820651253 3636584555250848701936055)
    ·
      refine ⟨5454876832876273052904083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3636584555250848701936055 5454876832876273052904083)
      ·
        refine ⟨8182315249314409579356125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5454876832876273052904083 8182315249314409579356125)
        ·
          refine ⟨3068368218492903592258547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8182315249314409579356125 3068368218492903592258547)
          ·
            refine ⟨4602552327739355388387821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3068368218492903592258547 4602552327739355388387821)
            ·
              refine ⟨1725957122902258270645433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4602552327739355388387821 1725957122902258270645433)
              ·
                refine ⟨1294467842176693702984075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1725957122902258270645433 1294467842176693702984075)
                ·
                  refine ⟨1941701763265040554476113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294467842176693702984075 1941701763265040554476113)
                  ·
                    refine ⟨1456276322448780415857085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1941701763265040554476113 1456276322448780415857085)
                    ·
                      refine ⟨546103620918292655946407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1456276322448780415857085 546103620918292655946407)
                      ·
                        rfl

theorem cell23_1063533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_1063533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063533 prefixEnd_1063533 := by exact prefixLift 1063533
  have htrace : WordTrace (prefixWord ++ tailWord_1063533) baseStart_1063533 baseEnd_1063533 := by
    simpa [prefixWord, tailWord_1063533, baseEnd_1063533] using wordTrace_append hprefix tailTrace_1063533
  have hstable : (prefixWord ++ tailWord_1063533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063533).length < 2 ^ (prefixWord ++ tailWord_1063533).sum := by decide
  have hdescent : baseEnd_1063533 < baseStart_1063533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063589 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 4, 4, 3]
def baseStart_1063589 : Nat := 118140960795 + 1063589 * 2 ^ 59
def prefixEnd_1063589 : Nat := 4983230072969 + 3 ^ 40 * 1063589 * 2
def baseEnd_1063589 : Nat := 546132375834944436846149

theorem tailTrace_1063589 : CollatzResearch.WordTrace tailWord_1063589 prefixEnd_1063589 546132375834944436846149 := by
  unfold tailWord_1063589
  simp only [CollatzResearch.WordTrace]
  refine ⟨38792277743806174384689821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25861518495870782923126547 38792277743806174384689821)
  ·
    refine ⟨14547104153927315394258683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38792277743806174384689821 14547104153927315394258683)
    ·
      refine ⟨21820656230890973091388025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14547104153927315394258683 21820656230890973091388025)
      ·
        refine ⟨16365492173168229818541019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21820656230890973091388025 16365492173168229818541019)
        ·
          refine ⟨24548238259752344727811529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16365492173168229818541019 24548238259752344727811529)
          ·
            refine ⟨18411178694814258545858647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24548238259752344727811529 18411178694814258545858647)
            ·
              refine ⟨27616768042221387818787971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18411178694814258545858647 27616768042221387818787971)
              ·
                refine ⟨41425152063332081728181957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27616768042221387818787971 41425152063332081728181957)
                ·
                  refine ⟨7767216011874765324034117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41425152063332081728181957 7767216011874765324034117)
                  ·
                    refine ⟨1456353002226518498256397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7767216011874765324034117 1456353002226518498256397)
                    ·
                      refine ⟨546132375834944436846149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1456353002226518498256397 546132375834944436846149)
                      ·
                        rfl

theorem cell23_1063589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_1063589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063589 prefixEnd_1063589 := by exact prefixLift 1063589
  have htrace : WordTrace (prefixWord ++ tailWord_1063589) baseStart_1063589 baseEnd_1063589 := by
    simpa [prefixWord, tailWord_1063589, baseEnd_1063589] using wordTrace_append hprefix tailTrace_1063589
  have hstable : (prefixWord ++ tailWord_1063589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063589).length < 2 ^ (prefixWord ++ tailWord_1063589).sum := by decide
  have hdescent : baseEnd_1063589 < baseStart_1063589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063607 : List Nat := [1, 1, 3, 1, 6, 2, 2, 1, 1, 3, 2]
def baseStart_1063607 : Nat := 118140960795 + 1063607 * 2 ^ 59
def prefixEnd_1063607 : Nat := 4983230072969 + 3 ^ 40 * 1063607 * 2
def baseEnd_1063607 : Nat := 546141618486725366421067

theorem tailTrace_1063607 : CollatzResearch.WordTrace tailWord_1063607 prefixEnd_1063607 546141618486725366421067 := by
  unfold tailWord_1063607
  simp only [CollatzResearch.WordTrace]
  refine ⟨38792934257740963458845075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25861956171827308972563383 38792934257740963458845075)
  ·
    refine ⟨58189401386611445188267613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38792934257740963458845075 58189401386611445188267613)
    ·
      refine ⟨21821025519979291945600355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58189401386611445188267613 21821025519979291945600355)
      ·
        refine ⟨32731538279968937918400533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21821025519979291945600355 32731538279968937918400533)
        ·
          refine ⟨1534290856873543964925025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32731538279968937918400533 1534290856873543964925025)
          ·
            refine ⟨1150718142655157973693769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1534290856873543964925025 1150718142655157973693769)
            ·
              refine ⟨863038606991368480270327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1150718142655157973693769 863038606991368480270327)
              ·
                refine ⟨1294557910487052720405491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863038606991368480270327 1294557910487052720405491)
                ·
                  refine ⟨1941836865730579080608237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294557910487052720405491 1941836865730579080608237)
                  ·
                    refine ⟨728188824648967155228089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1941836865730579080608237 728188824648967155228089)
                    ·
                      refine ⟨546141618486725366421067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728188824648967155228089 546141618486725366421067)
                      ·
                        rfl

theorem cell23_1063607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 1, 3, 2].length) (baseStart_1063607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063607 prefixEnd_1063607 := by exact prefixLift 1063607
  have htrace : WordTrace (prefixWord ++ tailWord_1063607) baseStart_1063607 baseEnd_1063607 := by
    simpa [prefixWord, tailWord_1063607, baseEnd_1063607] using wordTrace_append hprefix tailTrace_1063607
  have hstable : (prefixWord ++ tailWord_1063607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063607).length < 2 ^ (prefixWord ++ tailWord_1063607).sum := by decide
  have hdescent : baseEnd_1063607 < baseStart_1063607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063620 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_1063620 : Nat := 118140960795 + 1063620 * 2 ^ 59
def prefixEnd_1063620 : Nat := 4983230072969 + 3 ^ 40 * 1063620 * 2
def baseEnd_1063620 : Nat := 546148293735233815558507

theorem tailTrace_1063620 : CollatzResearch.WordTrace tailWord_1063620 prefixEnd_1063620 546148293735233815558507 := by
  unfold tailWord_1063620
  simp only [CollatzResearch.WordTrace]
  refine ⟨19396704203346933339534157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25862272271129244452712209 19396704203346933339534157)
  ·
    refine ⟨7273764076255100002325309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19396704203346933339534157 7273764076255100002325309)
    ·
      refine ⟨2727661528595662500871991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7273764076255100002325309 2727661528595662500871991)
      ·
        refine ⟨4091492292893493751307987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2727661528595662500871991 4091492292893493751307987)
        ·
          refine ⟨6137238439340240626961981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4091492292893493751307987 6137238439340240626961981)
          ·
            refine ⟨2301464414752590235110743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6137238439340240626961981 2301464414752590235110743)
            ·
              refine ⟨3452196622128885352666115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2301464414752590235110743 3452196622128885352666115)
              ·
                refine ⟨5178294933193328028999173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3452196622128885352666115 5178294933193328028999173)
                ·
                  refine ⟨970930299973749005437345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5178294933193328028999173 970930299973749005437345)
                  ·
                    refine ⟨728197724980311754078009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 970930299973749005437345 728197724980311754078009)
                    ·
                      refine ⟨546148293735233815558507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728197724980311754078009 546148293735233815558507)
                      ·
                        rfl

theorem cell23_1063620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_1063620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063620 prefixEnd_1063620 := by exact prefixLift 1063620
  have htrace : WordTrace (prefixWord ++ tailWord_1063620) baseStart_1063620 baseEnd_1063620 := by
    simpa [prefixWord, tailWord_1063620, baseEnd_1063620] using wordTrace_append hprefix tailTrace_1063620
  have hstable : (prefixWord ++ tailWord_1063620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063620).length < 2 ^ (prefixWord ++ tailWord_1063620).sum := by decide
  have hdescent : baseEnd_1063620 < baseStart_1063620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063626 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 7]
def baseStart_1063626 : Nat := 118140960795 + 1063626 * 2 ^ 59
def prefixEnd_1063626 : Nat := 4983230072969 + 3 ^ 40 * 1063626 * 2
def baseEnd_1063626 : Nat := 60683486068795643564831

theorem tailTrace_1063626 : CollatzResearch.WordTrace tailWord_1063626 prefixEnd_1063626 60683486068795643564831 := by
  unfold tailWord_1063626
  simp only [CollatzResearch.WordTrace]
  refine ⟨9698406811168032425946683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25862418163114753135857821 9698406811168032425946683)
  ·
    refine ⟨14547610216752048638920025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9698406811168032425946683 14547610216752048638920025)
    ·
      refine ⟨10910707662564036479190019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14547610216752048638920025 10910707662564036479190019)
      ·
        refine ⟨16366061493846054718785029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10910707662564036479190019 16366061493846054718785029)
        ·
          refine ⟨3068636530096135259772193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16366061493846054718785029 3068636530096135259772193)
          ·
            refine ⟨2301477397572101444829145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3068636530096135259772193 2301477397572101444829145)
            ·
              refine ⟨1726108048179076083621859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2301477397572101444829145 1726108048179076083621859)
              ·
                refine ⟨2589162072268614125432789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726108048179076083621859 2589162072268614125432789)
                ·
                  refine ⟨60683486068795643564831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2589162072268614125432789 60683486068795643564831)
                  ·
                    rfl

theorem cell23_1063626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 7].length) (baseStart_1063626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063626 prefixEnd_1063626 := by exact prefixLift 1063626
  have htrace : WordTrace (prefixWord ++ tailWord_1063626) baseStart_1063626 baseEnd_1063626 := by
    simpa [prefixWord, tailWord_1063626, baseEnd_1063626] using wordTrace_append hprefix tailTrace_1063626
  have hstable : (prefixWord ++ tailWord_1063626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063626).length < 2 ^ (prefixWord ++ tailWord_1063626).sum := by decide
  have hdescent : baseEnd_1063626 < baseStart_1063626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063637 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1063637 : Nat := 118140960795 + 1063637 * 2 ^ 59
def prefixEnd_1063637 : Nat := 4983230072969 + 3 ^ 40 * 1063637 * 2
def baseEnd_1063637 : Nat := 546157022906360249045929

theorem tailTrace_1063637 : CollatzResearch.WordTrace tailWord_1063637 prefixEnd_1063637 546157022906360249045929 := by
  unfold tailWord_1063637
  simp only [CollatzResearch.WordTrace]
  refine ⟨38794028447632278582437165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25862685631754852388291443 38794028447632278582437165)
  ·
    refine ⟨14547760667862104468413937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38794028447632278582437165 14547760667862104468413937)
    ·
      refine ⟨10910820500896578351310453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14547760667862104468413937 10910820500896578351310453)
      ·
        refine ⟨1022889421959054220435355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10910820500896578351310453 1022889421959054220435355)
        ·
          refine ⟨1534334132938581330653033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022889421959054220435355 1534334132938581330653033)
          ·
            refine ⟨1150750599703935997989775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1534334132938581330653033 1150750599703935997989775)
            ·
              refine ⟨1726125899555903996984663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1150750599703935997989775 1726125899555903996984663)
              ·
                refine ⟨2589188849333855995476995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726125899555903996984663 2589188849333855995476995)
                ·
                  refine ⟨3883783274000783993215493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589188849333855995476995 3883783274000783993215493)
                  ·
                    refine ⟨728209363875146998727905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3883783274000783993215493 728209363875146998727905)
                    ·
                      refine ⟨546157022906360249045929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728209363875146998727905 546157022906360249045929)
                      ·
                        rfl

theorem cell23_1063637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1063637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063637 prefixEnd_1063637 := by exact prefixLift 1063637
  have htrace : WordTrace (prefixWord ++ tailWord_1063637) baseStart_1063637 baseEnd_1063637 := by
    simpa [prefixWord, tailWord_1063637, baseEnd_1063637] using wordTrace_append hprefix tailTrace_1063637
  have hstable : (prefixWord ++ tailWord_1063637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063637).length < 2 ^ (prefixWord ++ tailWord_1063637).sum := by decide
  have hdescent : baseEnd_1063637 < baseStart_1063637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063639 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 1, 7]
def baseStart_1063639 : Nat := 118140960795 + 1063639 * 2 ^ 59
def prefixEnd_1063639 : Nat := 4983230072969 + 3 ^ 40 * 1063639 * 2
def baseEnd_1063639 : Nat := 182052683289223080406973

theorem tailTrace_1063639 : CollatzResearch.WordTrace tailWord_1063639 prefixEnd_1063639 182052683289223080406973 := by
  unfold tailWord_1063639
  simp only [CollatzResearch.WordTrace]
  refine ⟨38794101393625032924009971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25862734262416688616006647 38794101393625032924009971)
  ·
    refine ⟨58191152090437549386014957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38794101393625032924009971 58191152090437549386014957)
    ·
      refine ⟨21821682033914081019755609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58191152090437549386014957 21821682033914081019755609)
      ·
        refine ⟨16366261525435560764816707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21821682033914081019755609 16366261525435560764816707)
        ·
          refine ⟨24549392288153341147225061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16366261525435560764816707 24549392288153341147225061)
          ·
            refine ⟨4603011054028751465104699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24549392288153341147225061 4603011054028751465104699)
            ·
              refine ⟨6904516581043127197657049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4603011054028751465104699 6904516581043127197657049)
              ·
                refine ⟨5178387435782345398242787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6904516581043127197657049 5178387435782345398242787)
                ·
                  refine ⟨7767581153673518097364181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5178387435782345398242787 7767581153673518097364181)
                  ·
                    refine ⟨182052683289223080406973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7767581153673518097364181 182052683289223080406973)
                    ·
                      rfl

theorem cell23_1063639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_1063639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063639 prefixEnd_1063639 := by exact prefixLift 1063639
  have htrace : WordTrace (prefixWord ++ tailWord_1063639) baseStart_1063639 baseEnd_1063639 := by
    simpa [prefixWord, tailWord_1063639, baseEnd_1063639] using wordTrace_append hprefix tailTrace_1063639
  have hstable : (prefixWord ++ tailWord_1063639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063639).length < 2 ^ (prefixWord ++ tailWord_1063639).sum := by decide
  have hdescent : baseEnd_1063639 < baseStart_1063639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063676 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_1063676 : Nat := 118140960795 + 1063676 * 2 ^ 59
def prefixEnd_1063676 : Nat := 4983230072969 + 3 ^ 40 * 1063676 * 2
def baseEnd_1063676 : Nat := 546177048651885596458249

theorem tailTrace_1063676 : CollatzResearch.WordTrace tailWord_1063676 prefixEnd_1063676 546177048651885596458249 := by
  unfold tailWord_1063676
  simp only [CollatzResearch.WordTrace]
  refine ⟨19397725447245494121553441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25863633929660658828737921 19397725447245494121553441)
  ·
    refine ⟨14548294085434120591165081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19397725447245494121553441 14548294085434120591165081)
    ·
      refine ⟨10911220564075590443373811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14548294085434120591165081 10911220564075590443373811)
      ·
        refine ⟨16366830846113385665060717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10911220564075590443373811 16366830846113385665060717)
        ·
          refine ⟨6137561567292519624397769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16366830846113385665060717 6137561567292519624397769)
          ·
            refine ⟨4603171175469389718298327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6137561567292519624397769 4603171175469389718298327)
            ·
              refine ⟨6904756763204084577447491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4603171175469389718298327 6904756763204084577447491)
              ·
                refine ⟨10357135144806126866171237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6904756763204084577447491 10357135144806126866171237)
                ·
                  refine ⟨1941962839651148787407107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10357135144806126866171237 1941962839651148787407107)
                  ·
                    refine ⟨2912944259476723181110661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1941962839651148787407107 2912944259476723181110661)
                    ·
                      refine ⟨546177048651885596458249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2912944259476723181110661 546177048651885596458249)
                      ·
                        rfl

theorem cell23_1063676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_1063676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063676 prefixEnd_1063676 := by exact prefixLift 1063676
  have htrace : WordTrace (prefixWord ++ tailWord_1063676) baseStart_1063676 baseEnd_1063676 := by
    simpa [prefixWord, tailWord_1063676, baseEnd_1063676] using wordTrace_append hprefix tailTrace_1063676
  have hstable : (prefixWord ++ tailWord_1063676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063676).length < 2 ^ (prefixWord ++ tailWord_1063676).sum := by decide
  have hdescent : baseEnd_1063676 < baseStart_1063676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063689 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 6]
def baseStart_1063689 : Nat := 118140960795 + 1063689 * 2 ^ 59
def prefixEnd_1063689 : Nat := 4983230072969 + 3 ^ 40 * 1063689 * 2
def baseEnd_1063689 : Nat := 546183723900394045595689

theorem tailTrace_1063689 : CollatzResearch.WordTrace tailWord_1063689 prefixEnd_1063689 546183723900394045595689 := by
  unfold tailWord_1063689
  simp only [CollatzResearch.WordTrace]
  refine ⟨38795925043443891463330121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25863950028962594308886747 38795925043443891463330121)
  ·
    refine ⟨29096943782582918597497591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38795925043443891463330121 29096943782582918597497591)
    ·
      refine ⟨43645415673874377896246387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29096943782582918597497591 43645415673874377896246387)
      ·
        refine ⟨65468123510811566844369581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43645415673874377896246387 65468123510811566844369581)
        ·
          refine ⟨24550546316554337566638593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65468123510811566844369581 24550546316554337566638593)
          ·
            refine ⟨18412909737415753174978945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24550546316554337566638593 18412909737415753174978945)
            ·
              refine ⟨13809682303061814881234209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18412909737415753174978945 13809682303061814881234209)
              ·
                refine ⟨10357261727296361160925657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13809682303061814881234209 10357261727296361160925657)
                ·
                  refine ⟨7767946295472270870694243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10357261727296361160925657 7767946295472270870694243)
                  ·
                    refine ⟨11651919443208406306041365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7767946295472270870694243 11651919443208406306041365)
                    ·
                      refine ⟨546183723900394045595689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11651919443208406306041365 546183723900394045595689)
                      ·
                        rfl

theorem cell23_1063689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_1063689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063689 prefixEnd_1063689 := by exact prefixLift 1063689
  have htrace : WordTrace (prefixWord ++ tailWord_1063689) baseStart_1063689 baseEnd_1063689 := by
    simpa [prefixWord, tailWord_1063689, baseEnd_1063689] using wordTrace_append hprefix tailTrace_1063689
  have hstable : (prefixWord ++ tailWord_1063689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063689).length < 2 ^ (prefixWord ++ tailWord_1063689).sum := by decide
  have hdescent : baseEnd_1063689 < baseStart_1063689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063713 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_1063713 : Nat := 118140960795 + 1063713 * 2 ^ 59
def prefixEnd_1063713 : Nat := 4983230072969 + 3 ^ 40 * 1063713 * 2
def baseEnd_1063713 : Nat := 546196047436101951695579

theorem tailTrace_1063713 : CollatzResearch.WordTrace tailWord_1063713 prefixEnd_1063713 546196047436101951695579 := by
  unfold tailWord_1063713
  simp only [CollatzResearch.WordTrace]
  refine ⟨38796800395356943562203793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25864533596904629041469195 38796800395356943562203793)
  ·
    refine ⟨29097600296517707671652845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38796800395356943562203793 29097600296517707671652845)
    ·
      refine ⟨10911600111194140376869817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29097600296517707671652845 10911600111194140376869817)
      ·
        refine ⟨8183700083395605282652363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10911600111194140376869817 8183700083395605282652363)
        ·
          refine ⟨12275550125093407923978545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8183700083395605282652363 12275550125093407923978545)
          ·
            refine ⟨9206662593820055942983909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12275550125093407923978545 9206662593820055942983909)
            ·
              refine ⟨1726249236341260489309483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9206662593820055942983909 1726249236341260489309483)
              ·
                refine ⟨2589373854511890733964225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726249236341260489309483 2589373854511890733964225)
                ·
                  refine ⟨1942030390883918050473169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2589373854511890733964225 1942030390883918050473169)
                  ·
                    refine ⟨1456522793162938537854877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1942030390883918050473169 1456522793162938537854877)
                    ·
                      refine ⟨546196047436101951695579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1456522793162938537854877 546196047436101951695579)
                      ·
                        rfl

theorem cell23_1063713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_1063713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063713 prefixEnd_1063713 := by exact prefixLift 1063713
  have htrace : WordTrace (prefixWord ++ tailWord_1063713) baseStart_1063713 baseEnd_1063713 := by
    simpa [prefixWord, tailWord_1063713, baseEnd_1063713] using wordTrace_append hprefix tailTrace_1063713
  have hstable : (prefixWord ++ tailWord_1063713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063713).length < 2 ^ (prefixWord ++ tailWord_1063713).sum := by decide
  have hdescent : baseEnd_1063713 < baseStart_1063713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063720 : List Nat := [2, 1, 5, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1063720 : Nat := 118140960795 + 1063720 * 2 ^ 59
def prefixEnd_1063720 : Nat := 4983230072969 + 3 ^ 40 * 1063720 * 2
def baseEnd_1063720 : Nat := 182066547266894474769349

theorem tailTrace_1063720 : CollatzResearch.WordTrace tailWord_1063720 prefixEnd_1063720 182066547266894474769349 := by
  unfold tailWord_1063720
  simp only [CollatzResearch.WordTrace]
  refine ⟨19398527853165791878854307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25864703804221055838472409 19398527853165791878854307)
  ·
    refine ⟨29097791779748687818281461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19398527853165791878854307 29097791779748687818281461)
    ·
      refine ⟨2727917979351439482963887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29097791779748687818281461 2727917979351439482963887)
      ·
        refine ⟨4091876969027159224445831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2727917979351439482963887 4091876969027159224445831)
        ·
          refine ⟨6137815453540738836668747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4091876969027159224445831 6137815453540738836668747)
          ·
            refine ⟨9206723180311108255003121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6137815453540738836668747 9206723180311108255003121)
            ·
              refine ⟨6905042385233331191252341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9206723180311108255003121 6905042385233331191252341)
              ·
                refine ⟨647347723615624799179907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6905042385233331191252341 647347723615624799179907)
                ·
                  refine ⟨971021585423437198769861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 647347723615624799179907 971021585423437198769861)
                  ·
                    refine ⟨182066547266894474769349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 971021585423437198769861 182066547266894474769349)
                    ·
                      rfl

theorem cell23_1063720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1063720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063720 prefixEnd_1063720 := by exact prefixLift 1063720
  have htrace : WordTrace (prefixWord ++ tailWord_1063720) baseStart_1063720 baseEnd_1063720 := by
    simpa [prefixWord, tailWord_1063720, baseEnd_1063720] using wordTrace_append hprefix tailTrace_1063720
  have hstable : (prefixWord ++ tailWord_1063720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063720).length < 2 ^ (prefixWord ++ tailWord_1063720).sum := by decide
  have hdescent : baseEnd_1063720 < baseStart_1063720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063733 : List Nat := [1, 3, 3, 1, 3, 2, 2, 2, 6]
def baseStart_1063733 : Nat := 118140960795 + 1063733 * 2 ^ 59
def prefixEnd_1063733 : Nat := 4983230072969 + 3 ^ 40 * 1063733 * 2
def baseEnd_1063733 : Nat := 60689590783243541493943

theorem tailTrace_1063733 : CollatzResearch.WordTrace tailWord_1063733 prefixEnd_1063733 60689590783243541493943 := by
  unfold tailWord_1063733
  simp only [CollatzResearch.WordTrace]
  refine ⟨38797529855284486977931853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25865019903522991318621235 38797529855284486977931853)
  ·
    refine ⟨14549073695731682616724445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38797529855284486977931853 14549073695731682616724445)
    ·
      refine ⟨5455902635899380981271667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14549073695731682616724445 5455902635899380981271667)
      ·
        refine ⟨8183853953849071471907501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5455902635899380981271667 8183853953849071471907501)
        ·
          refine ⟨3068945232693401801965313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8183853953849071471907501 3068945232693401801965313)
          ·
            refine ⟨2301708924520051351473985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3068945232693401801965313 2301708924520051351473985)
            ·
              refine ⟨1726281693390038513605489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2301708924520051351473985 1726281693390038513605489)
              ·
                refine ⟨1294711270042528885204117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1726281693390038513605489 1294711270042528885204117)
                ·
                  refine ⟨60689590783243541493943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1294711270042528885204117 60689590783243541493943)
                  ·
                    rfl

theorem cell23_1063733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 6].length) (baseStart_1063733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063733 prefixEnd_1063733 := by exact prefixLift 1063733
  have htrace : WordTrace (prefixWord ++ tailWord_1063733) baseStart_1063733 baseEnd_1063733 := by
    simpa [prefixWord, tailWord_1063733, baseEnd_1063733] using wordTrace_append hprefix tailTrace_1063733
  have hstable : (prefixWord ++ tailWord_1063733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063733).length < 2 ^ (prefixWord ++ tailWord_1063733).sum := by decide
  have hdescent : baseEnd_1063733 < baseStart_1063733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063770 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2]
def baseStart_1063770 : Nat := 118140960795 + 1063770 * 2 ^ 59
def prefixEnd_1063770 : Nat := 4983230072969 + 3 ^ 40 * 1063770 * 2
def baseEnd_1063770 : Nat := 546225315833408228682817

theorem tailTrace_1063770 : CollatzResearch.WordTrace tailWord_1063770 prefixEnd_1063770 546225315833408228682817 := by
  unfold tailWord_1063770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9699719839037610574257191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25865919570766961531352509 9699719839037610574257191)
  ·
    refine ⟨14549579758556415861385787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9699719839037610574257191 14549579758556415861385787)
    ·
      refine ⟨21824369637834623792078681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14549579758556415861385787 21824369637834623792078681)
      ·
        refine ⟨16368277228375967844059011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21824369637834623792078681 16368277228375967844059011)
        ·
          refine ⟨24552415842563951766088517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16368277228375967844059011 24552415842563951766088517)
          ·
            refine ⟨4603577970480740956141597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24552415842563951766088517 4603577970480740956141597)
            ·
              refine ⟨1726341738930277858553099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4603577970480740956141597 1726341738930277858553099)
              ·
                refine ⟨2589512608395416787829649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726341738930277858553099 2589512608395416787829649)
                ·
                  refine ⟨1942134456296562590872237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2589512608395416787829649 1942134456296562590872237)
                  ·
                    refine ⟨728300421111210971577089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1942134456296562590872237 728300421111210971577089)
                    ·
                      refine ⟨546225315833408228682817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728300421111210971577089 546225315833408228682817)
                      ·
                        rfl

theorem cell23_1063770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_1063770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063770 prefixEnd_1063770 := by exact prefixLift 1063770
  have htrace : WordTrace (prefixWord ++ tailWord_1063770) baseStart_1063770 baseEnd_1063770 := by
    simpa [prefixWord, tailWord_1063770, baseEnd_1063770] using wordTrace_append hprefix tailTrace_1063770
  have hstable : (prefixWord ++ tailWord_1063770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063770).length < 2 ^ (prefixWord ++ tailWord_1063770).sum := by decide
  have hdescent : baseEnd_1063770 < baseStart_1063770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063776 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 1, 6]
def baseStart_1063776 : Nat := 118140960795 + 1063776 * 2 ^ 59
def prefixEnd_1063776 : Nat := 4983230072969 + 3 ^ 40 * 1063776 * 2
def baseEnd_1063776 : Nat := 182076132239111735069263

theorem tailTrace_1063776 : CollatzResearch.WordTrace tailWord_1063776 prefixEnd_1063776 182076132239111735069263 := by
  unfold tailWord_1063776
  simp only [CollatzResearch.WordTrace]
  refine ⟨19399549097064352660873591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25866065462752470214498121 19399549097064352660873591)
  ·
    refine ⟨29099323645596528991310387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19399549097064352660873591 29099323645596528991310387)
    ·
      refine ⟨43648985468394793486965581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29099323645596528991310387 43648985468394793486965581)
      ·
        refine ⟨16368369550648047557612093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43648985468394793486965581 16368369550648047557612093)
        ·
          refine ⟨6138138581493017834104535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16368369550648047557612093 6138138581493017834104535)
          ·
            refine ⟨9207207872239526751156803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6138138581493017834104535 9207207872239526751156803)
            ·
              refine ⟨13810811808359290126735205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9207207872239526751156803 13810811808359290126735205)
              ·
                refine ⟨2589527214067366898762851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13810811808359290126735205 2589527214067366898762851)
                ·
                  refine ⟨3884290821101050348144277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589527214067366898762851 3884290821101050348144277)
                  ·
                    refine ⟨182076132239111735069263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3884290821101050348144277 182076132239111735069263)
                    ·
                      rfl

theorem cell23_1063776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 1, 6].length) (baseStart_1063776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063776 prefixEnd_1063776 := by exact prefixLift 1063776
  have htrace : WordTrace (prefixWord ++ tailWord_1063776) baseStart_1063776 baseEnd_1063776 := by
    simpa [prefixWord, tailWord_1063776, baseEnd_1063776] using wordTrace_append hprefix tailTrace_1063776
  have hstable : (prefixWord ++ tailWord_1063776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063776).length < 2 ^ (prefixWord ++ tailWord_1063776).sum := by decide
  have hdescent : baseEnd_1063776 < baseStart_1063776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063780 : List Nat := [2, 3, 1, 1, 4, 1, 4, 1, 1, 5]
def baseStart_1063780 : Nat := 118140960795 + 1063780 * 2 ^ 59
def prefixEnd_1063780 : Nat := 4983230072969 + 3 ^ 40 * 1063780 * 2
def baseEnd_1063780 : Nat := 182076816879984396519257

theorem tailTrace_1063780 : CollatzResearch.WordTrace tailWord_1063780 prefixEnd_1063780 182076816879984396519257 := by
  unfold tailWord_1063780
  simp only [CollatzResearch.WordTrace]
  refine ⟨19399622043057107002446397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25866162724076142669928529 19399622043057107002446397)
  ·
    refine ⟨7274858266146415125917399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19399622043057107002446397 7274858266146415125917399)
    ·
      refine ⟨10912287399219622688876099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7274858266146415125917399 10912287399219622688876099)
      ·
        refine ⟨16368431098829434033314149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10912287399219622688876099 16368431098829434033314149)
        ·
          refine ⟨3069080831030518881246403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16368431098829434033314149 3069080831030518881246403)
          ·
            refine ⟨4603621246545778321869605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3069080831030518881246403 4603621246545778321869605)
            ·
              refine ⟨863178983727333435350551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4603621246545778321869605 863178983727333435350551)
              ·
                refine ⟨1294768475591000153025827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863178983727333435350551 1294768475591000153025827)
                ·
                  refine ⟨1942152713386500229538741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294768475591000153025827 1942152713386500229538741)
                  ·
                    refine ⟨182076816879984396519257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1942152713386500229538741 182076816879984396519257)
                    ·
                      rfl

theorem cell23_1063780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_1063780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063780 prefixEnd_1063780 := by exact prefixLift 1063780
  have htrace : WordTrace (prefixWord ++ tailWord_1063780) baseStart_1063780 baseEnd_1063780 := by
    simpa [prefixWord, tailWord_1063780, baseEnd_1063780] using wordTrace_append hprefix tailTrace_1063780
  have hstable : (prefixWord ++ tailWord_1063780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063780).length < 2 ^ (prefixWord ++ tailWord_1063780).sum := by decide
  have hdescent : baseEnd_1063780 < baseStart_1063780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063793 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 4, 4]
def baseStart_1063793 : Nat := 118140960795 + 1063793 * 2 ^ 59
def prefixEnd_1063793 : Nat := 4983230072969 + 3 ^ 40 * 1063793 * 2
def baseEnd_1063793 : Nat := 182079041962820546231737

theorem tailTrace_1063793 : CollatzResearch.WordTrace tailWord_1063793 prefixEnd_1063793 182079041962820546231737 := by
  unfold tailWord_1063793
  simp only [CollatzResearch.WordTrace]
  refine ⟨38799718235067117225116033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25866478823378078150077355 38799718235067117225116033)
  ·
    refine ⟨29099788676300337918837025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38799718235067117225116033 29099788676300337918837025)
    ·
      refine ⟨21824841507225253439127769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29099788676300337918837025 21824841507225253439127769)
      ·
        refine ⟨16368631130418940079345827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21824841507225253439127769 16368631130418940079345827)
        ·
          refine ⟨24552946695628410119018741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16368631130418940079345827 24552946695628410119018741)
          ·
            refine ⟨2301838752715163448658007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24552946695628410119018741 2301838752715163448658007)
            ·
              refine ⟨3452758129072745172987011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2301838752715163448658007 3452758129072745172987011)
              ·
                refine ⟨5179137193609117759480517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3452758129072745172987011 5179137193609117759480517)
                ·
                  refine ⟨971088223801709579902597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5179137193609117759480517 971088223801709579902597)
                  ·
                    refine ⟨182079041962820546231737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 971088223801709579902597 182079041962820546231737)
                    ·
                      rfl

theorem cell23_1063793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_1063793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063793 prefixEnd_1063793 := by exact prefixLift 1063793
  have htrace : WordTrace (prefixWord ++ tailWord_1063793) baseStart_1063793 baseEnd_1063793 := by
    simpa [prefixWord, tailWord_1063793, baseEnd_1063793] using wordTrace_append hprefix tailTrace_1063793
  have hstable : (prefixWord ++ tailWord_1063793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063793).length < 2 ^ (prefixWord ++ tailWord_1063793).sum := by decide
  have hdescent : baseEnd_1063793 < baseStart_1063793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063813 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 1, 2, 4]
def baseStart_1063813 : Nat := 118140960795 + 1063813 * 2 ^ 59
def prefixEnd_1063813 : Nat := 4983230072969 + 3 ^ 40 * 1063813 * 2
def baseEnd_1063813 : Nat := 546247395501551560445119

theorem tailTrace_1063813 : CollatzResearch.WordTrace tailWord_1063813 prefixEnd_1063813 546247395501551560445119 := by
  unfold tailWord_1063813
  simp only [CollatzResearch.WordTrace]
  refine ⟨38800447694994660640844093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25866965129996440427229395 38800447694994660640844093)
  ·
    refine ⟨14550167885622997740316535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38800447694994660640844093 14550167885622997740316535)
    ·
      refine ⟨21825251828434496610474803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14550167885622997740316535 21825251828434496610474803)
      ·
        refine ⟨32737877742651744915712205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21825251828434496610474803 32737877742651744915712205)
        ·
          refine ⟨12276704153494404343392077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32737877742651744915712205 12276704153494404343392077)
          ·
            refine ⟨4603764057560401628772029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12276704153494404343392077 4603764057560401628772029)
            ·
              refine ⟨1726411521585150610789511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4603764057560401628772029 1726411521585150610789511)
              ·
                refine ⟨2589617282377725916184267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726411521585150610789511 2589617282377725916184267)
                ·
                  refine ⟨3884425923566588874276401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589617282377725916184267 3884425923566588874276401)
                  ·
                    refine ⟨2913319442674941655707301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3884425923566588874276401 2913319442674941655707301)
                    ·
                      refine ⟨546247395501551560445119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2913319442674941655707301 546247395501551560445119)
                      ·
                        rfl

theorem cell23_1063813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_1063813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063813 prefixEnd_1063813 := by exact prefixLift 1063813
  have htrace : WordTrace (prefixWord ++ tailWord_1063813) baseStart_1063813 baseEnd_1063813 := by
    simpa [prefixWord, tailWord_1063813, baseEnd_1063813] using wordTrace_append hprefix tailTrace_1063813
  have hstable : (prefixWord ++ tailWord_1063813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063813).length < 2 ^ (prefixWord ++ tailWord_1063813).sum := by decide
  have hdescent : baseEnd_1063813 < baseStart_1063813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063866 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 1, 8]
def baseStart_1063866 : Nat := 118140960795 + 1063866 * 2 ^ 59
def prefixEnd_1063866 : Nat := 4983230072969 + 3 ^ 40 * 1063866 * 2
def baseEnd_1063866 : Nat := 182091536658746617694125

theorem tailTrace_1063866 : CollatzResearch.WordTrace tailWord_1063866 prefixEnd_1063866 182091536658746617694125 := by
  unfold tailWord_1063866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9700595190950662673130863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25868253842535100461682301 9700595190950662673130863)
  ·
    refine ⟨14550892786425994009696295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9700595190950662673130863 14550892786425994009696295)
    ·
      refine ⟨21826339179638991014544443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14550892786425994009696295 21826339179638991014544443)
      ·
        refine ⟨32739508769458486521816665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21826339179638991014544443 32739508769458486521816665)
        ·
          refine ⟨24554631577093864891362499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32739508769458486521816665 24554631577093864891362499)
          ·
            refine ⟨36831947365640797337043749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24554631577093864891362499 36831947365640797337043749)
            ·
              refine ⟨6905990131057649500695703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36831947365640797337043749 6905990131057649500695703)
              ·
                refine ⟨10358985196586474251043555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6905990131057649500695703 10358985196586474251043555)
                ·
                  refine ⟨15538477794879711376565333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10358985196586474251043555 15538477794879711376565333)
                  ·
                    refine ⟨182091536658746617694125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15538477794879711376565333 182091536658746617694125)
                    ·
                      rfl

theorem cell23_1063866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_1063866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063866 prefixEnd_1063866 := by exact prefixLift 1063866
  have htrace : WordTrace (prefixWord ++ tailWord_1063866) baseStart_1063866 baseEnd_1063866 := by
    simpa [prefixWord, tailWord_1063866, baseEnd_1063866] using wordTrace_append hprefix tailTrace_1063866
  have hstable : (prefixWord ++ tailWord_1063866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063866).length < 2 ^ (prefixWord ++ tailWord_1063866).sum := by decide
  have hdescent : baseEnd_1063866 < baseStart_1063866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063916 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_1063916 : Nat := 118140960795 + 1063916 * 2 ^ 59
def prefixEnd_1063916 : Nat := 4983230072969 + 3 ^ 40 * 1063916 * 2
def baseEnd_1063916 : Nat := 546300284008964657457145

theorem tailTrace_1063916 : CollatzResearch.WordTrace tailWord_1063916 prefixEnd_1063916 546300284008964657457145 := by
  unfold tailWord_1063916
  simp only [CollatzResearch.WordTrace]
  refine ⟨19402102206810754615921801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25869469609081006154562401 19402102206810754615921801)
  ·
    refine ⟨14551576655108065961941351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19402102206810754615921801 14551576655108065961941351)
    ·
      refine ⟨21827364982662098942912027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14551576655108065961941351 21827364982662098942912027)
      ·
        refine ⟨32741047473993148414368041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21827364982662098942912027 32741047473993148414368041)
        ·
          refine ⟨24555785605494861310776031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32741047473993148414368041 24555785605494861310776031)
          ·
            refine ⟨36833678408242291966164047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24555785605494861310776031 36833678408242291966164047)
            ·
              refine ⟨55250517612363437949246071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36833678408242291966164047 55250517612363437949246071)
              ·
                refine ⟨82875776418545156923869107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55250517612363437949246071 82875776418545156923869107)
                ·
                  refine ⟨124313664627817735385803661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82875776418545156923869107 124313664627817735385803661)
                  ·
                    refine ⟨46617624235431650769676373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 124313664627817735385803661 46617624235431650769676373)
                    ·
                      refine ⟨546300284008964657457145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 46617624235431650769676373 546300284008964657457145)
                      ·
                        rfl

theorem cell23_1063916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_1063916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063916 prefixEnd_1063916 := by exact prefixLift 1063916
  have htrace : WordTrace (prefixWord ++ tailWord_1063916) baseStart_1063916 baseEnd_1063916 := by
    simpa [prefixWord, tailWord_1063916, baseEnd_1063916] using wordTrace_append hprefix tailTrace_1063916
  have hstable : (prefixWord ++ tailWord_1063916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063916).length < 2 ^ (prefixWord ++ tailWord_1063916).sum := by decide
  have hdescent : baseEnd_1063916 < baseStart_1063916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063943 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 1, 7]
def baseStart_1063943 : Nat := 118140960795 + 1063943 * 2 ^ 59
def prefixEnd_1063943 : Nat := 4983230072969 + 3 ^ 40 * 1063943 * 2
def baseEnd_1063943 : Nat := 182104715995545350606507

theorem tailTrace_1063943 : CollatzResearch.WordTrace tailWord_1063943 prefixEnd_1063943 182104715995545350606507 := by
  unfold tailWord_1063943
  simp only [CollatzResearch.WordTrace]
  refine ⟨38805189184523692843076483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25870126123015795228717655 38805189184523692843076483)
  ·
    refine ⟨58207783776785539264614725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38805189184523692843076483 58207783776785539264614725)
    ·
      refine ⟨10913959458147288612115261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58207783776785539264614725 10913959458147288612115261)
      ·
        refine ⟨4092734796805233229543223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10913959458147288612115261 4092734796805233229543223)
        ·
          refine ⟨6139102195207849844314835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4092734796805233229543223 6139102195207849844314835)
          ·
            refine ⟨9208653292811774766472253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6139102195207849844314835 9208653292811774766472253)
            ·
              refine ⟨3453244984804415537427095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9208653292811774766472253 3453244984804415537427095)
              ·
                refine ⟨5179867477206623306140643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3453244984804415537427095 5179867477206623306140643)
                ·
                  refine ⟨7769801215809934959210965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5179867477206623306140643 7769801215809934959210965)
                  ·
                    refine ⟨182104715995545350606507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7769801215809934959210965 182104715995545350606507)
                    ·
                      rfl

theorem cell23_1063943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_1063943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063943 prefixEnd_1063943 := by exact prefixLift 1063943
  have htrace : WordTrace (prefixWord ++ tailWord_1063943) baseStart_1063943 baseEnd_1063943 := by
    simpa [prefixWord, tailWord_1063943, baseEnd_1063943] using wordTrace_append hprefix tailTrace_1063943
  have hstable : (prefixWord ++ tailWord_1063943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063943).length < 2 ^ (prefixWord ++ tailWord_1063943).sum := by decide
  have hdescent : baseEnd_1063943 < baseStart_1063943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1063980 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 2, 4, 2]
def baseStart_1063980 : Nat := 118140960795 + 1063980 * 2 ^ 59
def prefixEnd_1063980 : Nat := 4983230072969 + 3 ^ 40 * 1063980 * 2
def baseEnd_1063980 : Nat := 546333146770852407056851

theorem tailTrace_1063980 : CollatzResearch.WordTrace tailWord_1063980 prefixEnd_1063980 546333146770852407056851 := by
  unfold tailWord_1063980
  simp only [CollatzResearch.WordTrace]
  refine ⟨19403269342694824081086697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25871025790259765441448929 19403269342694824081086697)
  ·
    refine ⟨14552452007021118060815023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19403269342694824081086697 14552452007021118060815023)
    ·
      refine ⟨21828678010531677091222535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14552452007021118060815023 21828678010531677091222535)
      ·
        refine ⟨32743017015797515636833803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21828678010531677091222535 32743017015797515636833803)
        ·
          refine ⟨49114525523696273455250705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32743017015797515636833803 49114525523696273455250705)
          ·
            refine ⟨36835894142772205091438029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49114525523696273455250705 36835894142772205091438029)
            ·
              refine ⟨13813460303539576909289261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36835894142772205091438029 13813460303539576909289261)
              ·
                refine ⟨5180047613827341340983473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13813460303539576909289261 5180047613827341340983473)
                ·
                  refine ⟨3885035710370506005737605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5180047613827341340983473 3885035710370506005737605)
                  ·
                    refine ⟨728444195694469876075801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3885035710370506005737605 728444195694469876075801)
                    ·
                      refine ⟨546333146770852407056851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728444195694469876075801 546333146770852407056851)
                      ·
                        rfl

theorem cell23_1063980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 4, 2].length) (baseStart_1063980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1063980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1063980 prefixEnd_1063980 := by exact prefixLift 1063980
  have htrace : WordTrace (prefixWord ++ tailWord_1063980) baseStart_1063980 baseEnd_1063980 := by
    simpa [prefixWord, tailWord_1063980, baseEnd_1063980] using wordTrace_append hprefix tailTrace_1063980
  have hstable : (prefixWord ++ tailWord_1063980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1063980).length < 2 ^ (prefixWord ++ tailWord_1063980).sum := by decide
  have hdescent : baseEnd_1063980 < baseStart_1063980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1063980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064000 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 3]
def baseStart_1064000 : Nat := 118140960795 + 1064000 * 2 ^ 59
def prefixEnd_1064000 : Nat := 4983230072969 + 3 ^ 40 * 1064000 * 2
def baseEnd_1064000 : Nat := 546343416383942328806759

theorem tailTrace_1064000 : CollatzResearch.WordTrace tailWord_1064000 prefixEnd_1064000 546343416383942328806759 := by
  unfold tailWord_1064000
  simp only [CollatzResearch.WordTrace]
  refine ⟨19403634072658595788950727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25871512096878127718600969 19403634072658595788950727)
  ·
    refine ⟨29105451108987893683426091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19403634072658595788950727 29105451108987893683426091)
    ·
      refine ⟨43658176663481840525139137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29105451108987893683426091 43658176663481840525139137)
      ·
        refine ⟨32743632497611380393854353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43658176663481840525139137 32743632497611380393854353)
        ·
          refine ⟨24557724373208535295390765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32743632497611380393854353 24557724373208535295390765)
          ·
            refine ⟨9209146639953200735771537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24557724373208535295390765 9209146639953200735771537)
            ·
              refine ⟨6906859979964900551828653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9209146639953200735771537 6906859979964900551828653)
              ·
                refine ⟨2590072492486837706935745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6906859979964900551828653 2590072492486837706935745)
                ·
                  refine ⟨1942554369365128280201809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2590072492486837706935745 1942554369365128280201809)
                  ·
                    refine ⟨1456915777023846210151357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1942554369365128280201809 1456915777023846210151357)
                    ·
                      refine ⟨546343416383942328806759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1456915777023846210151357 546343416383942328806759)
                      ·
                        rfl

theorem cell23_1064000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_1064000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064000 prefixEnd_1064000 := by exact prefixLift 1064000
  have htrace : WordTrace (prefixWord ++ tailWord_1064000) baseStart_1064000 baseEnd_1064000 := by
    simpa [prefixWord, tailWord_1064000, baseEnd_1064000] using wordTrace_append hprefix tailTrace_1064000
  have hstable : (prefixWord ++ tailWord_1064000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064000).length < 2 ^ (prefixWord ++ tailWord_1064000).sum := by decide
  have hdescent : baseEnd_1064000 < baseStart_1064000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064024 : List Nat := [2, 1, 2, 2, 1, 3, 5, 2, 1, 4]
def baseStart_1064024 : Nat := 118140960795 + 1064024 * 2 ^ 59
def prefixEnd_1064024 : Nat := 4983230072969 + 3 ^ 40 * 1064024 * 2
def baseEnd_1064024 : Nat := 182118579973216744968883

theorem tailTrace_1064024 : CollatzResearch.WordTrace tailWord_1064024 prefixEnd_1064024 182118579973216744968883 := by
  unfold tailWord_1064024
  simp only [CollatzResearch.WordTrace]
  refine ⟨19404071748615121838387563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25872095664820162451183417 19404071748615121838387563)
  ·
    refine ⟨29106107622922682757581345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19404071748615121838387563 29106107622922682757581345)
    ·
      refine ⟨21829580717192012068186009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29106107622922682757581345 21829580717192012068186009)
      ·
        refine ⟨16372185537894009051139507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21829580717192012068186009 16372185537894009051139507)
        ·
          refine ⟨24558278306841013576709261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16372185537894009051139507 24558278306841013576709261)
          ·
            refine ⟨9209354365065380091265973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24558278306841013576709261 9209354365065380091265973)
            ·
              refine ⟨863376971724879383556185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9209354365065380091265973 863376971724879383556185)
              ·
                refine ⟨647532728793659537667139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 863376971724879383556185 647532728793659537667139)
                ·
                  refine ⟨971299093190489306500709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 647532728793659537667139 971299093190489306500709)
                  ·
                    refine ⟨182118579973216744968883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 971299093190489306500709 182118579973216744968883)
                    ·
                      rfl

theorem cell23_1064024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_1064024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064024 prefixEnd_1064024 := by exact prefixLift 1064024
  have htrace : WordTrace (prefixWord ++ tailWord_1064024) baseStart_1064024 baseEnd_1064024 := by
    simpa [prefixWord, tailWord_1064024, baseEnd_1064024] using wordTrace_append hprefix tailTrace_1064024
  have hstable : (prefixWord ++ tailWord_1064024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064024).length < 2 ^ (prefixWord ++ tailWord_1064024).sum := by decide
  have hdescent : baseEnd_1064024 < baseStart_1064024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064050 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_1064050 : Nat := 118140960795 + 1064050 * 2 ^ 59
def prefixEnd_1064050 : Nat := 4983230072969 + 3 ^ 40 * 1064050 * 2
def baseEnd_1064050 : Nat := 182123030138889044393843

theorem tailTrace_1064050 : CollatzResearch.WordTrace tailWord_1064050 prefixEnd_1064050 182123030138889044393843 := by
  unfold tailWord_1064050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9702272948784012529305401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25872727863424033411481069 9702272948784012529305401)
  ·
    refine ⟨7276704711588009396979051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9702272948784012529305401 7276704711588009396979051)
    ·
      refine ⟨10915057067382014095468577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7276704711588009396979051 10915057067382014095468577)
      ·
        refine ⟨8186292800536510571601433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10915057067382014095468577 8186292800536510571601433)
        ·
          refine ⟨6139719600402382928701075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8186292800536510571601433 6139719600402382928701075)
          ·
            refine ⟨9209579400603574393051613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6139719600402382928701075 9209579400603574393051613)
            ·
              refine ⟨3453592275226340397394355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9209579400603574393051613 3453592275226340397394355)
              ·
                refine ⟨5180388412839510596091533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3453592275226340397394355 5180388412839510596091533)
                ·
                  refine ⟨1942645654814816473534325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5180388412839510596091533 1942645654814816473534325)
                  ·
                    refine ⟨182123030138889044393843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1942645654814816473534325 182123030138889044393843)
                    ·
                      rfl

theorem cell23_1064050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_1064050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064050 prefixEnd_1064050 := by exact prefixLift 1064050
  have htrace : WordTrace (prefixWord ++ tailWord_1064050) baseStart_1064050 baseEnd_1064050 := by
    simpa [prefixWord, tailWord_1064050, baseEnd_1064050] using wordTrace_append hprefix tailTrace_1064050
  have hstable : (prefixWord ++ tailWord_1064050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064050).length < 2 ^ (prefixWord ++ tailWord_1064050).sum := by decide
  have hdescent : baseEnd_1064050 < baseStart_1064050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064067 : List Nat := [1, 1, 1, 3, 3, 2, 5, 1, 1, 5]
def baseStart_1064067 : Nat := 118140960795 + 1064067 * 2 ^ 59
def prefixEnd_1064067 : Nat := 4983230072969 + 3 ^ 40 * 1064067 * 2
def baseEnd_1064067 : Nat := 182125939862597855556317

theorem tailTrace_1064067 : CollatzResearch.WordTrace tailWord_1064067 prefixEnd_1064067 182125939862597855556317 := by
  unfold tailWord_1064067
  simp only [CollatzResearch.WordTrace]
  refine ⟨38809711836074462020590455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25873141224049641347060303 38809711836074462020590455)
  ·
    refine ⟨58214567754111693030885683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38809711836074462020590455 58214567754111693030885683)
    ·
      refine ⟨87321851631167539546328525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58214567754111693030885683 87321851631167539546328525)
      ·
        refine ⟨32745694361687827329873197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87321851631167539546328525 32745694361687827329873197)
        ·
          refine ⟨12279635385632935248702449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32745694361687827329873197 12279635385632935248702449)
          ·
            refine ⟨9209726539224701436526837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12279635385632935248702449 9209726539224701436526837)
            ·
              refine ⟨863411863052315759674391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9209726539224701436526837 863411863052315759674391)
              ·
                refine ⟨1295117794578473639511587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863411863052315759674391 1295117794578473639511587)
                ·
                  refine ⟨1942676691867710459267381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295117794578473639511587 1942676691867710459267381)
                  ·
                    refine ⟨182125939862597855556317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1942676691867710459267381 182125939862597855556317)
                    ·
                      rfl

theorem cell23_1064067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 1, 5].length) (baseStart_1064067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064067 prefixEnd_1064067 := by exact prefixLift 1064067
  have htrace : WordTrace (prefixWord ++ tailWord_1064067) baseStart_1064067 baseEnd_1064067 := by
    simpa [prefixWord, tailWord_1064067, baseEnd_1064067] using wordTrace_append hprefix tailTrace_1064067
  have hstable : (prefixWord ++ tailWord_1064067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064067).length < 2 ^ (prefixWord ++ tailWord_1064067).sum := by decide
  have hdescent : baseEnd_1064067 < baseStart_1064067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064083 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 6]
def baseStart_1064083 : Nat := 118140960795 + 1064083 * 2 ^ 59
def prefixEnd_1064083 : Nat := 4983230072969 + 3 ^ 40 * 1064083 * 2
def baseEnd_1064083 : Nat := 546386035278265504068877

theorem tailTrace_1064083 : CollatzResearch.WordTrace tailWord_1064083 prefixEnd_1064083 546386035278265504068877 := by
  unfold tailWord_1064083
  simp only [CollatzResearch.WordTrace]
  refine ⟨38810295404016496753172903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25873530269344331168781935 38810295404016496753172903)
  ·
    refine ⟨58215443106024745129759355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38810295404016496753172903 58215443106024745129759355)
    ·
      refine ⟨87323164659037117694639033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58215443106024745129759355 87323164659037117694639033)
      ·
        refine ⟨65492373494277838270979275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87323164659037117694639033 65492373494277838270979275)
        ·
          refine ⟨98238560241416757406468913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65492373494277838270979275 98238560241416757406468913)
          ·
            refine ⟨73678920181062568054851685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98238560241416757406468913 73678920181062568054851685)
            ·
              refine ⟨13814797533949231510284691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73678920181062568054851685 13814797533949231510284691)
              ·
                refine ⟨20722196300923847265427037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13814797533949231510284691 20722196300923847265427037)
                ·
                  refine ⟨7770823612846442724535139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20722196300923847265427037 7770823612846442724535139)
                  ·
                    refine ⟨11656235419269664086802709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7770823612846442724535139 11656235419269664086802709)
                    ·
                      refine ⟨546386035278265504068877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11656235419269664086802709 546386035278265504068877)
                      ·
                        rfl

theorem cell23_1064083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_1064083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064083 prefixEnd_1064083 := by exact prefixLift 1064083
  have htrace : WordTrace (prefixWord ++ tailWord_1064083) baseStart_1064083 baseEnd_1064083 := by
    simpa [prefixWord, tailWord_1064083, baseEnd_1064083] using wordTrace_append hprefix tailTrace_1064083
  have hstable : (prefixWord ++ tailWord_1064083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064083).length < 2 ^ (prefixWord ++ tailWord_1064083).sum := by decide
  have hdescent : baseEnd_1064083 < baseStart_1064083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064097 : List Nat := [1, 2, 3, 3, 1, 1, 1, 5, 2, 4]
def baseStart_1064097 : Nat := 118140960795 + 1064097 * 2 ^ 59
def prefixEnd_1064097 : Nat := 4983230072969 + 3 ^ 40 * 1064097 * 2
def baseEnd_1064097 : Nat := 182131074669142816431271

theorem tailTrace_1064097 : CollatzResearch.WordTrace tailWord_1064097 prefixEnd_1064097 182131074669142816431271 := by
  unfold tailWord_1064097
  simp only [CollatzResearch.WordTrace]
  refine ⟨38810806025965777144182545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25873870683977184762788363 38810806025965777144182545)
  ·
    refine ⟨29108104519474332858136909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38810806025965777144182545 29108104519474332858136909)
    ·
      refine ⟨10915539194802874821801341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29108104519474332858136909 10915539194802874821801341)
      ·
        refine ⟨4093327198051078058175503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10915539194802874821801341 4093327198051078058175503)
        ·
          refine ⟨6139990797076617087263255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4093327198051078058175503 6139990797076617087263255)
          ·
            refine ⟨9209986195614925630894883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6139990797076617087263255 9209986195614925630894883)
            ·
              refine ⟨13814979293422388446342325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9209986195614925630894883 13814979293422388446342325)
              ·
                refine ⟨1295154308758348916844593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13814979293422388446342325 1295154308758348916844593)
                ·
                  refine ⟨971365731568761687633445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1295154308758348916844593 971365731568761687633445)
                  ·
                    refine ⟨182131074669142816431271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 971365731568761687633445 182131074669142816431271)
                    ·
                      rfl

theorem cell23_1064097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_1064097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064097 prefixEnd_1064097 := by exact prefixLift 1064097
  have htrace : WordTrace (prefixWord ++ tailWord_1064097) baseStart_1064097 baseEnd_1064097 := by
    simpa [prefixWord, tailWord_1064097, baseEnd_1064097] using wordTrace_append hprefix tailTrace_1064097
  have hstable : (prefixWord ++ tailWord_1064097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064097).length < 2 ^ (prefixWord ++ tailWord_1064097).sum := by decide
  have hdescent : baseEnd_1064097 < baseStart_1064097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064120 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 3, 3, 3]
def baseStart_1064120 : Nat := 118140960795 + 1064120 * 2 ^ 59
def prefixEnd_1064120 : Nat := 4983230072969 + 3 ^ 40 * 1064120 * 2
def baseEnd_1064120 : Nat := 546405034062481859306207

theorem tailTrace_1064120 : CollatzResearch.WordTrace tailWord_1064120 prefixEnd_1064120 546405034062481859306207 := by
  unfold tailWord_1064120
  simp only [CollatzResearch.WordTrace]
  refine ⟨19405822452441226036134907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25874429936588301381513209 19405822452441226036134907)
  ·
    refine ⟨29108733678661839054202361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19405822452441226036134907 29108733678661839054202361)
    ·
      refine ⟨21831550258996379290651771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29108733678661839054202361 21831550258996379290651771)
      ·
        refine ⟨32747325388494568935977657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21831550258996379290651771 32747325388494568935977657)
        ·
          refine ⟨24560494041370926701983243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32747325388494568935977657 24560494041370926701983243)
          ·
            refine ⟨36840741062056390052974865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24560494041370926701983243 36840741062056390052974865)
            ·
              refine ⟨27630555796542292539731149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36840741062056390052974865 27630555796542292539731149)
              ·
                refine ⟨10361458423703359702399181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27630555796542292539731149 10361458423703359702399181)
                ·
                  refine ⟨3885546908888759888399693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10361458423703359702399181 3885546908888759888399693)
                  ·
                    refine ⟨1457080090833284958149885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3885546908888759888399693 1457080090833284958149885)
                    ·
                      refine ⟨546405034062481859306207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1457080090833284958149885 546405034062481859306207)
                      ·
                        rfl

theorem cell23_1064120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_1064120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064120 prefixEnd_1064120 := by exact prefixLift 1064120
  have htrace : WordTrace (prefixWord ++ tailWord_1064120) baseStart_1064120 baseEnd_1064120 := by
    simpa [prefixWord, tailWord_1064120, baseEnd_1064120] using wordTrace_append hprefix tailTrace_1064120
  have hstable : (prefixWord ++ tailWord_1064120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064120).length < 2 ^ (prefixWord ++ tailWord_1064120).sum := by decide
  have hdescent : baseEnd_1064120 < baseStart_1064120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064121 : List Nat := [1, 2, 1, 4, 1, 3, 1, 5, 1, 2, 2]
def baseStart_1064121 : Nat := 118140960795 + 1064121 * 2 ^ 59
def prefixEnd_1064121 : Nat := 4983230072969 + 3 ^ 40 * 1064121 * 2
def baseEnd_1064121 : Nat := 546405547543136355393703

theorem tailTrace_1064121 : CollatzResearch.WordTrace tailWord_1064121 prefixEnd_1064121 546405547543136355393703 := by
  unfold tailWord_1064121
  simp only [CollatzResearch.WordTrace]
  refine ⟨38811681377878829243056217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25874454251919219495370811 38811681377878829243056217)
  ·
    refine ⟨29108761033409121932292163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38811681377878829243056217 29108761033409121932292163)
    ·
      refine ⟨43663141550113682898438245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29108761033409121932292163 43663141550113682898438245)
      ·
        refine ⟨8186839040646315543457171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43663141550113682898438245 8186839040646315543457171)
        ·
          refine ⟨12280258560969473315185757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8186839040646315543457171 12280258560969473315185757)
          ·
            refine ⟨4605096960363552493194659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12280258560969473315185757 4605096960363552493194659)
            ·
              refine ⟨6907645440545328739791989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4605096960363552493194659 6907645440545328739791989)
              ·
                refine ⟨647591760051124569355499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6907645440545328739791989 647591760051124569355499)
                ·
                  refine ⟨971387640076686854033249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 647591760051124569355499 971387640076686854033249)
                  ·
                    refine ⟨728540730057515140524937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 971387640076686854033249 728540730057515140524937)
                    ·
                      refine ⟨546405547543136355393703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728540730057515140524937 546405547543136355393703)
                      ·
                        rfl

theorem cell23_1064121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_1064121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064121 prefixEnd_1064121 := by exact prefixLift 1064121
  have htrace : WordTrace (prefixWord ++ tailWord_1064121) baseStart_1064121 baseEnd_1064121 := by
    simpa [prefixWord, tailWord_1064121, baseEnd_1064121] using wordTrace_append hprefix tailTrace_1064121
  have hstable : (prefixWord ++ tailWord_1064121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064121).length < 2 ^ (prefixWord ++ tailWord_1064121).sum := by decide
  have hdescent : baseEnd_1064121 < baseStart_1064121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064123 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 1, 9]
def baseStart_1064123 : Nat := 118140960795 + 1064123 * 2 ^ 59
def prefixEnd_1064123 : Nat := 4983230072969 + 3 ^ 40 * 1064123 * 2
def baseEnd_1064123 : Nat := 182135524834815115856231

theorem tailTrace_1064123 : CollatzResearch.WordTrace tailWord_1064123 prefixEnd_1064123 182135524834815115856231 := by
  unfold tailWord_1064123
  simp only [CollatzResearch.WordTrace]
  refine ⟨38811754323871583584629023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25874502882581055723086015 38811754323871583584629023)
  ·
    refine ⟨58217631485807375376943535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38811754323871583584629023 58217631485807375376943535)
    ·
      refine ⟨87326447228711063065415303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58217631485807375376943535 87326447228711063065415303)
      ·
        refine ⟨130989670843066594598122955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87326447228711063065415303 130989670843066594598122955)
        ·
          refine ⟨196484506264599891897184433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130989670843066594598122955 196484506264599891897184433)
          ·
            refine ⟨147363379698449918922888325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196484506264599891897184433 147363379698449918922888325)
            ·
              refine ⟨27630633693459359798041561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 147363379698449918922888325 27630633693459359798041561)
              ·
                refine ⟨20722975270094519848531171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27630633693459359798041561 20722975270094519848531171)
                ·
                  refine ⟨31084462905141779772796757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20722975270094519848531171 31084462905141779772796757)
                  ·
                    refine ⟨182135524834815115856231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 31084462905141779772796757 182135524834815115856231)
                    ·
                      rfl

theorem cell23_1064123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 9].length) (baseStart_1064123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064123 prefixEnd_1064123 := by exact prefixLift 1064123
  have htrace : WordTrace (prefixWord ++ tailWord_1064123) baseStart_1064123 baseEnd_1064123 := by
    simpa [prefixWord, tailWord_1064123, baseEnd_1064123] using wordTrace_append hprefix tailTrace_1064123
  have hstable : (prefixWord ++ tailWord_1064123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064123).length < 2 ^ (prefixWord ++ tailWord_1064123).sum := by decide
  have hdescent : baseEnd_1064123 < baseStart_1064123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064124 : List Nat := [2, 2, 2, 3, 2, 2, 1, 3, 1, 2, 3]
def baseStart_1064124 : Nat := 118140960795 + 1064124 * 2 ^ 59
def prefixEnd_1064124 : Nat := 4983230072969 + 3 ^ 40 * 1064124 * 2
def baseEnd_1064124 : Nat := 546407087985099843656189

theorem tailTrace_1064124 : CollatzResearch.WordTrace tailWord_1064124 prefixEnd_1064124 546407087985099843656189 := by
  unfold tailWord_1064124
  simp only [CollatzResearch.WordTrace]
  refine ⟨19405895398433980377707713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25874527197911973836943617 19405895398433980377707713)
  ·
    refine ⟨14554421548825485283280785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19405895398433980377707713 14554421548825485283280785)
    ·
      refine ⟨10915816161619113962460589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14554421548825485283280785 10915816161619113962460589)
      ·
        refine ⟨4093431060607167735922721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10915816161619113962460589 4093431060607167735922721)
        ·
          refine ⟨3070073295455375801942041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4093431060607167735922721 3070073295455375801942041)
          ·
            refine ⟨2302554971591531851456531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3070073295455375801942041 2302554971591531851456531)
            ·
              refine ⟨3453832457387297777184797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302554971591531851456531 3453832457387297777184797)
              ·
                refine ⟨1295187171520236666444299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3453832457387297777184797 1295187171520236666444299)
                ·
                  refine ⟨1942780757280354999666449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295187171520236666444299 1942780757280354999666449)
                  ·
                    refine ⟨1457085567960266249749837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1942780757280354999666449 1457085567960266249749837)
                    ·
                      refine ⟨546407087985099843656189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1457085567960266249749837 546407087985099843656189)
                      ·
                        rfl

theorem cell23_1064124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_1064124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064124 prefixEnd_1064124 := by exact prefixLift 1064124
  have htrace : WordTrace (prefixWord ++ tailWord_1064124) baseStart_1064124 baseEnd_1064124 := by
    simpa [prefixWord, tailWord_1064124, baseEnd_1064124] using wordTrace_append hprefix tailTrace_1064124
  have hstable : (prefixWord ++ tailWord_1064124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064124).length < 2 ^ (prefixWord ++ tailWord_1064124).sum := by decide
  have hdescent : baseEnd_1064124 < baseStart_1064124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064141 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1064141 : Nat := 118140960795 + 1064141 * 2 ^ 59
def prefixEnd_1064141 : Nat := 4983230072969 + 3 ^ 40 * 1064141 * 2
def baseEnd_1064141 : Nat := 546415817156226277143611

theorem tailTrace_1064141 : CollatzResearch.WordTrace tailWord_1064141 prefixEnd_1064141 546415817156226277143611 := by
  unfold tailWord_1064141
  simp only [CollatzResearch.WordTrace]
  refine ⟨38812410837806372658784277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25874940558537581772522851 38812410837806372658784277)
  ·
    refine ⟨1819331758022173718380513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38812410837806372658784277 1819331758022173718380513)
    ·
      refine ⟨1364498818516630288785385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1819331758022173718380513 1364498818516630288785385)
      ·
        refine ⟨1023374113887472716589039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1364498818516630288785385 1023374113887472716589039)
        ·
          refine ⟨1535061170831209074883559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023374113887472716589039 1535061170831209074883559)
          ·
            refine ⟨2302591756246813612325339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535061170831209074883559 2302591756246813612325339)
            ·
              refine ⟨3453887634370220418488009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302591756246813612325339 3453887634370220418488009)
              ·
                refine ⟨2590415725777665313866007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3453887634370220418488009 2590415725777665313866007)
                ·
                  refine ⟨3885623588666497970799011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2590415725777665313866007 3885623588666497970799011)
                  ·
                    refine ⟨5828435382999746956198517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3885623588666497970799011 5828435382999746956198517)
                    ·
                      refine ⟨546415817156226277143611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5828435382999746956198517 546415817156226277143611)
                      ·
                        rfl

theorem cell23_1064141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1064141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064141 prefixEnd_1064141 := by exact prefixLift 1064141
  have htrace : WordTrace (prefixWord ++ tailWord_1064141) baseStart_1064141 baseEnd_1064141 := by
    simpa [prefixWord, tailWord_1064141, baseEnd_1064141] using wordTrace_append hprefix tailTrace_1064141
  have hstable : (prefixWord ++ tailWord_1064141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064141).length < 2 ^ (prefixWord ++ tailWord_1064141).sum := by decide
  have hdescent : baseEnd_1064141 < baseStart_1064141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064148 : List Nat := [2, 4, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_1064148 : Nat := 118140960795 + 1064148 * 2 ^ 59
def prefixEnd_1064148 : Nat := 4983230072969 + 3 ^ 40 * 1064148 * 2
def baseEnd_1064148 : Nat := 182139803840269249918693

theorem tailTrace_1064148 : CollatzResearch.WordTrace tailWord_1064148 prefixEnd_1064148 182139803840269249918693 := by
  unfold tailWord_1064148
  simp only [CollatzResearch.WordTrace]
  refine ⟨19406333074390506427144549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25875110765854008569526065 19406333074390506427144549)
  ·
    refine ⟨3638687451448219955089603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19406333074390506427144549 3638687451448219955089603)
    ·
      refine ⟨5458031177172329932634405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3638687451448219955089603 5458031177172329932634405)
      ·
        refine ⟨1023380845719811862368951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5458031177172329932634405 1023380845719811862368951)
        ·
          refine ⟨1535071268579717793553427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023380845719811862368951 1535071268579717793553427)
          ·
            refine ⟨2302606902869576690330141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535071268579717793553427 2302606902869576690330141)
            ·
              refine ⟨863477588576091258873803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2302606902869576690330141 863477588576091258873803)
              ·
                refine ⟨1295216382864136888310705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863477588576091258873803 1295216382864136888310705)
                ·
                  refine ⟨971412287148102666233029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1295216382864136888310705 971412287148102666233029)
                  ·
                    refine ⟨182139803840269249918693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 971412287148102666233029 182139803840269249918693)
                    ·
                      rfl

theorem cell23_1064148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_1064148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064148 prefixEnd_1064148 := by exact prefixLift 1064148
  have htrace : WordTrace (prefixWord ++ tailWord_1064148) baseStart_1064148 baseEnd_1064148 := by
    simpa [prefixWord, tailWord_1064148, baseEnd_1064148] using wordTrace_append hprefix tailTrace_1064148
  have hstable : (prefixWord ++ tailWord_1064148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064148).length < 2 ^ (prefixWord ++ tailWord_1064148).sum := by decide
  have hdescent : baseEnd_1064148 < baseStart_1064148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064164 : List Nat := [2, 3, 1, 1, 1, 2, 3, 4, 1, 3, 2]
def baseStart_1064164 : Nat := 118140960795 + 1064164 * 2 ^ 59
def prefixEnd_1064164 : Nat := 4983230072969 + 3 ^ 40 * 1064164 * 2
def baseEnd_1064164 : Nat := 546427627211279687156005

theorem tailTrace_1064164 : CollatzResearch.WordTrace tailWord_1064164 prefixEnd_1064164 546427627211279687156005 := by
  unfold tailWord_1064164
  simp only [CollatzResearch.WordTrace]
  refine ⟨19406624858361523793435773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25875499811148698391247697 19406624858361523793435773)
  ·
    refine ⟨7277484321885571422538415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19406624858361523793435773 7277484321885571422538415)
    ·
      refine ⟨10916226482828357133807623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7277484321885571422538415 10916226482828357133807623)
      ·
        refine ⟨16374339724242535700711435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10916226482828357133807623 16374339724242535700711435)
        ·
          refine ⟨24561509586363803551067153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16374339724242535700711435 24561509586363803551067153)
          ·
            refine ⟨18421132189772852663300365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24561509586363803551067153 18421132189772852663300365)
            ·
              refine ⟨6907924571164819748737637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18421132189772852663300365 6907924571164819748737637)
              ·
                refine ⟨1295235857093403702888307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6907924571164819748737637 1295235857093403702888307)
                ·
                  refine ⟨1942853785640105554332461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295235857093403702888307 1942853785640105554332461)
                  ·
                    refine ⟨728570169615039582874673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1942853785640105554332461 728570169615039582874673)
                    ·
                      refine ⟨546427627211279687156005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728570169615039582874673 546427627211279687156005)
                      ·
                        rfl

theorem cell23_1064164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_1064164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064164 prefixEnd_1064164 := by exact prefixLift 1064164
  have htrace : WordTrace (prefixWord ++ tailWord_1064164) baseStart_1064164 baseEnd_1064164 := by
    simpa [prefixWord, tailWord_1064164, baseEnd_1064164] using wordTrace_append hprefix tailTrace_1064164
  have hstable : (prefixWord ++ tailWord_1064164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064164).length < 2 ^ (prefixWord ++ tailWord_1064164).sum := by decide
  have hdescent : baseEnd_1064164 < baseStart_1064164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064177 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 3, 4, 2]
def baseStart_1064177 : Nat := 118140960795 + 1064177 * 2 ^ 59
def prefixEnd_1064177 : Nat := 4983230072969 + 3 ^ 40 * 1064177 * 2
def baseEnd_1064177 : Nat := 546434302459788136293445

theorem tailTrace_1064177 : CollatzResearch.WordTrace tailWord_1064177 prefixEnd_1064177 546434302459788136293445 := by
  unfold tailWord_1064177
  simp only [CollatzResearch.WordTrace]
  refine ⟨38813723865675950807094785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25875815910450633871396523 38813723865675950807094785)
  ·
    refine ⟨29110292899256963105321089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38813723865675950807094785 29110292899256963105321089)
    ·
      refine ⟨21832719674442722328990817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29110292899256963105321089 21832719674442722328990817)
      ·
        refine ⟨16374539755832041746743113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21832719674442722328990817 16374539755832041746743113)
        ·
          refine ⟨12280904816874031310057335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16374539755832041746743113 12280904816874031310057335)
          ·
            refine ⟨18421357225311046965086003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12280904816874031310057335 18421357225311046965086003)
            ·
              refine ⟨27632035837966570447629005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18421357225311046965086003 27632035837966570447629005)
              ·
                refine ⟨10362013439237463917860877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27632035837966570447629005 10362013439237463917860877)
                ·
                  refine ⟨3885755039714048969197829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10362013439237463917860877 3885755039714048969197829)
                  ·
                    refine ⟨728579069946384181724593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3885755039714048969197829 728579069946384181724593)
                    ·
                      refine ⟨546434302459788136293445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728579069946384181724593 546434302459788136293445)
                      ·
                        rfl

theorem cell23_1064177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_1064177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064177 prefixEnd_1064177 := by exact prefixLift 1064177
  have htrace : WordTrace (prefixWord ++ tailWord_1064177) baseStart_1064177 baseEnd_1064177 := by
    simpa [prefixWord, tailWord_1064177, baseEnd_1064177] using wordTrace_append hprefix tailTrace_1064177
  have hstable : (prefixWord ++ tailWord_1064177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064177).length < 2 ^ (prefixWord ++ tailWord_1064177).sum := by decide
  have hdescent : baseEnd_1064177 < baseStart_1064177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064240 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 5]
def baseStart_1064240 : Nat := 118140960795 + 1064240 * 2 ^ 59
def prefixEnd_1064240 : Nat := 4983230072969 + 3 ^ 40 * 1064240 * 2
def baseEnd_1064240 : Nat := 546466651741021389805655

theorem tailTrace_1064240 : CollatzResearch.WordTrace tailWord_1064240 prefixEnd_1064240 546466651741021389805655 := by
  unfold tailWord_1064240
  simp only [CollatzResearch.WordTrace]
  refine ⟨19408010832223856283319087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25877347776298475044425449 19408010832223856283319087)
  ·
    refine ⟨29112016248335784424978631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19408010832223856283319087 29112016248335784424978631)
    ·
      refine ⟨43668024372503676637467947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29112016248335784424978631 43668024372503676637467947)
      ·
        refine ⟨65502036558755514956201921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43668024372503676637467947 65502036558755514956201921)
        ·
          refine ⟨49126527419066636217151441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65502036558755514956201921 49126527419066636217151441)
          ·
            refine ⟨36844895564299977162863581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49126527419066636217151441 36844895564299977162863581)
            ·
              refine ⟨13816835836612491436073843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36844895564299977162863581 13816835836612491436073843)
              ·
                refine ⟨20725253754918737154110765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13816835836612491436073843 20725253754918737154110765)
                ·
                  refine ⟨7771970158094526432791537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20725253754918737154110765 7771970158094526432791537)
                  ·
                    refine ⟨5828977618570894824593653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7771970158094526432791537 5828977618570894824593653)
                    ·
                      refine ⟨546466651741021389805655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5828977618570894824593653 546466651741021389805655)
                      ·
                        rfl

theorem cell23_1064240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_1064240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064240 prefixEnd_1064240 := by exact prefixLift 1064240
  have htrace : WordTrace (prefixWord ++ tailWord_1064240) baseStart_1064240 baseEnd_1064240 := by
    simpa [prefixWord, tailWord_1064240, baseEnd_1064240] using wordTrace_append hprefix tailTrace_1064240
  have hstable : (prefixWord ++ tailWord_1064240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064240).length < 2 ^ (prefixWord ++ tailWord_1064240).sum := by decide
  have hdescent : baseEnd_1064240 < baseStart_1064240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064244 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_1064244 : Nat := 118140960795 + 1064244 * 2 ^ 59
def prefixEnd_1064244 : Nat := 4983230072969 + 3 ^ 40 * 1064244 * 2
def baseEnd_1064244 : Nat := 546468705663639374155637

theorem tailTrace_1064244 : CollatzResearch.WordTrace tailWord_1064244 prefixEnd_1064244 546468705663639374155637 := by
  unfold tailWord_1064244
  simp only [CollatzResearch.WordTrace]
  refine ⟨19408083778216610624891893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25877445037622147499855857 19408083778216610624891893)
  ·
    refine ⟨1819507854207807246083615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19408083778216610624891893 1819507854207807246083615)
    ·
      refine ⟨2729261781311710869125423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1819507854207807246083615 2729261781311710869125423)
      ·
        refine ⟨4093892671967566303688135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2729261781311710869125423 4093892671967566303688135)
        ·
          refine ⟨6140839007951349455532203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4093892671967566303688135 6140839007951349455532203)
          ·
            refine ⟨9211258511927024183298305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6140839007951349455532203 9211258511927024183298305)
            ·
              refine ⟨6908443883945268137473729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9211258511927024183298305 6908443883945268137473729)
              ·
                refine ⟨5181332912958951103105297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6908443883945268137473729 5181332912958951103105297)
                ·
                  refine ⟨3885999684719213327328973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5181332912958951103105297 3885999684719213327328973)
                  ·
                    refine ⟨1457249881769704997748365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3885999684719213327328973 1457249881769704997748365)
                    ·
                      refine ⟨546468705663639374155637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1457249881769704997748365 546468705663639374155637)
                      ·
                        rfl

theorem cell23_1064244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_1064244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064244 prefixEnd_1064244 := by exact prefixLift 1064244
  have htrace : WordTrace (prefixWord ++ tailWord_1064244) baseStart_1064244 baseEnd_1064244 := by
    simpa [prefixWord, tailWord_1064244, baseEnd_1064244] using wordTrace_append hprefix tailTrace_1064244
  have hstable : (prefixWord ++ tailWord_1064244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064244).length < 2 ^ (prefixWord ++ tailWord_1064244).sum := by decide
  have hdescent : baseEnd_1064244 < baseStart_1064244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064254 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_1064254 : Nat := 118140960795 + 1064254 * 2 ^ 59
def prefixEnd_1064254 : Nat := 4983230072969 + 3 ^ 40 * 1064254 * 2
def baseEnd_1064254 : Nat := 546473840470184335030591

theorem tailTrace_1064254 : CollatzResearch.WordTrace tailWord_1064254 prefixEnd_1064254 546473840470184335030591 := by
  unfold tailWord_1064254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4852066535799624119705977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25877688190931328638431877 4852066535799624119705977)
  ·
    refine ⟨3639049901849718089779483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4852066535799624119705977 3639049901849718089779483)
    ·
      refine ⟨5458574852774577134669225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3639049901849718089779483 5458574852774577134669225)
      ·
        refine ⟨4093931139580932851001919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5458574852774577134669225 4093931139580932851001919)
        ·
          refine ⟨6140896709371399276502879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4093931139580932851001919 6140896709371399276502879)
          ·
            refine ⟨9211345064057098914754319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6140896709371399276502879 9211345064057098914754319)
            ·
              refine ⟨13817017596085648372131479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9211345064057098914754319 13817017596085648372131479)
              ·
                refine ⟨20725526394128472558197219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13817017596085648372131479 20725526394128472558197219)
                ·
                  refine ⟨31088289591192708837295829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20725526394128472558197219 31088289591192708837295829)
                  ·
                    refine ⟨728631787293579113374121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31088289591192708837295829 728631787293579113374121)
                    ·
                      refine ⟨546473840470184335030591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728631787293579113374121 546473840470184335030591)
                      ·
                        rfl

theorem cell23_1064254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_1064254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064254 prefixEnd_1064254 := by exact prefixLift 1064254
  have htrace : WordTrace (prefixWord ++ tailWord_1064254) baseStart_1064254 baseEnd_1064254 := by
    simpa [prefixWord, tailWord_1064254, baseEnd_1064254] using wordTrace_append hprefix tailTrace_1064254
  have hstable : (prefixWord ++ tailWord_1064254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064254).length < 2 ^ (prefixWord ++ tailWord_1064254).sum := by decide
  have hdescent : baseEnd_1064254 < baseStart_1064254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064285 : List Nat := [1, 4, 5, 1, 1, 1, 2, 3, 5]
def baseStart_1064285 : Nat := 118140960795 + 1064285 * 2 ^ 59
def prefixEnd_1064285 : Nat := 4983230072969 + 3 ^ 40 * 1064285 * 2
def baseEnd_1064285 : Nat := 60721084263385968193661

theorem tailTrace_1064285 : CollatzResearch.WordTrace tailWord_1064285 prefixEnd_1064285 60721084263385968193661 := by
  unfold tailWord_1064285
  simp only [CollatzResearch.WordTrace]
  refine ⟨38817662949284685252026309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25878441966189790168017539 38817662949284685252026309)
  ·
    refine ⟨7278311802990878484754933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38817662949284685252026309 7278311802990878484754933)
    ·
      refine ⟨682341731530394857945775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7278311802990878484754933 682341731530394857945775)
      ·
        refine ⟨1023512597295592286918663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 682341731530394857945775 1023512597295592286918663)
        ·
          refine ⟨1535268895943388430377995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023512597295592286918663 1535268895943388430377995)
          ·
            refine ⟨2302903343915082645566993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535268895943388430377995 2302903343915082645566993)
            ·
              refine ⟨1727177507936311984175245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2302903343915082645566993 1727177507936311984175245)
              ·
                refine ⟨647691565476116994065717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1727177507936311984175245 647691565476116994065717)
                ·
                  refine ⟨60721084263385968193661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 647691565476116994065717 60721084263385968193661)
                  ·
                    rfl

theorem cell23_1064285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_1064285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064285 prefixEnd_1064285 := by exact prefixLift 1064285
  have htrace : WordTrace (prefixWord ++ tailWord_1064285) baseStart_1064285 baseEnd_1064285 := by
    simpa [prefixWord, tailWord_1064285, baseEnd_1064285] using wordTrace_append hprefix tailTrace_1064285
  have hstable : (prefixWord ++ tailWord_1064285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064285).length < 2 ^ (prefixWord ++ tailWord_1064285).sum := by decide
  have hdescent : baseEnd_1064285 < baseStart_1064285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064387 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 6]
def baseStart_1064387 : Nat := 118140960795 + 1064387 * 2 ^ 59
def prefixEnd_1064387 : Nat := 4983230072969 + 3 ^ 40 * 1064387 * 2
def baseEnd_1064387 : Nat := 546542133397232314667479

theorem tailTrace_1064387 : CollatzResearch.WordTrace tailWord_1064387 prefixEnd_1064387 546542133397232314667479 := by
  unfold tailWord_1064387
  simp only [CollatzResearch.WordTrace]
  refine ⟨38821383194915156672239415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25880922129943437781492943 38821383194915156672239415)
  ·
    refine ⟨58232074792372735008359123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38821383194915156672239415 58232074792372735008359123)
    ·
      refine ⟨87348112188559102512538685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58232074792372735008359123 87348112188559102512538685)
      ·
        refine ⟨32755542070709663442202007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87348112188559102512538685 32755542070709663442202007)
        ·
          refine ⟨49133313106064495163303011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32755542070709663442202007 49133313106064495163303011)
          ·
            refine ⟨73699969659096742744954517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49133313106064495163303011 73699969659096742744954517)
            ·
              refine ⟨3454686077770159816169743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73699969659096742744954517 3454686077770159816169743)
              ·
                refine ⟨5182029116655239724254615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454686077770159816169743 5182029116655239724254615)
                ·
                  refine ⟨7773043674982859586381923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5182029116655239724254615 7773043674982859586381923)
                  ·
                    refine ⟨11659565512474289379572885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7773043674982859586381923 11659565512474289379572885)
                    ·
                      refine ⟨546542133397232314667479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11659565512474289379572885 546542133397232314667479)
                      ·
                        rfl

theorem cell23_1064387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_1064387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064387 prefixEnd_1064387 := by exact prefixLift 1064387
  have htrace : WordTrace (prefixWord ++ tailWord_1064387) baseStart_1064387 baseEnd_1064387 := by
    simpa [prefixWord, tailWord_1064387, baseEnd_1064387] using wordTrace_append hprefix tailTrace_1064387
  have hstable : (prefixWord ++ tailWord_1064387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064387).length < 2 ^ (prefixWord ++ tailWord_1064387).sum := by decide
  have hdescent : baseEnd_1064387 < baseStart_1064387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064388 : List Nat := [2, 3, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_1064388 : Nat := 118140960795 + 1064388 * 2 ^ 59
def prefixEnd_1064388 : Nat := 4983230072969 + 3 ^ 40 * 1064388 * 2
def baseEnd_1064388 : Nat := 182180882292628936918325

theorem tailTrace_1064388 : CollatzResearch.WordTrace tailWord_1064388 prefixEnd_1064388 182180882292628936918325 := by
  unfold tailWord_1064388
  simp only [CollatzResearch.WordTrace]
  refine ⟨19410709833955766921512909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25880946445274355895350545 19410709833955766921512909)
  ·
    refine ⟨7279016187733412595567341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19410709833955766921512909 7279016187733412595567341)
    ·
      refine ⟨2729631070400029723337753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7279016187733412595567341 2729631070400029723337753)
      ·
        refine ⟨2047223302800022292503315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2729631070400029723337753 2047223302800022292503315)
        ·
          refine ⟨3070834954200033438754973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2047223302800022292503315 3070834954200033438754973)
          ·
            refine ⟨1151563107825012539533115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3070834954200033438754973 1151563107825012539533115)
            ·
              refine ⟨1727344661737518809299673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151563107825012539533115 1727344661737518809299673)
              ·
                refine ⟨1295508496303139106974755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1727344661737518809299673 1295508496303139106974755)
                ·
                  refine ⟨1943262744454708660462133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295508496303139106974755 1943262744454708660462133)
                  ·
                    refine ⟨182180882292628936918325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1943262744454708660462133 182180882292628936918325)
                    ·
                      rfl

theorem cell23_1064388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_1064388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064388 prefixEnd_1064388 := by exact prefixLift 1064388
  have htrace : WordTrace (prefixWord ++ tailWord_1064388) baseStart_1064388 baseEnd_1064388 := by
    simpa [prefixWord, tailWord_1064388, baseEnd_1064388] using wordTrace_append hprefix tailTrace_1064388
  have hstable : (prefixWord ++ tailWord_1064388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064388).length < 2 ^ (prefixWord ++ tailWord_1064388).sum := by decide
  have hdescent : baseEnd_1064388 < baseStart_1064388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064391 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 5, 2, 2]
def baseStart_1064391 : Nat := 118140960795 + 1064391 * 2 ^ 59
def prefixEnd_1064391 : Nat := 4983230072969 + 3 ^ 40 * 1064391 * 2
def baseEnd_1064391 : Nat := 546544187319850299017461

theorem tailTrace_1064391 : CollatzResearch.WordTrace tailWord_1064391 prefixEnd_1064391 546544187319850299017461 := by
  unfold tailWord_1064391
  simp only [CollatzResearch.WordTrace]
  refine ⟨38821529086900665355385027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25881019391267110236923351 38821529086900665355385027)
  ·
    refine ⟨58232293630350998033077541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38821529086900665355385027 58232293630350998033077541)
    ·
      refine ⟨10918555055690812131202039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58232293630350998033077541 10918555055690812131202039)
      ·
        refine ⟨16377832583536218196803059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10918555055690812131202039 16377832583536218196803059)
        ·
          refine ⟨24566748875304327295204589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16377832583536218196803059 24566748875304327295204589)
          ·
            refine ⟨9212530828239122735701721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24566748875304327295204589 9212530828239122735701721)
            ·
              refine ⟨6909398121179342051776291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9212530828239122735701721 6909398121179342051776291)
              ·
                refine ⟨10364097181769013077664437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6909398121179342051776291 10364097181769013077664437)
                ·
                  refine ⟨971634110790844976031041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10364097181769013077664437 971634110790844976031041)
                  ·
                    refine ⟨728725583093133732023281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 971634110790844976031041 728725583093133732023281)
                    ·
                      refine ⟨546544187319850299017461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728725583093133732023281 546544187319850299017461)
                      ·
                        rfl

theorem cell23_1064391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_1064391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064391 prefixEnd_1064391 := by exact prefixLift 1064391
  have htrace : WordTrace (prefixWord ++ tailWord_1064391) baseStart_1064391 baseEnd_1064391 := by
    simpa [prefixWord, tailWord_1064391, baseEnd_1064391] using wordTrace_append hprefix tailTrace_1064391
  have hstable : (prefixWord ++ tailWord_1064391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064391).length < 2 ^ (prefixWord ++ tailWord_1064391).sum := by decide
  have hdescent : baseEnd_1064391 < baseStart_1064391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064424 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_1064424 : Nat := 118140960795 + 1064424 * 2 ^ 59
def prefixEnd_1064424 : Nat := 4983230072969 + 3 ^ 40 * 1064424 * 2
def baseEnd_1064424 : Nat := 546561132181448669904809

theorem tailTrace_1064424 : CollatzResearch.WordTrace tailWord_1064424 prefixEnd_1064424 546561132181448669904809 := by
  unfold tailWord_1064424
  simp only [CollatzResearch.WordTrace]
  refine ⟨19411366347890555995668163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25881821797187407994224217 19411366347890555995668163)
  ·
    refine ⟨29117049521835833993502245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19411366347890555995668163 29117049521835833993502245)
    ·
      refine ⟨5459446785344218873781671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29117049521835833993502245 5459446785344218873781671)
      ·
        refine ⟨8189170178016328310672507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5459446785344218873781671 8189170178016328310672507)
        ·
          refine ⟨12283755267024492466008761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8189170178016328310672507 12283755267024492466008761)
          ·
            refine ⟨9212816450268369349506571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12283755267024492466008761 9212816450268369349506571)
            ·
              refine ⟨13819224675402554024259857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9212816450268369349506571 13819224675402554024259857)
              ·
                refine ⟨10364418506551915518194893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13819224675402554024259857 10364418506551915518194893)
                ·
                  refine ⟨3886656939956968319323085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10364418506551915518194893 3886656939956968319323085)
                  ·
                    refine ⟨1457496352483863119746157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3886656939956968319323085 1457496352483863119746157)
                    ·
                      refine ⟨546561132181448669904809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1457496352483863119746157 546561132181448669904809)
                      ·
                        rfl

theorem cell23_1064424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_1064424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064424 prefixEnd_1064424 := by exact prefixLift 1064424
  have htrace : WordTrace (prefixWord ++ tailWord_1064424) baseStart_1064424 baseEnd_1064424 := by
    simpa [prefixWord, tailWord_1064424, baseEnd_1064424] using wordTrace_append hprefix tailTrace_1064424
  have hstable : (prefixWord ++ tailWord_1064424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064424).length < 2 ^ (prefixWord ++ tailWord_1064424).sum := by decide
  have hdescent : baseEnd_1064424 < baseStart_1064424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064457 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 1, 8]
def baseStart_1064457 : Nat := 118140960795 + 1064457 * 2 ^ 59
def prefixEnd_1064457 : Nat := 4983230072969 + 3 ^ 40 * 1064457 * 2
def baseEnd_1064457 : Nat := 182192692347682346930719

theorem tailTrace_1064457 : CollatzResearch.WordTrace tailWord_1064457 prefixEnd_1064457 182192692347682346930719 := by
  unfold tailWord_1064457
  simp only [CollatzResearch.WordTrace]
  refine ⟨38823936304661558627287625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25882624203107705751525083 38823936304661558627287625)
  ·
    refine ⟨29117952228496168970465719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38823936304661558627287625 29117952228496168970465719)
    ·
      refine ⟨43676928342744253455698579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29117952228496168970465719 43676928342744253455698579)
      ·
        refine ⟨65515392514116380183547869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43676928342744253455698579 65515392514116380183547869)
        ·
          refine ⟨24568272192793642568830451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65515392514116380183547869 24568272192793642568830451)
          ·
            refine ⟨36852408289190463853245677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24568272192793642568830451 36852408289190463853245677)
            ·
              refine ⟨13819653108446423944967129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36852408289190463853245677 13819653108446423944967129)
              ·
                refine ⟨10364739831334817958725347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13819653108446423944967129 10364739831334817958725347)
                ·
                  refine ⟨15547109747002226938088021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10364739831334817958725347 15547109747002226938088021)
                  ·
                    refine ⟨182192692347682346930719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15547109747002226938088021 182192692347682346930719)
                    ·
                      rfl

theorem cell23_1064457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_1064457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064457 prefixEnd_1064457 := by exact prefixLift 1064457
  have htrace : WordTrace (prefixWord ++ tailWord_1064457) baseStart_1064457 baseEnd_1064457 := by
    simpa [prefixWord, tailWord_1064457, baseEnd_1064457] using wordTrace_append hprefix tailTrace_1064457
  have hstable : (prefixWord ++ tailWord_1064457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064457).length < 2 ^ (prefixWord ++ tailWord_1064457).sum := by decide
  have hdescent : baseEnd_1064457 < baseStart_1064457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064462 : List Nat := [4, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3]
def baseStart_1064462 : Nat := 118140960795 + 1064462 * 2 ^ 59
def prefixEnd_1064462 : Nat := 4983230072969 + 3 ^ 40 * 1064462 * 2
def baseEnd_1064462 : Nat := 546580644446319521229635

theorem tailTrace_1064462 : CollatzResearch.WordTrace tailWord_1064462 prefixEnd_1064462 546580644446319521229635 := by
  unfold tailWord_1064462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4853014833705430560152455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25882745779762296320813093 4853014833705430560152455)
  ·
    refine ⟨7279522250558145840228683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4853014833705430560152455 7279522250558145840228683)
    ·
      refine ⟨10919283375837218760343025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7279522250558145840228683 10919283375837218760343025)
      ·
        refine ⟨8189462531877914070257269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10919283375837218760343025 8189462531877914070257269)
        ·
          refine ⟨767762112363554444086619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8189462531877914070257269 767762112363554444086619)
          ·
            refine ⟨1151643168545331666129929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 767762112363554444086619 1151643168545331666129929)
            ·
              refine ⟨863732376408998749597447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151643168545331666129929 863732376408998749597447)
              ·
                refine ⟨1295598564613498124396171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863732376408998749597447 1295598564613498124396171)
                ·
                  refine ⟨1943397846920247186594257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295598564613498124396171 1943397846920247186594257)
                  ·
                    refine ⟨1457548385190185389945693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1943397846920247186594257 1457548385190185389945693)
                    ·
                      refine ⟨546580644446319521229635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1457548385190185389945693 546580644446319521229635)
                      ·
                        rfl

theorem cell23_1064462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_1064462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064462 prefixEnd_1064462 := by exact prefixLift 1064462
  have htrace : WordTrace (prefixWord ++ tailWord_1064462) baseStart_1064462 baseEnd_1064462 := by
    simpa [prefixWord, tailWord_1064462, baseEnd_1064462] using wordTrace_append hprefix tailTrace_1064462
  have hstable : (prefixWord ++ tailWord_1064462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064462).length < 2 ^ (prefixWord ++ tailWord_1064462).sum := by decide
  have hdescent : baseEnd_1064462 < baseStart_1064462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064502 : List Nat := [5, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_1064502 : Nat := 118140960795 + 1064502 * 2 ^ 59
def prefixEnd_1064502 : Nat := 4983230072969 + 3 ^ 40 * 1064502 * 2
def baseEnd_1064502 : Nat := 546601183672499364729451

theorem tailTrace_1064502 : CollatzResearch.WordTrace tailWord_1064502 prefixEnd_1064502 546601183672499364729451 := by
  unfold tailWord_1064502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2426598599343658207042235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25883718392999020875117173 2426598599343658207042235)
  ·
    refine ⟨3639897899015487310563353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2426598599343658207042235 3639897899015487310563353)
    ·
      refine ⟨2729923424261615482922515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3639897899015487310563353 2729923424261615482922515)
      ·
        refine ⟨4094885136392423224383773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2729923424261615482922515 4094885136392423224383773)
        ·
          refine ⟨1535581926147158709143915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4094885136392423224383773 1535581926147158709143915)
          ·
            refine ⟨2303372889220738063715873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535581926147158709143915 2303372889220738063715873)
            ·
              refine ⟨1727529666915553547786905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2303372889220738063715873 1727529666915553547786905)
              ·
                refine ⟨1295647250186665160840179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1727529666915553547786905 1295647250186665160840179)
                ·
                  refine ⟨1943470875279997741260269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295647250186665160840179 1943470875279997741260269)
                  ·
                    refine ⟨728801578229999152972601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1943470875279997741260269 728801578229999152972601)
                    ·
                      refine ⟨546601183672499364729451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728801578229999152972601 546601183672499364729451)
                      ·
                        rfl

theorem cell23_1064502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_1064502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064502 prefixEnd_1064502 := by exact prefixLift 1064502
  have htrace : WordTrace (prefixWord ++ tailWord_1064502) baseStart_1064502 baseEnd_1064502 := by
    simpa [prefixWord, tailWord_1064502, baseEnd_1064502] using wordTrace_append hprefix tailTrace_1064502
  have hstable : (prefixWord ++ tailWord_1064502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064502).length < 2 ^ (prefixWord ++ tailWord_1064502).sum := by decide
  have hdescent : baseEnd_1064502 < baseStart_1064502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064504 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 7]
def baseStart_1064504 : Nat := 118140960795 + 1064504 * 2 ^ 59
def prefixEnd_1064504 : Nat := 4983230072969 + 3 ^ 40 * 1064504 * 2
def baseEnd_1064504 : Nat := 60733578959312039656049

theorem tailTrace_1064504 : CollatzResearch.WordTrace tailWord_1064504 prefixEnd_1064504 60733578959312039656049 := by
  unfold tailWord_1064504
  simp only [CollatzResearch.WordTrace]
  refine ⟨19412825267745642827124283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25883767023660857102832377 19412825267745642827124283)
  ·
    refine ⟨29119237901618464240686425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19412825267745642827124283 29119237901618464240686425)
    ·
      refine ⟨21839428426213848180514819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29119237901618464240686425 21839428426213848180514819)
      ·
        refine ⟨32759142639320772270772229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21839428426213848180514819 32759142639320772270772229)
        ·
          refine ⟨6142339244872644800769793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32759142639320772270772229 6142339244872644800769793)
          ·
            refine ⟨4606754433654483600577345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6142339244872644800769793 4606754433654483600577345)
            ·
              refine ⟨3455065825240862700433009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4606754433654483600577345 3455065825240862700433009)
              ·
                refine ⟨2591299368930647025324757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3455065825240862700433009 2591299368930647025324757)
                ·
                  refine ⟨60733578959312039656049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2591299368930647025324757 60733578959312039656049)
                  ·
                    rfl

theorem cell23_1064504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 7].length) (baseStart_1064504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064504 prefixEnd_1064504 := by exact prefixLift 1064504
  have htrace : WordTrace (prefixWord ++ tailWord_1064504) baseStart_1064504 baseEnd_1064504 := by
    simpa [prefixWord, tailWord_1064504, baseEnd_1064504] using wordTrace_append hprefix tailTrace_1064504
  have hstable : (prefixWord ++ tailWord_1064504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064504).length < 2 ^ (prefixWord ++ tailWord_1064504).sum := by decide
  have hdescent : baseEnd_1064504 < baseStart_1064504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064571 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 4]
def baseStart_1064571 : Nat := 118140960795 + 1064571 * 2 ^ 59
def prefixEnd_1064571 : Nat := 4983230072969 + 3 ^ 40 * 1064571 * 2
def baseEnd_1064571 : Nat := 546636613837659594766633

theorem tailTrace_1064571 : CollatzResearch.WordTrace tailWord_1064571 prefixEnd_1064571 546636613837659594766633 := by
  unfold tailWord_1064571
  simp only [CollatzResearch.WordTrace]
  refine ⟨38828094226248556096937567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25885396150832370731291711 38828094226248556096937567)
  ·
    refine ⟨58242141339372834145406351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38828094226248556096937567 58242141339372834145406351)
    ·
      refine ⟨87363212009059251218109527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58242141339372834145406351 87363212009059251218109527)
      ·
        refine ⟨131044818013588876827164291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87363212009059251218109527 131044818013588876827164291)
        ·
          refine ⟨196567227020383315240746437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131044818013588876827164291 196567227020383315240746437)
          ·
            refine ⟨36856355066321871607639957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196567227020383315240746437 36856355066321871607639957)
            ·
              refine ⟨1727641643733837731608123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36856355066321871607639957 1727641643733837731608123)
              ·
                refine ⟨2591462465600756597412185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727641643733837731608123 2591462465600756597412185)
                ·
                  refine ⟨1943596849200567448059139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2591462465600756597412185 1943596849200567448059139)
                  ·
                    refine ⟨2915395273800851172088709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1943596849200567448059139 2915395273800851172088709)
                    ·
                      refine ⟨546636613837659594766633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2915395273800851172088709 546636613837659594766633)
                      ·
                        rfl

theorem cell23_1064571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 4].length) (baseStart_1064571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064571 prefixEnd_1064571 := by exact prefixLift 1064571
  have htrace : WordTrace (prefixWord ++ tailWord_1064571) baseStart_1064571 baseEnd_1064571 := by
    simpa [prefixWord, tailWord_1064571, baseEnd_1064571] using wordTrace_append hprefix tailTrace_1064571
  have hstable : (prefixWord ++ tailWord_1064571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064571).length < 2 ^ (prefixWord ++ tailWord_1064571).sum := by decide
  have hdescent : baseEnd_1064571 < baseStart_1064571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064622 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1064622 : Nat := 118140960795 + 1064622 * 2 ^ 59
def prefixEnd_1064622 : Nat := 4983230072969 + 3 ^ 40 * 1064622 * 2
def baseEnd_1064622 : Nat := 546662801351038895228899

theorem tailTrace_1064622 : CollatzResearch.WordTrace tailWord_1064622 prefixEnd_1064622 546662801351038895228899 := by
  unfold tailWord_1064622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4853744293632973975880515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25886636232709194538029413 4853744293632973975880515)
  ·
    refine ⟨7280616440449460963820773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4853744293632973975880515 7280616440449460963820773)
    ·
      refine ⟨1365115582584273930716395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7280616440449460963820773 1365115582584273930716395)
      ·
        refine ⟨2047673373876410896074593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1365115582584273930716395 2047673373876410896074593)
        ·
          refine ⟨1535755030407308172055945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2047673373876410896074593 1535755030407308172055945)
          ·
            refine ⟨1151816272805481129041959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1535755030407308172055945 1151816272805481129041959)
            ·
              refine ⟨1727724409208221693562939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1151816272805481129041959 1727724409208221693562939)
              ·
                refine ⟨2591586613812332540344409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727724409208221693562939 2591586613812332540344409)
                ·
                  refine ⟨1943689960359249405258307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2591586613812332540344409 1943689960359249405258307)
                  ·
                    refine ⟨2915534940538874107887461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1943689960359249405258307 2915534940538874107887461)
                    ·
                      refine ⟨546662801351038895228899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2915534940538874107887461 546662801351038895228899)
                      ·
                        rfl

theorem cell23_1064622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1064622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064622 prefixEnd_1064622 := by exact prefixLift 1064622
  have htrace : WordTrace (prefixWord ++ tailWord_1064622) baseStart_1064622 baseEnd_1064622 := by
    simpa [prefixWord, tailWord_1064622, baseEnd_1064622] using wordTrace_append hprefix tailTrace_1064622
  have hstable : (prefixWord ++ tailWord_1064622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064622).length < 2 ^ (prefixWord ++ tailWord_1064622).sum := by decide
  have hdescent : baseEnd_1064622 < baseStart_1064622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064648 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 4, 3, 2]
def baseStart_1064648 : Nat := 118140960795 + 1064648 * 2 ^ 59
def prefixEnd_1064648 : Nat := 4983230072969 + 3 ^ 40 * 1064648 * 2
def baseEnd_1064648 : Nat := 546676151848055793503779

theorem tailTrace_1064648 : CollatzResearch.WordTrace tailWord_1064648 prefixEnd_1064648 546676151848055793503779 := by
  unfold tailWord_1064648
  simp only [CollatzResearch.WordTrace]
  refine ⟨19415451323484799123745299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25887268431313065498327065 19415451323484799123745299)
  ·
    refine ⟨29123176985227198685617949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19415451323484799123745299 29123176985227198685617949)
    ·
      refine ⟨10921191369460199507106731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29123176985227198685617949 10921191369460199507106731)
      ·
        refine ⟨16381787054190299260660097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10921191369460199507106731 16381787054190299260660097)
        ·
          refine ⟨12286340290642724445495073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16381787054190299260660097 12286340290642724445495073)
          ·
            refine ⟨9214755217982043334121305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12286340290642724445495073 9214755217982043334121305)
            ·
              refine ⟨6911066413486532500590979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9214755217982043334121305 6911066413486532500590979)
              ·
                refine ⟨10366599620229798750886469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6911066413486532500590979 10366599620229798750886469)
                ·
                  refine ⟨1943737428793087265791213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10366599620229798750886469 1943737428793087265791213)
                  ·
                    refine ⟨728901535797407724671705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1943737428793087265791213 728901535797407724671705)
                    ·
                      refine ⟨546676151848055793503779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728901535797407724671705 546676151848055793503779)
                      ·
                        rfl

theorem cell23_1064648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_1064648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064648 prefixEnd_1064648 := by exact prefixLift 1064648
  have htrace : WordTrace (prefixWord ++ tailWord_1064648) baseStart_1064648 baseEnd_1064648 := by
    simpa [prefixWord, tailWord_1064648, baseEnd_1064648] using wordTrace_append hprefix tailTrace_1064648
  have hstable : (prefixWord ++ tailWord_1064648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064648).length < 2 ^ (prefixWord ++ tailWord_1064648).sum := by decide
  have hdescent : baseEnd_1064648 < baseStart_1064648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064675 : List Nat := [1, 1, 1, 7, 2, 1, 2, 2, 1, 5]
def baseStart_1064675 : Nat := 118140960795 + 1064675 * 2 ^ 59
def prefixEnd_1064675 : Nat := 4983230072969 + 3 ^ 40 * 1064675 * 2
def baseEnd_1064675 : Nat := 182230005275242395955385

theorem tailTrace_1064675 : CollatzResearch.WordTrace tailWord_1064675 prefixEnd_1064675 182230005275242395955385 := by
  unfold tailWord_1064675
  simp only [CollatzResearch.WordTrace]
  refine ⟨38831887417871781858723479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25887924945247854572482319 38831887417871781858723479)
  ·
    refine ⟨58247831126807672788085219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38831887417871781858723479 58247831126807672788085219)
    ·
      refine ⟨87371746690211509182127829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58247831126807672788085219 87371746690211509182127829)
      ·
        refine ⟨2047775313051832246456121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 87371746690211509182127829 2047775313051832246456121)
        ·
          refine ⟨1535831484788874184842091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2047775313051832246456121 1535831484788874184842091)
          ·
            refine ⟨2303747227183311277263137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535831484788874184842091 2303747227183311277263137)
            ·
              refine ⟨1727810420387483457947353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2303747227183311277263137 1727810420387483457947353)
              ·
                refine ⟨1295857815290612593460515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1727810420387483457947353 1295857815290612593460515)
                ·
                  refine ⟨1943786722935918890190773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295857815290612593460515 1943786722935918890190773)
                  ·
                    refine ⟨182230005275242395955385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1943786722935918890190773 182230005275242395955385)
                    ·
                      rfl

theorem cell23_1064675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 5].length) (baseStart_1064675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064675 prefixEnd_1064675 := by exact prefixLift 1064675
  have htrace : WordTrace (prefixWord ++ tailWord_1064675) baseStart_1064675 baseEnd_1064675 := by
    simpa [prefixWord, tailWord_1064675, baseEnd_1064675] using wordTrace_append hprefix tailTrace_1064675
  have hstable : (prefixWord ++ tailWord_1064675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064675).length < 2 ^ (prefixWord ++ tailWord_1064675).sum := by decide
  have hdescent : baseEnd_1064675 < baseStart_1064675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064691 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 4]
def baseStart_1064691 : Nat := 118140960795 + 1064691 * 2 ^ 59
def prefixEnd_1064691 : Nat := 4983230072969 + 3 ^ 40 * 1064691 * 2
def baseEnd_1064691 : Nat := 546698231516199125266081

theorem tailTrace_1064691 : CollatzResearch.WordTrace tailWord_1064691 prefixEnd_1064691 546698231516199125266081 := by
  unfold tailWord_1064691
  simp only [CollatzResearch.WordTrace]
  refine ⟨38832470985813816591305927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25888313990542544394203951 38832470985813816591305927)
  ·
    refine ⟨58248706478720724886958891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38832470985813816591305927 58248706478720724886958891)
    ·
      refine ⟨87373059718081087330438337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58248706478720724886958891 87373059718081087330438337)
      ·
        refine ⟨65529794788560815497828753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87373059718081087330438337 65529794788560815497828753)
        ·
          refine ⟨49147346091420611623371565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65529794788560815497828753 49147346091420611623371565)
          ·
            refine ⟨18430254784282729358764337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49147346091420611623371565 18430254784282729358764337)
            ·
              refine ⟨13822691088212047019073253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18430254784282729358764337 13822691088212047019073253)
              ·
                refine ⟨2591754579039758816076235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13822691088212047019073253 2591754579039758816076235)
                ·
                  refine ⟨3887631868559638224114353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2591754579039758816076235 3887631868559638224114353)
                  ·
                    refine ⟨2915723901419728668085765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3887631868559638224114353 2915723901419728668085765)
                    ·
                      refine ⟨546698231516199125266081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2915723901419728668085765 546698231516199125266081)
                      ·
                        rfl

theorem cell23_1064691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_1064691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064691 prefixEnd_1064691 := by exact prefixLift 1064691
  have htrace : WordTrace (prefixWord ++ tailWord_1064691) baseStart_1064691 baseEnd_1064691 := by
    simpa [prefixWord, tailWord_1064691, baseEnd_1064691] using wordTrace_append hprefix tailTrace_1064691
  have hstable : (prefixWord ++ tailWord_1064691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064691).length < 2 ^ (prefixWord ++ tailWord_1064691).sum := by decide
  have hdescent : baseEnd_1064691 < baseStart_1064691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064692 : List Nat := [2, 6, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1064692 : Nat := 118140960795 + 1064692 * 2 ^ 59
def prefixEnd_1064692 : Nat := 4983230072969 + 3 ^ 40 * 1064692 * 2
def baseEnd_1064692 : Nat := 182232914998951207117859

theorem tailTrace_1064692 : CollatzResearch.WordTrace tailWord_1064692 prefixEnd_1064692 182232914998951207117859 := by
  unfold tailWord_1064692
  simp only [CollatzResearch.WordTrace]
  refine ⟨19416253729405096881046165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25888338305873462508061553 19416253729405096881046165)
  ·
    refine ⟨910136893565863916299039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19416253729405096881046165 910136893565863916299039)
    ·
      refine ⟨1365205340348795874448559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 910136893565863916299039 1365205340348795874448559)
      ·
        refine ⟨2047808010523193811672839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1365205340348795874448559 2047808010523193811672839)
        ·
          refine ⟨3071712015784790717509259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2047808010523193811672839 3071712015784790717509259)
          ·
            refine ⟨4607568023677186076263889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3071712015784790717509259 4607568023677186076263889)
            ·
              refine ⟨3455676017757889557197917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4607568023677186076263889 3455676017757889557197917)
              ·
                refine ⟨1295878506659208583949219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3455676017757889557197917 1295878506659208583949219)
                ·
                  refine ⟨1943817759988812875923829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295878506659208583949219 1943817759988812875923829)
                  ·
                    refine ⟨182232914998951207117859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1943817759988812875923829 182232914998951207117859)
                    ·
                      rfl

theorem cell23_1064692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1064692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064692 prefixEnd_1064692 := by exact prefixLift 1064692
  have htrace : WordTrace (prefixWord ++ tailWord_1064692) baseStart_1064692 baseEnd_1064692 := by
    simpa [prefixWord, tailWord_1064692, baseEnd_1064692] using wordTrace_append hprefix tailTrace_1064692
  have hstable : (prefixWord ++ tailWord_1064692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064692).length < 2 ^ (prefixWord ++ tailWord_1064692).sum := by decide
  have hdescent : baseEnd_1064692 < baseStart_1064692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064722 : List Nat := [3, 2, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1064722 : Nat := 118140960795 + 1064722 * 2 ^ 59
def prefixEnd_1064722 : Nat := 4983230072969 + 3 ^ 40 * 1064722 * 2
def baseEnd_1064722 : Nat := 182238049805496167992813

theorem tailTrace_1064722 : CollatzResearch.WordTrace tailWord_1064722 prefixEnd_1064722 182238049805496167992813 := by
  unfold tailWord_1064722
  simp only [CollatzResearch.WordTrace]
  refine ⟨9708400412175377221421105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25889067765801005923789613 9708400412175377221421105)
  ·
    refine ⟨7281300309131532916065829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9708400412175377221421105 7281300309131532916065829)
    ·
      refine ⟨1365243807962162421762343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7281300309131532916065829 1365243807962162421762343)
      ·
        refine ⟨2047865711943243632643515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1365243807962162421762343 2047865711943243632643515)
        ·
          refine ⟨3071798567914865448965273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2047865711943243632643515 3071798567914865448965273)
          ·
            refine ⟨2303848925936149086723955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3071798567914865448965273 2303848925936149086723955)
            ·
              refine ⟨3455773388904223630085933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303848925936149086723955 3455773388904223630085933)
              ·
                refine ⟨1295915020839083861282225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3455773388904223630085933 1295915020839083861282225)
                ·
                  refine ⟨971936265629312895961669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1295915020839083861282225 971936265629312895961669)
                  ·
                    refine ⟨182238049805496167992813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 971936265629312895961669 182238049805496167992813)
                    ·
                      rfl

theorem cell23_1064722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1064722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064722 prefixEnd_1064722 := by exact prefixLift 1064722
  have htrace : WordTrace (prefixWord ++ tailWord_1064722) baseStart_1064722 baseEnd_1064722 := by
    simpa [prefixWord, tailWord_1064722, baseEnd_1064722] using wordTrace_append hprefix tailTrace_1064722
  have hstable : (prefixWord ++ tailWord_1064722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064722).length < 2 ^ (prefixWord ++ tailWord_1064722).sum := by decide
  have hdescent : baseEnd_1064722 < baseStart_1064722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064762 : List Nat := [3, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3]
def baseStart_1064762 : Nat := 118140960795 + 1064762 * 2 ^ 59
def prefixEnd_1064762 : Nat := 4983230072969 + 3 ^ 40 * 1064762 * 2
def baseEnd_1064762 : Nat := 546734688642668347478255

theorem tailTrace_1064762 : CollatzResearch.WordTrace tailWord_1064762 prefixEnd_1064762 546734688642668347478255 := by
  unfold tailWord_1064762
  simp only [CollatzResearch.WordTrace]
  refine ⟨9708765142139148929285135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25890040379037730478093693 9708765142139148929285135)
  ·
    refine ⟨14563147713208723393927703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9708765142139148929285135 14563147713208723393927703)
    ·
      refine ⟨21844721569813085090891555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14563147713208723393927703 21844721569813085090891555)
      ·
        refine ⟨32767082354719627636337333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21844721569813085090891555 32767082354719627636337333)
        ·
          refine ⟨3071913970754965090906625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32767082354719627636337333 3071913970754965090906625)
          ·
            refine ⟨2303935478066223818179969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3071913970754965090906625 2303935478066223818179969)
            ·
              refine ⟨1727951608549667863634977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2303935478066223818179969 1727951608549667863634977)
              ·
                refine ⟨1295963706412250897726233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1727951608549667863634977 1295963706412250897726233)
                ·
                  refine ⟨971972779809188173294675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1295963706412250897726233 971972779809188173294675)
                  ·
                    refine ⟨1457959169713782259942013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 971972779809188173294675 1457959169713782259942013)
                    ·
                      refine ⟨546734688642668347478255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1457959169713782259942013 546734688642668347478255)
                      ·
                        rfl

theorem cell23_1064762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_1064762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064762 prefixEnd_1064762 := by exact prefixLift 1064762
  have htrace : WordTrace (prefixWord ++ tailWord_1064762) baseStart_1064762 baseEnd_1064762 := by
    simpa [prefixWord, tailWord_1064762, baseEnd_1064762] using wordTrace_append hprefix tailTrace_1064762
  have hstable : (prefixWord ++ tailWord_1064762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064762).length < 2 ^ (prefixWord ++ tailWord_1064762).sum := by decide
  have hdescent : baseEnd_1064762 < baseStart_1064762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064785 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 1, 4, 2]
def baseStart_1064785 : Nat := 118140960795 + 1064785 * 2 ^ 59
def prefixEnd_1064785 : Nat := 4983230072969 + 3 ^ 40 * 1064785 * 2
def baseEnd_1064785 : Nat := 546746498697721757490649

theorem tailTrace_1064785 : CollatzResearch.WordTrace tailWord_1064785 prefixEnd_1064785 546746498697721757490649 := by
  unfold tailWord_1064785
  simp only [CollatzResearch.WordTrace]
  refine ⟨38835899447473270645227809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25890599631648847096818539 38835899447473270645227809)
  ·
    refine ⟨29126924585604952983920857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38835899447473270645227809 29126924585604952983920857)
    ·
      refine ⟨21845193439203714737940643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29126924585604952983920857 21845193439203714737940643)
      ·
        refine ⟨32767790158805572106910965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21845193439203714737940643 32767790158805572106910965)
        ·
          refine ⟨3071980327388022385022903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32767790158805572106910965 3071980327388022385022903)
          ·
            refine ⟨4607970491082033577534355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3071980327388022385022903 4607970491082033577534355)
            ·
              refine ⟨6911955736623050366301533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4607970491082033577534355 6911955736623050366301533)
              ·
                refine ⟨2591983401233643887363075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6911955736623050366301533 2591983401233643887363075)
                ·
                  refine ⟨3887975101850465831044613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2591983401233643887363075 3887975101850465831044613)
                  ·
                    refine ⟨728995331596962343320865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3887975101850465831044613 728995331596962343320865)
                    ·
                      refine ⟨546746498697721757490649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 728995331596962343320865 546746498697721757490649)
                      ·
                        rfl

theorem cell23_1064785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 4, 2].length) (baseStart_1064785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064785 prefixEnd_1064785 := by exact prefixLift 1064785
  have htrace : WordTrace (prefixWord ++ tailWord_1064785) baseStart_1064785 baseEnd_1064785 := by
    simpa [prefixWord, tailWord_1064785, baseEnd_1064785] using wordTrace_append hprefix tailTrace_1064785
  have hstable : (prefixWord ++ tailWord_1064785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064785).length < 2 ^ (prefixWord ++ tailWord_1064785).sum := by decide
  have hdescent : baseEnd_1064785 < baseStart_1064785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064802 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_1064802 : Nat := 118140960795 + 1064802 * 2 ^ 59
def prefixEnd_1064802 : Nat := 4983230072969 + 3 ^ 40 * 1064802 * 2
def baseEnd_1064802 : Nat := 546755227868848190978071

theorem tailTrace_1064802 : CollatzResearch.WordTrace tailWord_1064802 prefixEnd_1064802 546755227868848190978071 := by
  unfold tailWord_1064802
  simp only [CollatzResearch.WordTrace]
  refine ⟨9709129872102920637149165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25891012992274455032397773 9709129872102920637149165)
  ·
    refine ⟨3640923702038595238930937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9709129872102920637149165 3640923702038595238930937)
    ·
      refine ⟨2730692776528946429198203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3640923702038595238930937 2730692776528946429198203)
      ·
        refine ⟨4096039164793419643797305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2730692776528946429198203 4096039164793419643797305)
        ·
          refine ⟨3072029373595064732847979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4096039164793419643797305 3072029373595064732847979)
          ·
            refine ⟨4608044060392597099271969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3072029373595064732847979 4608044060392597099271969)
            ·
              refine ⟨3456033045294447824453977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4608044060392597099271969 3456033045294447824453977)
              ·
                refine ⟨2592024783970835868340483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3456033045294447824453977 2592024783970835868340483)
                ·
                  refine ⟨3888037175956253802510725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2592024783970835868340483 3888037175956253802510725)
                  ·
                    refine ⟨729006970491797587970761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3888037175956253802510725 729006970491797587970761)
                    ·
                      refine ⟨546755227868848190978071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 729006970491797587970761 546755227868848190978071)
                      ·
                        rfl

theorem cell23_1064802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_1064802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064802 prefixEnd_1064802 := by exact prefixLift 1064802
  have htrace : WordTrace (prefixWord ++ tailWord_1064802) baseStart_1064802 baseEnd_1064802 := by
    simpa [prefixWord, tailWord_1064802, baseEnd_1064802] using wordTrace_append hprefix tailTrace_1064802
  have hstable : (prefixWord ++ tailWord_1064802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064802).length < 2 ^ (prefixWord ++ tailWord_1064802).sum := by decide
  have hdescent : baseEnd_1064802 < baseStart_1064802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064831 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 7]
def baseStart_1064831 : Nat := 118140960795 + 1064831 * 2 ^ 59
def prefixEnd_1064831 : Nat := 4983230072969 + 3 ^ 40 * 1064831 * 2
def baseEnd_1064831 : Nat := 546770118807828577515437

theorem tailTrace_1064831 : CollatzResearch.WordTrace tailWord_1064831 prefixEnd_1064831 546770118807828577515437 := by
  unfold tailWord_1064831
  simp only [CollatzResearch.WordTrace]
  refine ⟨38837577205306620501402347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25891718136871080334268231 38837577205306620501402347)
  ·
    refine ⟨58256365807959930752103521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38837577205306620501402347 58256365807959930752103521)
    ·
      refine ⟨43692274355969948064077641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58256365807959930752103521 43692274355969948064077641)
      ·
        refine ⟨32769205766977461048058231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43692274355969948064077641 32769205766977461048058231)
        ·
          refine ⟨49153808650466191572087347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32769205766977461048058231 49153808650466191572087347)
          ·
            refine ⟨73730712975699287358131021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49153808650466191572087347 73730712975699287358131021)
            ·
              refine ⟨27649017365887232759299133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73730712975699287358131021 27649017365887232759299133)
              ·
                refine ⟨10368381512207712284737175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27649017365887232759299133 10368381512207712284737175)
                ·
                  refine ⟨15552572268311568427105763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10368381512207712284737175 15552572268311568427105763)
                  ·
                    refine ⟨23328858402467352640658645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15552572268311568427105763 23328858402467352640658645)
                    ·
                      refine ⟨546770118807828577515437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23328858402467352640658645 546770118807828577515437)
                      ·
                        rfl

theorem cell23_1064831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_1064831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064831 prefixEnd_1064831 := by exact prefixLift 1064831
  have htrace : WordTrace (prefixWord ++ tailWord_1064831) baseStart_1064831 baseEnd_1064831 := by
    simpa [prefixWord, tailWord_1064831, baseEnd_1064831] using wordTrace_append hprefix tailTrace_1064831
  have hstable : (prefixWord ++ tailWord_1064831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064831).length < 2 ^ (prefixWord ++ tailWord_1064831).sum := by decide
  have hdescent : baseEnd_1064831 < baseStart_1064831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1064965 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 3, 1, 4]
def baseStart_1064965 : Nat := 118140960795 + 1064965 * 2 ^ 59
def prefixEnd_1064965 : Nat := 4983230072969 + 3 ^ 40 * 1064965 * 2
def baseEnd_1064965 : Nat := 546838925215531053239821

theorem tailTrace_1064965 : CollatzResearch.WordTrace tailWord_1064965 prefixEnd_1064965 546838925215531053239821 := by
  unfold tailWord_1064965
  simp only [CollatzResearch.WordTrace]
  refine ⟨38842464586821161386780349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25894976391214107591186899 38842464586821161386780349)
  ·
    refine ⟨14565924220057935520042631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38842464586821161386780349 14565924220057935520042631)
    ·
      refine ⟨21848886330086903280063947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14565924220057935520042631 21848886330086903280063947)
      ·
        refine ⟨32773329495130354920095921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21848886330086903280063947 32773329495130354920095921)
        ·
          refine ⟨24579997121347766190071941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32773329495130354920095921 24579997121347766190071941)
          ·
            refine ⟨4608749460252706160638489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24579997121347766190071941 4608749460252706160638489)
            ·
              refine ⟨3456562095189529620478867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4608749460252706160638489 3456562095189529620478867)
              ·
                refine ⟨5184843142784294430718301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3456562095189529620478867 5184843142784294430718301)
                ·
                  refine ⟨1944316178544110411519363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5184843142784294430718301 1944316178544110411519363)
                  ·
                    refine ⟨2916474267816165617279045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1944316178544110411519363 2916474267816165617279045)
                    ·
                      refine ⟨546838925215531053239821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2916474267816165617279045 546838925215531053239821)
                      ·
                        rfl

theorem cell23_1064965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_1064965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1064965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1064965 prefixEnd_1064965 := by exact prefixLift 1064965
  have htrace : WordTrace (prefixWord ++ tailWord_1064965) baseStart_1064965 baseEnd_1064965 := by
    simpa [prefixWord, tailWord_1064965, baseEnd_1064965] using wordTrace_append hprefix tailTrace_1064965
  have hstable : (prefixWord ++ tailWord_1064965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1064965).length < 2 ^ (prefixWord ++ tailWord_1064965).sum := by decide
  have hdescent : baseEnd_1064965 < baseStart_1064965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1064965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065002 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1065002 : Nat := 118140960795 + 1065002 * 2 ^ 59
def prefixEnd_1065002 : Nat := 4983230072969 + 3 ^ 40 * 1065002 * 2
def baseEnd_1065002 : Nat := 546857923999747408477151

theorem tailTrace_1065002 : CollatzResearch.WordTrace tailWord_1065002 prefixEnd_1065002 546857923999747408477151 := by
  unfold tailWord_1065002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9710953521921779176469315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25895876058458077803918173 9710953521921779176469315)
  ·
    refine ⟨14566430282882668764703973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9710953521921779176469315 14566430282882668764703973)
    ·
      refine ⟨2731205678040500393381995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14566430282882668764703973 2731205678040500393381995)
      ·
        refine ⟨4096808517060750590072993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2731205678040500393381995 4096808517060750590072993)
        ·
          refine ⟨3072606387795562942554745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4096808517060750590072993 3072606387795562942554745)
          ·
            refine ⟨2304454790846672206916059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3072606387795562942554745 2304454790846672206916059)
            ·
              refine ⟨3456682186270008310374089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2304454790846672206916059 3456682186270008310374089)
              ·
                refine ⟨2592511639702506232780567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3456682186270008310374089 2592511639702506232780567)
                ·
                  refine ⟨3888767459553759349170851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2592511639702506232780567 3888767459553759349170851)
                  ·
                    refine ⟨5833151189330639023756277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3888767459553759349170851 5833151189330639023756277)
                    ·
                      refine ⟨546857923999747408477151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5833151189330639023756277 546857923999747408477151)
                      ·
                        rfl

theorem cell23_1065002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1065002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065002 prefixEnd_1065002 := by exact prefixLift 1065002
  have htrace : WordTrace (prefixWord ++ tailWord_1065002) baseStart_1065002 baseEnd_1065002 := by
    simpa [prefixWord, tailWord_1065002, baseEnd_1065002] using wordTrace_append hprefix tailTrace_1065002
  have hstable : (prefixWord ++ tailWord_1065002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065002).length < 2 ^ (prefixWord ++ tailWord_1065002).sum := by decide
  have hdescent : baseEnd_1065002 < baseStart_1065002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065009 : List Nat := [1, 2, 2, 3, 1, 4, 3, 1, 2, 4]
def baseStart_1065009 : Nat := 118140960795 + 1065009 * 2 ^ 59
def prefixEnd_1065009 : Nat := 4983230072969 + 3 ^ 40 * 1065009 * 2
def baseEnd_1065009 : Nat := 182287172788109627029873

theorem tailTrace_1065009 : CollatzResearch.WordTrace tailWord_1065009 prefixEnd_1065009 182287172788109627029873 := by
  unfold tailWord_1065009
  simp only [CollatzResearch.WordTrace]
  refine ⟨38844069398661756901382081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25896046265774504600921387 38844069398661756901382081)
  ·
    refine ⟨29133052048996317676036561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38844069398661756901382081 29133052048996317676036561)
    ·
      refine ⟨21849789036747238257027421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29133052048996317676036561 21849789036747238257027421)
      ·
        refine ⟨8193670888780214346385283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21849789036747238257027421 8193670888780214346385283)
        ·
          refine ⟨12290506333170321519577925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8193670888780214346385283 12290506333170321519577925)
          ·
            refine ⟨2304469937469435284920861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12290506333170321519577925 2304469937469435284920861)
            ·
              refine ⟨864176226551038231845323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2304469937469435284920861 864176226551038231845323)
              ·
                refine ⟨1296264339826557347767985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 864176226551038231845323 1296264339826557347767985)
                ·
                  refine ⟨972198254869918010825989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1296264339826557347767985 972198254869918010825989)
                  ·
                    refine ⟨182287172788109627029873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 972198254869918010825989 182287172788109627029873)
                    ·
                      rfl

theorem cell23_1065009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_1065009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065009 prefixEnd_1065009 := by exact prefixLift 1065009
  have htrace : WordTrace (prefixWord ++ tailWord_1065009) baseStart_1065009 baseEnd_1065009 := by
    simpa [prefixWord, tailWord_1065009, baseEnd_1065009] using wordTrace_append hprefix tailTrace_1065009
  have hstable : (prefixWord ++ tailWord_1065009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065009).length < 2 ^ (prefixWord ++ tailWord_1065009).sum := by decide
  have hdescent : baseEnd_1065009 < baseStart_1065009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065022 : List Nat := [4, 2, 1, 3, 2, 1, 1, 9]
def baseStart_1065022 : Nat := 118140960795 + 1065022 * 2 ^ 59
def prefixEnd_1065022 : Nat := 4983230072969 + 3 ^ 40 * 1065022 * 2
def baseEnd_1065022 : Nat := 20254377541216197415817

theorem tailTrace_1065022 : CollatzResearch.WordTrace tailWord_1065022 prefixEnd_1065022 20254377541216197415817 := by
  unfold tailWord_1065022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4855567943451832515200665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25896362365076440081070213 4855567943451832515200665)
  ·
    refine ⟨3641675957588874386400499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4855567943451832515200665 3641675957588874386400499)
    ·
      refine ⟨5462513936383311579600749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3641675957588874386400499 5462513936383311579600749)
      ·
        refine ⟨2048442726143741842350281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5462513936383311579600749 2048442726143741842350281)
        ·
          refine ⟨1536332044607806381762711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2048442726143741842350281 1536332044607806381762711)
          ·
            refine ⟨2304498066911709572644067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1536332044607806381762711 2304498066911709572644067)
            ·
              refine ⟨3456747100367564358966101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2304498066911709572644067 3456747100367564358966101)
              ·
                refine ⟨20254377541216197415817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3456747100367564358966101 20254377541216197415817)
                ·
                  rfl

theorem cell23_1065022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_1065022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065022 prefixEnd_1065022 := by exact prefixLift 1065022
  have htrace : WordTrace (prefixWord ++ tailWord_1065022) baseStart_1065022 baseEnd_1065022 := by
    simpa [prefixWord, tailWord_1065022, baseEnd_1065022] using wordTrace_append hprefix tailTrace_1065022
  have hstable : (prefixWord ++ tailWord_1065022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065022).length < 2 ^ (prefixWord ++ tailWord_1065022).sum := by decide
  have hdescent : baseEnd_1065022 < baseStart_1065022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065066 : List Nat := [3, 1, 3, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_1065066 : Nat := 118140960795 + 1065066 * 2 ^ 59
def prefixEnd_1065066 : Nat := 4983230072969 + 3 ^ 40 * 1065066 * 2
def baseEnd_1065066 : Nat := 546890786761635158076857

theorem tailTrace_1065066 : CollatzResearch.WordTrace tailWord_1065066 prefixEnd_1065066 546890786761635158076857 := by
  unfold tailWord_1065066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9711537089863813909051763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25897432239636837090804701 9711537089863813909051763)
  ·
    refine ⟨14567305634795720863577645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9711537089863813909051763 14567305634795720863577645)
    ·
      refine ⟨5462739613048395323841617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14567305634795720863577645 5462739613048395323841617)
      ·
        refine ⟨4097054709786296492881213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5462739613048395323841617 4097054709786296492881213)
        ·
          refine ⟨1536395516169861184830455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4097054709786296492881213 1536395516169861184830455)
          ·
            refine ⟨2304593274254791777245683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1536395516169861184830455 2304593274254791777245683)
            ·
              refine ⟨3456889911382187665868525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2304593274254791777245683 3456889911382187665868525)
              ·
                refine ⟨1296333716768320374700697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3456889911382187665868525 1296333716768320374700697)
                ·
                  refine ⟨972250287576240281025523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1296333716768320374700697 972250287576240281025523)
                  ·
                    refine ⟨1458375431364360421538285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 972250287576240281025523 1458375431364360421538285)
                    ·
                      refine ⟨546890786761635158076857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1458375431364360421538285 546890786761635158076857)
                      ·
                        rfl

theorem cell23_1065066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_1065066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065066 prefixEnd_1065066 := by exact prefixLift 1065066
  have htrace : WordTrace (prefixWord ++ tailWord_1065066) baseStart_1065066 baseEnd_1065066 := by
    simpa [prefixWord, tailWord_1065066, baseEnd_1065066] using wordTrace_append hprefix tailTrace_1065066
  have hstable : (prefixWord ++ tailWord_1065066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065066).length < 2 ^ (prefixWord ++ tailWord_1065066).sum := by decide
  have hdescent : baseEnd_1065066 < baseStart_1065066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065105 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 3]
def baseStart_1065105 : Nat := 118140960795 + 1065105 * 2 ^ 59
def prefixEnd_1065105 : Nat := 4983230072969 + 3 ^ 40 * 1065105 * 2
def baseEnd_1065105 : Nat := 546910812507160505489177

theorem tailTrace_1065105 : CollatzResearch.WordTrace tailWord_1065105 prefixEnd_1065105 546910812507160505489177 := by
  unfold tailWord_1065105
  simp only [CollatzResearch.WordTrace]
  refine ⟨38847570806313965296876769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25898380537542643531251179 38847570806313965296876769)
  ·
    refine ⟨29135678104735473972657577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38847570806313965296876769 29135678104735473972657577)
    ·
      refine ⟨21851758578551605479493183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29135678104735473972657577 21851758578551605479493183)
      ·
        refine ⟨32777637867827408219239775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21851758578551605479493183 32777637867827408219239775)
        ·
          refine ⟨49166456801741112328859663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32777637867827408219239775 49166456801741112328859663)
          ·
            refine ⟨73749685202611668493289495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49166456801741112328859663 73749685202611668493289495)
            ·
              refine ⟨110624527803917502739934243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73749685202611668493289495 110624527803917502739934243)
              ·
                refine ⟨165936791705876254109901365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110624527803917502739934243 165936791705876254109901365)
                ·
                  refine ⟨15556574222425898822803253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165936791705876254109901365 15556574222425898822803253)
                  ·
                    refine ⟨1458428833352428014637805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15556574222425898822803253 1458428833352428014637805)
                    ·
                      refine ⟨546910812507160505489177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1458428833352428014637805 546910812507160505489177)
                      ·
                        rfl

theorem cell23_1065105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_1065105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065105 prefixEnd_1065105 := by exact prefixLift 1065105
  have htrace : WordTrace (prefixWord ++ tailWord_1065105) baseStart_1065105 baseEnd_1065105 := by
    simpa [prefixWord, tailWord_1065105, baseEnd_1065105] using wordTrace_append hprefix tailTrace_1065105
  have hstable : (prefixWord ++ tailWord_1065105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065105).length < 2 ^ (prefixWord ++ tailWord_1065105).sum := by decide
  have hdescent : baseEnd_1065105 < baseStart_1065105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065125 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 1, 7]
def baseStart_1065125 : Nat := 118140960795 + 1065125 * 2 ^ 59
def prefixEnd_1065125 : Nat := 4983230072969 + 3 ^ 40 * 1065125 * 2
def baseEnd_1065125 : Nat := 182307027373416809079695

theorem tailTrace_1065125 : CollatzResearch.WordTrace tailWord_1065125 prefixEnd_1065125 182307027373416809079695 := by
  unfold tailWord_1065125
  simp only [CollatzResearch.WordTrace]
  refine ⟨38848300266241508712604829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25898866844161005808403219 38848300266241508712604829)
  ·
    refine ⟨14568112599840565767226811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38848300266241508712604829 14568112599840565767226811)
    ·
      refine ⟨21852168899760848650840217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14568112599840565767226811 21852168899760848650840217)
      ·
        refine ⟨16389126674820636488130163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21852168899760848650840217 16389126674820636488130163)
        ·
          refine ⟨24583690012230954732195245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16389126674820636488130163 24583690012230954732195245)
          ·
            refine ⟨9218883754586608024573217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24583690012230954732195245 9218883754586608024573217)
            ·
              refine ⟨6914162815939956018429913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9218883754586608024573217 6914162815939956018429913)
              ·
                refine ⟨5185622111954967013822435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6914162815939956018429913 5185622111954967013822435)
                ·
                  refine ⟨7778433167932450520733653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5185622111954967013822435 7778433167932450520733653)
                  ·
                    refine ⟨182307027373416809079695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7778433167932450520733653 182307027373416809079695)
                    ·
                      rfl

theorem cell23_1065125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_1065125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065125 prefixEnd_1065125 := by exact prefixLift 1065125
  have htrace : WordTrace (prefixWord ++ tailWord_1065125) baseStart_1065125 baseEnd_1065125 := by
    simpa [prefixWord, tailWord_1065125, baseEnd_1065125] using wordTrace_append hprefix tailTrace_1065125
  have hstable : (prefixWord ++ tailWord_1065125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065125).length < 2 ^ (prefixWord ++ tailWord_1065125).sum := by decide
  have hdescent : baseEnd_1065125 < baseStart_1065125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065162 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_1065162 : Nat := 118140960795 + 1065162 * 2 ^ 59
def prefixEnd_1065162 : Nat := 4983230072969 + 3 ^ 40 * 1065162 * 2
def baseEnd_1065162 : Nat := 546940080904466782476415

theorem tailTrace_1065162 : CollatzResearch.WordTrace tailWord_1065162 prefixEnd_1065162 546940080904466782476415 := by
  unfold tailWord_1065162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9712412441776866007925435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25899766511404976021134493 9712412441776866007925435)
  ·
    refine ⟨14568618662665299011888153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9712412441776866007925435 14568618662665299011888153)
    ·
      refine ⟨10926463996998974258916115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14568618662665299011888153 10926463996998974258916115)
      ·
        refine ⟨16389695995498461388374173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10926463996998974258916115 16389695995498461388374173)
        ·
          refine ⟨6146135998311923020640315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16389695995498461388374173 6146135998311923020640315)
          ·
            refine ⟨9219203997467884530960473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6146135998311923020640315 9219203997467884530960473)
            ·
              refine ⟨6914402998100913398220355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9219203997467884530960473 6914402998100913398220355)
              ·
                refine ⟨10371604497151370097330533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6914402998100913398220355 10371604497151370097330533)
                ·
                  refine ⟨1944675843215881893249475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10371604497151370097330533 1944675843215881893249475)
                  ·
                    refine ⟨2917013764823822839874213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1944675843215881893249475 2917013764823822839874213)
                    ·
                      refine ⟨546940080904466782476415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2917013764823822839874213 546940080904466782476415)
                      ·
                        rfl

theorem cell23_1065162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_1065162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065162 prefixEnd_1065162 := by exact prefixLift 1065162
  have htrace : WordTrace (prefixWord ++ tailWord_1065162) baseStart_1065162 baseEnd_1065162 := by
    simpa [prefixWord, tailWord_1065162, baseEnd_1065162] using wordTrace_append hprefix tailTrace_1065162
  have hstable : (prefixWord ++ tailWord_1065162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065162).length < 2 ^ (prefixWord ++ tailWord_1065162).sum := by decide
  have hdescent : baseEnd_1065162 < baseStart_1065162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065175 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_1065175 : Nat := 118140960795 + 1065175 * 2 ^ 59
def prefixEnd_1065175 : Nat := 4983230072969 + 3 ^ 40 * 1065175 * 2
def baseEnd_1065175 : Nat := 546946756152975231613855

theorem tailTrace_1065175 : CollatzResearch.WordTrace tailWord_1065175 prefixEnd_1065175 546946756152975231613855 := by
  unfold tailWord_1065175
  simp only [CollatzResearch.WordTrace]
  refine ⟨38850123916060367251924979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25900082610706911501283319 38850123916060367251924979)
  ·
    refine ⟨58275185874090550877887469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38850123916060367251924979 58275185874090550877887469)
    ·
      refine ⟨21853194702783956579207801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58275185874090550877887469 21853194702783956579207801)
      ·
        refine ⟨16389896027087967434405851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21853194702783956579207801 16389896027087967434405851)
        ·
          refine ⟨24584844040631951151608777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16389896027087967434405851 24584844040631951151608777)
          ·
            refine ⟨18438633030473963363706583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24584844040631951151608777 18438633030473963363706583)
            ·
              refine ⟨27657949545710945045559875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18438633030473963363706583 27657949545710945045559875)
              ·
                refine ⟨41486924318566417568339813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27657949545710945045559875 41486924318566417568339813)
                ·
                  refine ⟨7778798309731203294063715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41486924318566417568339813 7778798309731203294063715)
                  ·
                    refine ⟨11668197464596804941095573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7778798309731203294063715 11668197464596804941095573)
                    ·
                      refine ⟨546946756152975231613855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11668197464596804941095573 546946756152975231613855)
                      ·
                        rfl

theorem cell23_1065175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_1065175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065175 prefixEnd_1065175 := by exact prefixLift 1065175
  have htrace : WordTrace (prefixWord ++ tailWord_1065175) baseStart_1065175 baseEnd_1065175 := by
    simpa [prefixWord, tailWord_1065175, baseEnd_1065175] using wordTrace_append hprefix tailTrace_1065175
  have hstable : (prefixWord ++ tailWord_1065175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065175).length < 2 ^ (prefixWord ++ tailWord_1065175).sum := by decide
  have hdescent : baseEnd_1065175 < baseStart_1065175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065189 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 3, 4]
def baseStart_1065189 : Nat := 118140960795 + 1065189 * 2 ^ 59
def prefixEnd_1065189 : Nat := 4983230072969 + 3 ^ 40 * 1065189 * 2
def baseEnd_1065189 : Nat := 182317981627379392279597

theorem tailTrace_1065189 : CollatzResearch.WordTrace tailWord_1065189 prefixEnd_1065189 182317981627379392279597 := by
  unfold tailWord_1065189
  simp only [CollatzResearch.WordTrace]
  refine ⟨38850634538009647642934621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25900423025339765095289747 38850634538009647642934621)
  ·
    refine ⟨14568987951753617866100483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38850634538009647642934621 14568987951753617866100483)
    ·
      refine ⟨21853481927630426799150725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14568987951753617866100483 21853481927630426799150725)
      ·
        refine ⟨4097527861430705024840761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21853481927630426799150725 4097527861430705024840761)
        ·
          refine ⟨3073145896073028768630571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4097527861430705024840761 3073145896073028768630571)
          ·
            refine ⟨4609718844109543152945857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3073145896073028768630571 4609718844109543152945857)
            ·
              refine ⟨3457289133082157364709393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4609718844109543152945857 3457289133082157364709393)
              ·
                refine ⟨2592966849811618023532045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3457289133082157364709393 2592966849811618023532045)
                ·
                  refine ⟨972362568679356758824517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2592966849811618023532045 972362568679356758824517)
                  ·
                    refine ⟨182317981627379392279597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 972362568679356758824517 182317981627379392279597)
                    ·
                      rfl

theorem cell23_1065189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_1065189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065189 prefixEnd_1065189 := by exact prefixLift 1065189
  have htrace : WordTrace (prefixWord ++ tailWord_1065189) baseStart_1065189 baseEnd_1065189 := by
    simpa [prefixWord, tailWord_1065189, baseEnd_1065189] using wordTrace_append hprefix tailTrace_1065189
  have hstable : (prefixWord ++ tailWord_1065189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065189).length < 2 ^ (prefixWord ++ tailWord_1065189).sum := by decide
  have hdescent : baseEnd_1065189 < baseStart_1065189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065202 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 8]
def baseStart_1065202 : Nat := 118140960795 + 1065202 * 2 ^ 59
def prefixEnd_1065202 : Nat := 4983230072969 + 3 ^ 40 * 1065202 * 2
def baseEnd_1065202 : Nat := 60773402236738513997359

theorem tailTrace_1065202 : CollatzResearch.WordTrace tailWord_1065202 prefixEnd_1065202 60773402236738513997359 := by
  unfold tailWord_1065202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9712777171740637715789465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25900739124641700575438573 9712777171740637715789465)
  ·
    refine ⟨7284582878805478286842099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9712777171740637715789465 7284582878805478286842099)
    ·
      refine ⟨10926874318208217430263149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7284582878805478286842099 10926874318208217430263149)
      ·
        refine ⟨4097577869328081536348681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10926874318208217430263149 4097577869328081536348681)
        ·
          refine ⟨3073183401996061152261511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4097577869328081536348681 3073183401996061152261511)
          ·
            refine ⟨4609775102994091728392267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3073183401996061152261511 4609775102994091728392267)
            ·
              refine ⟨6914662654491137592588401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4609775102994091728392267 6914662654491137592588401)
              ·
                refine ⟨5185996990868353194441301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6914662654491137592588401 5185996990868353194441301)
                ·
                  refine ⟨60773402236738513997359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5185996990868353194441301 60773402236738513997359)
                  ·
                    rfl

theorem cell23_1065202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_1065202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065202 prefixEnd_1065202 := by exact prefixLift 1065202
  have htrace : WordTrace (prefixWord ++ tailWord_1065202) baseStart_1065202 baseEnd_1065202 := by
    simpa [prefixWord, tailWord_1065202, baseEnd_1065202] using wordTrace_append hprefix tailTrace_1065202
  have hstable : (prefixWord ++ tailWord_1065202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065202).length < 2 ^ (prefixWord ++ tailWord_1065202).sum := by decide
  have hdescent : baseEnd_1065202 < baseStart_1065202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065223 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 3, 4]
def baseStart_1065223 : Nat := 118140960795 + 1065223 * 2 ^ 59
def prefixEnd_1065223 : Nat := 4983230072969 + 3 ^ 40 * 1065223 * 2
def baseEnd_1065223 : Nat := 182323801074797014604545

theorem tailTrace_1065223 : CollatzResearch.WordTrace tailWord_1065223 prefixEnd_1065223 182323801074797014604545 := by
  unfold tailWord_1065223
  simp only [CollatzResearch.WordTrace]
  refine ⟨38851874619886471449672323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25901249746590980966448215 38851874619886471449672323)
  ·
    refine ⟨58277811929829707174508485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38851874619886471449672323 58277811929829707174508485)
    ·
      refine ⟨10927089736843070095220341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58277811929829707174508485 10927089736843070095220341)
      ·
        refine ⟨1024414662829037821426907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10927089736843070095220341 1024414662829037821426907)
        ·
          refine ⟨1536621994243556732140361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024414662829037821426907 1536621994243556732140361)
          ·
            refine ⟨1152466495682667549105271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1536621994243556732140361 1152466495682667549105271)
            ·
              refine ⟨1728699743524001323657907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152466495682667549105271 1728699743524001323657907)
              ·
                refine ⟨2593049615286001985486861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1728699743524001323657907 2593049615286001985486861)
                ·
                  refine ⟨972393605732250744557573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2593049615286001985486861 972393605732250744557573)
                  ·
                    refine ⟨182323801074797014604545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 972393605732250744557573 182323801074797014604545)
                    ·
                      rfl

theorem cell23_1065223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_1065223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065223 prefixEnd_1065223 := by exact prefixLift 1065223
  have htrace : WordTrace (prefixWord ++ tailWord_1065223) baseStart_1065223 baseEnd_1065223 := by
    simpa [prefixWord, tailWord_1065223, baseEnd_1065223] using wordTrace_append hprefix tailTrace_1065223
  have hstable : (prefixWord ++ tailWord_1065223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065223).length < 2 ^ (prefixWord ++ tailWord_1065223).sum := by decide
  have hdescent : baseEnd_1065223 < baseStart_1065223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065249 : List Nat := [1, 2, 3, 2, 1, 1, 5, 2, 1, 5]
def baseStart_1065249 : Nat := 118140960795 + 1065249 * 2 ^ 59
def prefixEnd_1065249 : Nat := 4983230072969 + 3 ^ 40 * 1065249 * 2
def baseEnd_1065249 : Nat := 182328251240469314029505

theorem tailTrace_1065249 : CollatzResearch.WordTrace tailWord_1065249 prefixEnd_1065249 182328251240469314029505 := by
  unfold tailWord_1065249
  simp only [CollatzResearch.WordTrace]
  refine ⟨38852822917792277890118801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25901881945194851926745867 38852822917792277890118801)
  ·
    refine ⟨29139617188344208417589101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38852822917792277890118801 29139617188344208417589101)
    ·
      refine ⟨10927356445629078156595913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29139617188344208417589101 10927356445629078156595913)
      ·
        refine ⟨8195517334221808617446935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10927356445629078156595913 8195517334221808617446935)
        ·
          refine ⟨12293276001332712926170403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8195517334221808617446935 12293276001332712926170403)
          ·
            refine ⟨18439914001999069389255605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12293276001332712926170403 18439914001999069389255605)
            ·
              refine ⟨1728741937687412755242713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18439914001999069389255605 1728741937687412755242713)
              ·
                refine ⟨1296556453265559566432035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1728741937687412755242713 1296556453265559566432035)
                ·
                  refine ⟨1944834679898339349648053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296556453265559566432035 1944834679898339349648053)
                  ·
                    refine ⟨182328251240469314029505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1944834679898339349648053 182328251240469314029505)
                    ·
                      rfl

theorem cell23_1065249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_1065249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065249 prefixEnd_1065249 := by exact prefixLift 1065249
  have htrace : WordTrace (prefixWord ++ tailWord_1065249) baseStart_1065249 baseEnd_1065249 := by
    simpa [prefixWord, tailWord_1065249, baseEnd_1065249] using wordTrace_append hprefix tailTrace_1065249
  have hstable : (prefixWord ++ tailWord_1065249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065249).length < 2 ^ (prefixWord ++ tailWord_1065249).sum := by decide
  have hdescent : baseEnd_1065249 < baseStart_1065249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065320 : List Nat := [2, 1, 4, 2, 2, 1, 1, 5, 1, 2, 2]
def baseStart_1065320 : Nat := 118140960795 + 1065320 * 2 ^ 59
def prefixEnd_1065320 : Nat := 4983230072969 + 3 ^ 40 * 1065320 * 2
def baseEnd_1065320 : Nat := 547021210847877164300689

theorem tailTrace_1065320 : CollatzResearch.WordTrace tailWord_1065320 prefixEnd_1065320 547021210847877164300689 := by
  unfold tailWord_1065320
  simp only [CollatzResearch.WordTrace]
  refine ⟨19427706250267528507976707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25903608333690038010635609 19427706250267528507976707)
  ·
    refine ⟨29141559375401292761965061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19427706250267528507976707 29141559375401292761965061)
    ·
      refine ⟨5464042382887742392868449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29141559375401292761965061 5464042382887742392868449)
      ·
        refine ⟨4098031787165806794651337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5464042382887742392868449 4098031787165806794651337)
        ·
          refine ⟨3073523840374355095988503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4098031787165806794651337 3073523840374355095988503)
          ·
            refine ⟨4610285760561532643982755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3073523840374355095988503 4610285760561532643982755)
            ·
              refine ⟨6915428640842298965974133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4610285760561532643982755 6915428640842298965974133)
              ·
                refine ⟨648321435078965528060075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6915428640842298965974133 648321435078965528060075)
                ·
                  refine ⟨972482152618448292090113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 648321435078965528060075 972482152618448292090113)
                  ·
                    refine ⟨729361614463836219067585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 972482152618448292090113 729361614463836219067585)
                    ·
                      refine ⟨547021210847877164300689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 729361614463836219067585 547021210847877164300689)
                      ·
                        rfl

theorem cell23_1065320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_1065320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065320 prefixEnd_1065320 := by exact prefixLift 1065320
  have htrace : WordTrace (prefixWord ++ tailWord_1065320) baseStart_1065320 baseEnd_1065320 := by
    simpa [prefixWord, tailWord_1065320, baseEnd_1065320] using wordTrace_append hprefix tailTrace_1065320
  have hstable : (prefixWord ++ tailWord_1065320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065320).length < 2 ^ (prefixWord ++ tailWord_1065320).sum := by decide
  have hdescent : baseEnd_1065320 < baseStart_1065320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065379 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 5]
def baseStart_1065379 : Nat := 118140960795 + 1065379 * 2 ^ 59
def prefixEnd_1065379 : Nat := 4983230072969 + 3 ^ 40 * 1065379 * 2
def baseEnd_1065379 : Nat := 547051506206492433462917

theorem tailTrace_1065379 : CollatzResearch.WordTrace tailWord_1065379 prefixEnd_1065379 547051506206492433462917 := by
  unfold tailWord_1065379
  simp only [CollatzResearch.WordTrace]
  refine ⟨38857564407321310092351191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25905042938214206728234127 38857564407321310092351191)
  ·
    refine ⟨58286346610981965138526787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38857564407321310092351191 58286346610981965138526787)
    ·
      refine ⟨87429519916472947707790181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58286346610981965138526787 87429519916472947707790181)
      ·
        refine ⟨16393034984338677695210659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87429519916472947707790181 16393034984338677695210659)
        ·
          refine ⟨24589552476508016542815989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16393034984338677695210659 24589552476508016542815989)
          ·
            refine ⟨2305270544672626550888999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24589552476508016542815989 2305270544672626550888999)
            ·
              refine ⟨3457905817008939826333499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2305270544672626550888999 3457905817008939826333499)
              ·
                refine ⟨5186858725513409739500249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3457905817008939826333499 5186858725513409739500249)
                ·
                  refine ⟨3890144044135057304625187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5186858725513409739500249 3890144044135057304625187)
                  ·
                    refine ⟨5835216066202585956937781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3890144044135057304625187 5835216066202585956937781)
                    ·
                      refine ⟨547051506206492433462917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5835216066202585956937781 547051506206492433462917)
                      ·
                        rfl

theorem cell23_1065379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_1065379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065379 prefixEnd_1065379 := by exact prefixLift 1065379
  have htrace : WordTrace (prefixWord ++ tailWord_1065379) baseStart_1065379 baseEnd_1065379 := by
    simpa [prefixWord, tailWord_1065379, baseEnd_1065379] using wordTrace_append hprefix tailTrace_1065379
  have hstable : (prefixWord ++ tailWord_1065379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065379).length < 2 ^ (prefixWord ++ tailWord_1065379).sum := by decide
  have hdescent : baseEnd_1065379 < baseStart_1065379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065393 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 4, 2, 2]
def baseStart_1065393 : Nat := 118140960795 + 1065393 * 2 ^ 59
def prefixEnd_1065393 : Nat := 4983230072969 + 3 ^ 40 * 1065393 * 2
def baseEnd_1065393 : Nat := 547058694935655378687853

theorem tailTrace_1065393 : CollatzResearch.WordTrace tailWord_1065393 prefixEnd_1065393 547058694935655378687853 := by
  unfold tailWord_1065393
  simp only [CollatzResearch.WordTrace]
  refine ⟨38858075029270590483360833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25905383352847060322240555 38858075029270590483360833)
  ·
    refine ⟨29143556271952942862520625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38858075029270590483360833 29143556271952942862520625)
    ·
      refine ⟨21857667203964707146890469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29143556271952942862520625 21857667203964707146890469)
      ·
        refine ⟨4098312600743382590041963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21857667203964707146890469 4098312600743382590041963)
        ·
          refine ⟨6147468901115073885062945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4098312600743382590041963 6147468901115073885062945)
          ·
            refine ⟨4610601675836305413797209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6147468901115073885062945 4610601675836305413797209)
            ·
              refine ⟨3457951256877229060347907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4610601675836305413797209 3457951256877229060347907)
              ·
                refine ⟨5186926885315843590521861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3457951256877229060347907 5186926885315843590521861)
                ·
                  refine ⟨972548790996720673222849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5186926885315843590521861 972548790996720673222849)
                  ·
                    refine ⟨729411593247540504917137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 972548790996720673222849 729411593247540504917137)
                    ·
                      refine ⟨547058694935655378687853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 729411593247540504917137 547058694935655378687853)
                      ·
                        rfl

theorem cell23_1065393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_1065393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065393 prefixEnd_1065393 := by exact prefixLift 1065393
  have htrace : WordTrace (prefixWord ++ tailWord_1065393) baseStart_1065393 baseEnd_1065393 := by
    simpa [prefixWord, tailWord_1065393, baseEnd_1065393] using wordTrace_append hprefix tailTrace_1065393
  have hstable : (prefixWord ++ tailWord_1065393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065393).length < 2 ^ (prefixWord ++ tailWord_1065393).sum := by decide
  have hdescent : baseEnd_1065393 < baseStart_1065393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065399 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 7]
def baseStart_1065399 : Nat := 118140960795 + 1065399 * 2 ^ 59
def prefixEnd_1065399 : Nat := 4983230072969 + 3 ^ 40 * 1065399 * 2
def baseEnd_1065399 : Nat := 60784641757731372801425

theorem tailTrace_1065399 : CollatzResearch.WordTrace tailWord_1065399 prefixEnd_1065399 60784641757731372801425 := by
  unfold tailWord_1065399
  simp only [CollatzResearch.WordTrace]
  refine ⟨38858293867248853508079251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25905529244832569005386167 38858293867248853508079251)
  ·
    refine ⟨58287440800873280262118877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38858293867248853508079251 58287440800873280262118877)
    ·
      refine ⟨21857790300327480098294579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58287440800873280262118877 21857790300327480098294579)
      ·
        refine ⟨32786685450491220147441869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21857790300327480098294579 32786685450491220147441869)
        ·
          refine ⟨12295007043934207555290701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32786685450491220147441869 12295007043934207555290701)
          ·
            refine ⟨4610627641475327833234013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12295007043934207555290701 4610627641475327833234013)
            ·
              refine ⟨1728985365553247937462755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4610627641475327833234013 1728985365553247937462755)
              ·
                refine ⟨2593478048329871906194133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1728985365553247937462755 2593478048329871906194133)
                ·
                  refine ⟨60784641757731372801425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2593478048329871906194133 60784641757731372801425)
                  ·
                    rfl

theorem cell23_1065399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 7].length) (baseStart_1065399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065399 prefixEnd_1065399 := by exact prefixLift 1065399
  have htrace : WordTrace (prefixWord ++ tailWord_1065399) baseStart_1065399 baseEnd_1065399 := by
    simpa [prefixWord, tailWord_1065399, baseEnd_1065399] using wordTrace_append hprefix tailTrace_1065399
  have hstable : (prefixWord ++ tailWord_1065399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065399).length < 2 ^ (prefixWord ++ tailWord_1065399).sum := by decide
  have hdescent : baseEnd_1065399 < baseStart_1065399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065439 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 5]
def baseStart_1065439 : Nat := 118140960795 + 1065439 * 2 ^ 59
def prefixEnd_1065439 : Nat := 4983230072969 + 3 ^ 40 * 1065439 * 2
def baseEnd_1065439 : Nat := 547082315045762198712641

theorem tailTrace_1065439 : CollatzResearch.WordTrace tailWord_1065439 prefixEnd_1065439 547082315045762198712641 := by
  unfold tailWord_1065439
  simp only [CollatzResearch.WordTrace]
  refine ⟨38859752787103940339535371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25906501858069293559690247 38859752787103940339535371)
  ·
    refine ⟨58289629180655910509303057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38859752787103940339535371 58289629180655910509303057)
    ·
      refine ⟨43717221885491932881977293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58289629180655910509303057 43717221885491932881977293)
      ·
        refine ⟨16393958207059474830741485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43717221885491932881977293 16393958207059474830741485)
        ·
          refine ⟨6147734327647303061528057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16393958207059474830741485 6147734327647303061528057)
          ·
            refine ⟨4610800745735477296146043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6147734327647303061528057 4610800745735477296146043)
            ·
              refine ⟨6916201118603215944219065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4610800745735477296146043 6916201118603215944219065)
              ·
                refine ⟨5187150838952411958164299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6916201118603215944219065 5187150838952411958164299)
                ·
                  refine ⟨7780726258428617937246449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5187150838952411958164299 7780726258428617937246449)
                  ·
                    refine ⟨5835544693821463452934837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7780726258428617937246449 5835544693821463452934837)
                    ·
                      refine ⟨547082315045762198712641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5835544693821463452934837 547082315045762198712641)
                      ·
                        rfl

theorem cell23_1065439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_1065439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065439 prefixEnd_1065439 := by exact prefixLift 1065439
  have htrace : WordTrace (prefixWord ++ tailWord_1065439) baseStart_1065439 baseEnd_1065439 := by
    simpa [prefixWord, tailWord_1065439, baseEnd_1065439] using wordTrace_append hprefix tailTrace_1065439
  have hstable : (prefixWord ++ tailWord_1065439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065439).length < 2 ^ (prefixWord ++ tailWord_1065439).sum := by decide
  have hdescent : baseEnd_1065439 < baseStart_1065439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065449 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 4, 1, 4]
def baseStart_1065449 : Nat := 118140960795 + 1065449 * 2 ^ 59
def prefixEnd_1065449 : Nat := 4983230072969 + 3 ^ 40 * 1065449 * 2
def baseEnd_1065449 : Nat := 547087449852307159587595

theorem tailTrace_1065449 : CollatzResearch.WordTrace tailWord_1065449 prefixEnd_1065449 547087449852307159587595 := by
  unfold tailWord_1065449
  simp only [CollatzResearch.WordTrace]
  refine ⟨38860117517067712047399401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25906745011378474698266267 38860117517067712047399401)
  ·
    refine ⟨29145088137800784035549551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38860117517067712047399401 29145088137800784035549551)
    ·
      refine ⟨43717632206701176053324327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29145088137800784035549551 43717632206701176053324327)
      ·
        refine ⟨65576448310051764079986491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43717632206701176053324327 65576448310051764079986491)
        ·
          refine ⟨98364672465077646119979737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65576448310051764079986491 98364672465077646119979737)
          ·
            refine ⟨73773504348808234589984803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98364672465077646119979737 73773504348808234589984803)
            ·
              refine ⟨110660256523212351884977205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73773504348808234589984803 110660256523212351884977205)
              ·
                refine ⟨10374399049051157989216613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110660256523212351884977205 10374399049051157989216613)
                ·
                  refine ⟨1945199821697092122978115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10374399049051157989216613 1945199821697092122978115)
                  ·
                    refine ⟨2917799732545638184467173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1945199821697092122978115 2917799732545638184467173)
                    ·
                      refine ⟨547087449852307159587595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2917799732545638184467173 547087449852307159587595)
                      ·
                        rfl

theorem cell23_1065449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_1065449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065449 prefixEnd_1065449 := by exact prefixLift 1065449
  have htrace : WordTrace (prefixWord ++ tailWord_1065449) baseStart_1065449 baseEnd_1065449 := by
    simpa [prefixWord, tailWord_1065449, baseEnd_1065449] using wordTrace_append hprefix tailTrace_1065449
  have hstable : (prefixWord ++ tailWord_1065449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065449).length < 2 ^ (prefixWord ++ tailWord_1065449).sum := by decide
  have hdescent : baseEnd_1065449 < baseStart_1065449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065450 : List Nat := [3, 1, 3, 1, 3, 3, 2, 2, 5]
def baseStart_1065450 : Nat := 118140960795 + 1065450 * 2 ^ 59
def prefixEnd_1065450 : Nat := 4983230072969 + 3 ^ 40 * 1065450 * 2
def baseEnd_1065450 : Nat := 60787551481440183963899

theorem tailTrace_1065450 : CollatzResearch.WordTrace tailWord_1065450 prefixEnd_1065450 60787551481440183963899 := by
  unfold tailWord_1065450
  simp only [CollatzResearch.WordTrace]
  refine ⟨9715038497516022304546451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25906769326709392812123869 9715038497516022304546451)
  ·
    refine ⟨14572557746274033456819677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9715038497516022304546451 14572557746274033456819677)
    ·
      refine ⟨5464709154852762546307379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14572557746274033456819677 5464709154852762546307379)
      ·
        refine ⟨8197063732279143819461069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5464709154852762546307379 8197063732279143819461069)
        ·
          refine ⟨3073898899604678932297901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8197063732279143819461069 3073898899604678932297901)
          ·
            refine ⟨1152712087351754599611713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3073898899604678932297901 1152712087351754599611713)
            ·
              refine ⟨864534065513815949708785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1152712087351754599611713 864534065513815949708785)
              ·
                refine ⟨648400549135361962281589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 864534065513815949708785 648400549135361962281589)
                ·
                  refine ⟨60787551481440183963899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 648400549135361962281589 60787551481440183963899)
                  ·
                    rfl

theorem cell23_1065450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 5].length) (baseStart_1065450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065450 prefixEnd_1065450 := by exact prefixLift 1065450
  have htrace : WordTrace (prefixWord ++ tailWord_1065450) baseStart_1065450 baseEnd_1065450 := by
    simpa [prefixWord, tailWord_1065450, baseEnd_1065450] using wordTrace_append hprefix tailTrace_1065450
  have hstable : (prefixWord ++ tailWord_1065450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065450).length < 2 ^ (prefixWord ++ tailWord_1065450).sum := by decide
  have hdescent : baseEnd_1065450 < baseStart_1065450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065453 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_1065453 : Nat := 118140960795 + 1065453 * 2 ^ 59
def prefixEnd_1065453 : Nat := 4983230072969 + 3 ^ 40 * 1065453 * 2
def baseEnd_1065453 : Nat := 547089503774925143937577

theorem tailTrace_1065453 : CollatzResearch.WordTrace tailWord_1065453 prefixEnd_1065453 547089503774925143937577 := by
  unfold tailWord_1065453
  simp only [CollatzResearch.WordTrace]
  refine ⟨38860263409053220730545013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25906842272702147153696675 38860263409053220730545013)
  ·
    refine ⟨3643149694598739443488595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38860263409053220730545013 3643149694598739443488595)
    ·
      refine ⟨5464724541898109165232893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3643149694598739443488595 5464724541898109165232893)
      ·
        refine ⟨2049271703211790936962335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5464724541898109165232893 2049271703211790936962335)
        ·
          refine ⟨3073907554817686405443503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2049271703211790936962335 3073907554817686405443503)
          ·
            refine ⟨4610861332226529608165255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3073907554817686405443503 4610861332226529608165255)
            ·
              refine ⟨6916291998339794412247883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4610861332226529608165255 6916291998339794412247883)
              ·
                refine ⟨10374437997509691618371825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6916291998339794412247883 10374437997509691618371825)
                ·
                  refine ⟨7780828498132268713778869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10374437997509691618371825 7780828498132268713778869)
                  ·
                    refine ⟨729452671699900191916769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7780828498132268713778869 729452671699900191916769)
                    ·
                      refine ⟨547089503774925143937577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 729452671699900191916769 547089503774925143937577)
                      ·
                        rfl

theorem cell23_1065453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_1065453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065453 prefixEnd_1065453 := by exact prefixLift 1065453
  have htrace : WordTrace (prefixWord ++ tailWord_1065453) baseStart_1065453 baseEnd_1065453 := by
    simpa [prefixWord, tailWord_1065453, baseEnd_1065453] using wordTrace_append hprefix tailTrace_1065453
  have hstable : (prefixWord ++ tailWord_1065453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065453).length < 2 ^ (prefixWord ++ tailWord_1065453).sum := by decide
  have hdescent : baseEnd_1065453 < baseStart_1065453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065483 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 2, 1, 4]
def baseStart_1065483 : Nat := 118140960795 + 1065483 * 2 ^ 59
def prefixEnd_1065483 : Nat := 4983230072969 + 3 ^ 40 * 1065483 * 2
def baseEnd_1065483 : Nat := 547104908194560026562439

theorem tailTrace_1065483 : CollatzResearch.WordTrace tailWord_1065483 prefixEnd_1065483 547104908194560026562439 := by
  unfold tailWord_1065483
  simp only [CollatzResearch.WordTrace]
  refine ⟨38861357598944535854137103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25907571732629690569424735 38861357598944535854137103)
  ·
    refine ⟨58292036398416803781205655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38861357598944535854137103 58292036398416803781205655)
    ·
      refine ⟨87438054597625205671808483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58292036398416803781205655 87438054597625205671808483)
      ·
        refine ⟨131157081896437808507712725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87438054597625205671808483 131157081896437808507712725)
        ·
          refine ⟨3073994106947761136899517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 131157081896437808507712725 3073994106947761136899517)
          ·
            refine ⟨1152747790105410426337319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3073994106947761136899517 1152747790105410426337319)
            ·
              refine ⟨1729121685158115639505979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152747790105410426337319 1729121685158115639505979)
              ·
                refine ⟨2593682527737173459258969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1729121685158115639505979 2593682527737173459258969)
                ·
                  refine ⟨1945261895802880094444227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2593682527737173459258969 1945261895802880094444227)
                  ·
                    refine ⟨2917892843704320141666341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1945261895802880094444227 2917892843704320141666341)
                    ·
                      refine ⟨547104908194560026562439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2917892843704320141666341 547104908194560026562439)
                      ·
                        rfl

theorem cell23_1065483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 1, 4].length) (baseStart_1065483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065483 prefixEnd_1065483 := by exact prefixLift 1065483
  have htrace : WordTrace (prefixWord ++ tailWord_1065483) baseStart_1065483 baseEnd_1065483 := by
    simpa [prefixWord, tailWord_1065483, baseEnd_1065483] using wordTrace_append hprefix tailTrace_1065483
  have hstable : (prefixWord ++ tailWord_1065483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065483).length < 2 ^ (prefixWord ++ tailWord_1065483).sum := by decide
  have hdescent : baseEnd_1065483 < baseStart_1065483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065499 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 3]
def baseStart_1065499 : Nat := 118140960795 + 1065499 * 2 ^ 59
def prefixEnd_1065499 : Nat := 4983230072969 + 3 ^ 40 * 1065499 * 2
def baseEnd_1065499 : Nat := 547113123885031963962365

theorem tailTrace_1065499 : CollatzResearch.WordTrace tailWord_1065499 prefixEnd_1065499 547113123885031963962365 := by
  unfold tailWord_1065499
  simp only [CollatzResearch.WordTrace]
  refine ⟨38861941166886570586719551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25907960777924380391146367 38861941166886570586719551)
  ·
    refine ⟨58292911750329855880079327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38861941166886570586719551 58292911750329855880079327)
    ·
      refine ⟨87439367625494783820118991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58292911750329855880079327 87439367625494783820118991)
      ·
        refine ⟨131159051438242175730178487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87439367625494783820118991 131159051438242175730178487)
        ·
          refine ⟨196738577157363263595267731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131159051438242175730178487 196738577157363263595267731)
          ·
            refine ⟨295107865736044895392901597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196738577157363263595267731 295107865736044895392901597)
            ·
              refine ⟨110665449651016835772338099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 295107865736044895392901597 110665449651016835772338099)
              ·
                refine ⟨165998174476525253658507149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110665449651016835772338099 165998174476525253658507149)
                ·
                  refine ⟨62249315428696970121940181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165998174476525253658507149 62249315428696970121940181)
                  ·
                    refine ⟨1458968330360085237232973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 62249315428696970121940181 1458968330360085237232973)
                    ·
                      refine ⟨547113123885031963962365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1458968330360085237232973 547113123885031963962365)
                      ·
                        rfl

theorem cell23_1065499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 3].length) (baseStart_1065499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065499 prefixEnd_1065499 := by exact prefixLift 1065499
  have htrace : WordTrace (prefixWord ++ tailWord_1065499) baseStart_1065499 baseEnd_1065499 := by
    simpa [prefixWord, tailWord_1065499, baseEnd_1065499] using wordTrace_append hprefix tailTrace_1065499
  have hstable : (prefixWord ++ tailWord_1065499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065499).length < 2 ^ (prefixWord ++ tailWord_1065499).sum := by decide
  have hdescent : baseEnd_1065499 < baseStart_1065499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065509 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_1065509 : Nat := 118140960795 + 1065509 * 2 ^ 59
def prefixEnd_1065509 : Nat := 4983230072969 + 3 ^ 40 * 1065509 * 2
def baseEnd_1065509 : Nat := 547118258691576924837319

theorem tailTrace_1065509 : CollatzResearch.WordTrace tailWord_1065509 prefixEnd_1065509 547118258691576924837319 := by
  unfold tailWord_1065509
  simp only [CollatzResearch.WordTrace]
  refine ⟨38862305896850342294583581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25908203931233561529722387 38862305896850342294583581)
  ·
    refine ⟨14573364711318878360468843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38862305896850342294583581 14573364711318878360468843)
    ·
      refine ⟨21860047066978317540703265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14573364711318878360468843 21860047066978317540703265)
      ·
        refine ⟨16395035300233738155527449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21860047066978317540703265 16395035300233738155527449)
        ·
          refine ⟨12296276475175303616645587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16395035300233738155527449 12296276475175303616645587)
          ·
            refine ⟨18444414712762955424968381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12296276475175303616645587 18444414712762955424968381)
            ·
              refine ⟨6916655517286108284363143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18444414712762955424968381 6916655517286108284363143)
              ·
                refine ⟨10374983275929162426544715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6916655517286108284363143 10374983275929162426544715)
                ·
                  refine ⟨15562474913893743639817073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10374983275929162426544715 15562474913893743639817073)
                  ·
                    refine ⟨11671856185420307729862805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15562474913893743639817073 11671856185420307729862805)
                    ·
                      refine ⟨547118258691576924837319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11671856185420307729862805 547118258691576924837319)
                      ·
                        rfl

theorem cell23_1065509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_1065509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065509 prefixEnd_1065509 := by exact prefixLift 1065509
  have htrace : WordTrace (prefixWord ++ tailWord_1065509) baseStart_1065509 baseEnd_1065509 := by
    simpa [prefixWord, tailWord_1065509, baseEnd_1065509] using wordTrace_append hprefix tailTrace_1065509
  have hstable : (prefixWord ++ tailWord_1065509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065509).length < 2 ^ (prefixWord ++ tailWord_1065509).sum := by decide
  have hdescent : baseEnd_1065509 < baseStart_1065509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065536 : List Nat := [2, 1, 1, 2, 2, 2, 3, 4, 1, 5]
def baseStart_1065536 : Nat := 118140960795 + 1065536 * 2 ^ 59
def prefixEnd_1065536 : Nat := 4983230072969 + 3 ^ 40 * 1065536 * 2
def baseEnd_1065536 : Nat := 182377374223082773066565

theorem tailTrace_1065536 : CollatzResearch.WordTrace tailWord_1065536 prefixEnd_1065536 182377374223082773066565 := by
  unfold tailWord_1065536
  simp only [CollatzResearch.WordTrace]
  refine ⟨19431645333876262952908231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25908860445168350603877641 19431645333876262952908231)
  ·
    refine ⟨29147468000814394429362347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19431645333876262952908231 29147468000814394429362347)
    ·
      refine ⟨43721202001221591644043521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29147468000814394429362347 43721202001221591644043521)
      ·
        refine ⟨32790901500916193733032641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43721202001221591644043521 32790901500916193733032641)
        ·
          refine ⟨24593176125687145299774481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32790901500916193733032641 24593176125687145299774481)
          ·
            refine ⟨18444882094265358974830861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24593176125687145299774481 18444882094265358974830861)
            ·
              refine ⟨6916830785349509615561573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18444882094265358974830861 6916830785349509615561573)
              ·
                refine ⟨1296905772253033052917795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6916830785349509615561573 1296905772253033052917795)
                ·
                  refine ⟨1945358658379549579376693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1296905772253033052917795 1945358658379549579376693)
                  ·
                    refine ⟨182377374223082773066565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1945358658379549579376693 182377374223082773066565)
                    ·
                      rfl

theorem cell23_1065536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 1, 5].length) (baseStart_1065536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065536 prefixEnd_1065536 := by exact prefixLift 1065536
  have htrace : WordTrace (prefixWord ++ tailWord_1065536) baseStart_1065536 baseEnd_1065536 := by
    simpa [prefixWord, tailWord_1065536, baseEnd_1065536] using wordTrace_append hprefix tailTrace_1065536
  have hstable : (prefixWord ++ tailWord_1065536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065536).length < 2 ^ (prefixWord ++ tailWord_1065536).sum := by decide
  have hdescent : baseEnd_1065536 < baseStart_1065536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065539 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 4]
def baseStart_1065539 : Nat := 118140960795 + 1065539 * 2 ^ 59
def prefixEnd_1065539 : Nat := 4983230072969 + 3 ^ 40 * 1065539 * 2
def baseEnd_1065539 : Nat := 547133663111211807462181

theorem tailTrace_1065539 : CollatzResearch.WordTrace tailWord_1065539 prefixEnd_1065539 547133663111211807462181 := by
  unfold tailWord_1065539
  simp only [CollatzResearch.WordTrace]
  refine ⟨38863400086741657418175671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25908933391161104945450447 38863400086741657418175671)
  ·
    refine ⟨58295100130112486127263507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38863400086741657418175671 58295100130112486127263507)
    ·
      refine ⟨87442650195168729190895261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58295100130112486127263507 87442650195168729190895261)
      ·
        refine ⟨32790993823188273446585723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87442650195168729190895261 32790993823188273446585723)
        ·
          refine ⟨49186490734782410169878585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32790993823188273446585723 49186490734782410169878585)
          ·
            refine ⟨36889868051086807627408939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49186490734782410169878585 36889868051086807627408939)
            ·
              refine ⟨55334802076630211441113409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36889868051086807627408939 55334802076630211441113409)
              ·
                refine ⟨41501101557472658580835057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55334802076630211441113409 41501101557472658580835057)
                ·
                  refine ⟨31125826168104493935626293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41501101557472658580835057 31125826168104493935626293)
                  ·
                    refine ⟨2918046203259796306464965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31125826168104493935626293 2918046203259796306464965)
                    ·
                      refine ⟨547133663111211807462181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2918046203259796306464965 547133663111211807462181)
                      ·
                        rfl

theorem cell23_1065539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_1065539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065539 prefixEnd_1065539 := by exact prefixLift 1065539
  have htrace : WordTrace (prefixWord ++ tailWord_1065539) baseStart_1065539 baseEnd_1065539 := by
    simpa [prefixWord, tailWord_1065539, baseEnd_1065539] using wordTrace_append hprefix tailTrace_1065539
  have hstable : (prefixWord ++ tailWord_1065539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065539).length < 2 ^ (prefixWord ++ tailWord_1065539).sum := by decide
  have hdescent : baseEnd_1065539 < baseStart_1065539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065543 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 1, 5, 2]
def baseStart_1065543 : Nat := 118140960795 + 1065543 * 2 ^ 59
def prefixEnd_1065543 : Nat := 4983230072969 + 3 ^ 40 * 1065543 * 2
def baseEnd_1065543 : Nat := 547135717033829791812163

theorem tailTrace_1065543 : CollatzResearch.WordTrace tailWord_1065543 prefixEnd_1065543 547135717033829791812163 := by
  unfold tailWord_1065543
  simp only [CollatzResearch.WordTrace]
  refine ⟨38863545978727166101321283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25909030652484777400880855 38863545978727166101321283)
  ·
    refine ⟨58295318968090749151981925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38863545978727166101321283 58295318968090749151981925)
    ·
      refine ⟨10930372306517015465996611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58295318968090749151981925 10930372306517015465996611)
      ·
        refine ⟨16395558459775523198994917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10930372306517015465996611 16395558459775523198994917)
        ·
          refine ⟨3074167211207910599811547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16395558459775523198994917 3074167211207910599811547)
          ·
            refine ⟨4611250816811865899717321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3074167211207910599811547 4611250816811865899717321)
            ·
              refine ⟨3458438112608899424787991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4611250816811865899717321 3458438112608899424787991)
              ·
                refine ⟨5187657168913349137181987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3458438112608899424787991 5187657168913349137181987)
                ·
                  refine ⟨7781485753370023705772981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5187657168913349137181987 7781485753370023705772981)
                  ·
                    refine ⟨729514289378439722416217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7781485753370023705772981 729514289378439722416217)
                    ·
                      refine ⟨547135717033829791812163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 729514289378439722416217 547135717033829791812163)
                      ·
                        rfl

theorem cell23_1065543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_1065543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065543 prefixEnd_1065543 := by exact prefixLift 1065543
  have htrace : WordTrace (prefixWord ++ tailWord_1065543) baseStart_1065543 baseEnd_1065543 := by
    simpa [prefixWord, tailWord_1065543, baseEnd_1065543] using wordTrace_append hprefix tailTrace_1065543
  have hstable : (prefixWord ++ tailWord_1065543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065543).length < 2 ^ (prefixWord ++ tailWord_1065543).sum := by decide
  have hdescent : baseEnd_1065543 < baseStart_1065543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065590 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_1065590 : Nat := 118140960795 + 1065590 * 2 ^ 59
def prefixEnd_1065590 : Nat := 4983230072969 + 3 ^ 40 * 1065590 * 2
def baseEnd_1065590 : Nat := 547159850624591107924447

theorem tailTrace_1065590 : CollatzResearch.WordTrace tailWord_1065590 prefixEnd_1065590 547159850624591107924447 := by
  unfold tailWord_1065590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2429078763097305820517639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25910173473037928752188149 2429078763097305820517639)
  ·
    refine ⟨3643618144645958730776459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2429078763097305820517639 3643618144645958730776459)
    ·
      refine ⟨5465427216968938096164689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3643618144645958730776459 5465427216968938096164689)
      ·
        refine ⟨4099070412726703572123517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5465427216968938096164689 4099070412726703572123517)
        ·
          refine ⟨1537151404772513839546319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4099070412726703572123517 1537151404772513839546319)
          ·
            refine ⟨2305727107158770759319479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537151404772513839546319 2305727107158770759319479)
            ·
              refine ⟨3458590660738156138979219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2305727107158770759319479 3458590660738156138979219)
              ·
                refine ⟨5187885991107234208468829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3458590660738156138979219 5187885991107234208468829)
                ·
                  refine ⟨1945457246665212828175811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5187885991107234208468829 1945457246665212828175811)
                  ·
                    refine ⟨2918185869997819242263717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1945457246665212828175811 2918185869997819242263717)
                    ·
                      refine ⟨547159850624591107924447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2918185869997819242263717 547159850624591107924447)
                      ·
                        rfl

theorem cell23_1065590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_1065590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065590 prefixEnd_1065590 := by exact prefixLift 1065590
  have htrace : WordTrace (prefixWord ++ tailWord_1065590) baseStart_1065590 baseEnd_1065590 := by
    simpa [prefixWord, tailWord_1065590, baseEnd_1065590] using wordTrace_append hprefix tailTrace_1065590
  have hstable : (prefixWord ++ tailWord_1065590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065590).length < 2 ^ (prefixWord ++ tailWord_1065590).sum := by decide
  have hdescent : baseEnd_1065590 < baseStart_1065590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1065593 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 3, 2, 3]
def baseStart_1065593 : Nat := 118140960795 + 1065593 * 2 ^ 59
def prefixEnd_1065593 : Nat := 4983230072969 + 3 ^ 40 * 1065593 * 2
def baseEnd_1065593 : Nat := 547161391066554596186933

theorem tailTrace_1065593 : CollatzResearch.WordTrace tailWord_1065593 prefixEnd_1065593 547161391066554596186933 := by
  unfold tailWord_1065593
  simp only [CollatzResearch.WordTrace]
  refine ⟨38865369628546024640641433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25910246419030683093760955 38865369628546024640641433)
  ·
    refine ⟨29149027221409518480481075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38865369628546024640641433 29149027221409518480481075)
    ·
      refine ⟨43723540832114277720721613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29149027221409518480481075 43723540832114277720721613)
      ·
        refine ⟨16396327812042854145270605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43723540832114277720721613 16396327812042854145270605)
        ·
          refine ⟨6148622929516070304476477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16396327812042854145270605 6148622929516070304476477)
          ·
            refine ⟨2305733598568526364178679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6148622929516070304476477 2305733598568526364178679)
            ·
              refine ⟨3458600397852789546268019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2305733598568526364178679 3458600397852789546268019)
              ·
                refine ⟨5187900596779184319402029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3458600397852789546268019 5187900596779184319402029)
                ·
                  refine ⟨1945462723792194119775761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5187900596779184319402029 1945462723792194119775761)
                  ·
                    refine ⟨1459097042844145589831821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1945462723792194119775761 1459097042844145589831821)
                    ·
                      refine ⟨547161391066554596186933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1459097042844145589831821 547161391066554596186933)
                      ·
                        rfl

theorem cell23_1065593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_1065593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1065593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1065593 prefixEnd_1065593 := by exact prefixLift 1065593
  have htrace : WordTrace (prefixWord ++ tailWord_1065593) baseStart_1065593 baseEnd_1065593 := by
    simpa [prefixWord, tailWord_1065593, baseEnd_1065593] using wordTrace_append hprefix tailTrace_1065593
  have hstable : (prefixWord ++ tailWord_1065593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1065593).length < 2 ^ (prefixWord ++ tailWord_1065593).sum := by decide
  have hdescent : baseEnd_1065593 < baseStart_1065593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1065593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
